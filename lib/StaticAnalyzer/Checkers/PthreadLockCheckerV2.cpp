//===--- PthreadLockChecker.cpp - Check for locking problems ---*- C++ -*--===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This defines PthreadLockChecker, a simple lock -> unlock checker.
// Also handles XNU locks, which behave similarly enough to share code.
//
//===----------------------------------------------------------------------===//

#include "ClangSACheckers.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramStateTrait.h"

#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "llvm/ADT/StringMap.h"

using namespace clang;
using namespace ento;
using namespace llvm;
using namespace ast_matchers;
using namespace internal;

namespace {

struct LockState {
  enum Kind {
    Destroyed,
    Locked,
    Unlocked,
    UntouchedAndPossiblyDestroyed,
    UnlockedAndPossiblyDestroyed
  } K;

private:
  LockState(Kind K) : K(K) {}

public:
  static LockState getLocked() { return LockState(Locked); }
  static LockState getUnlocked() { return LockState(Unlocked); }
  static LockState getDestroyed() { return LockState(Destroyed); }
  static LockState getUntouchedAndPossiblyDestroyed() {
    return LockState(UntouchedAndPossiblyDestroyed);
  }
  static LockState getUnlockedAndPossiblyDestroyed() {
    return LockState(UnlockedAndPossiblyDestroyed);
  }

  bool operator==(const LockState &X) const { return K == X.K; }

  bool isLocked() const { return K == Locked; }
  bool isUnlocked() const { return K == Unlocked; }
  bool isDestroyed() const { return K == Destroyed; }
  bool isUntouchedAndPossiblyDestroyed() const {
    return K == UntouchedAndPossiblyDestroyed;
  }
  bool isUnlockedAndPossiblyDestroyed() const {
    return K == UnlockedAndPossiblyDestroyed;
  }

  void Profile(llvm::FoldingSetNodeID &ID) const { ID.AddInteger(K); }
};

using namespace ast_type_traits;

class ASTGraphNode {
  enum NodeKindId { NKI_ASTType, NKI_ExplodedNode, NKI_SVal };

  AlignedCharArrayUnion<const ExplodedNode *, SVal, DynTypedNode> Storage;

  template <typename T> T &castUnsafe() {
    assert(is<T>());
    return *reinterpret_cast<T *>(Storage.buffer);
  }
  template <typename T> void assignStorage(T Value) { castUnsafe<T>() = Value; }

  NodeKindId Id;

public:
  ASTGraphNode(const ExplodedNode *N) : Id(NKI_ExplodedNode) {
    assignStorage(N);
  }
  ASTGraphNode(SVal SV) : Id(NKI_SVal) { assignStorage(SV); }
  ASTGraphNode(DynTypedNode N) : Id(NKI_ASTType) { assignStorage(N); }

  template <typename T> bool is() const;
};

template <> bool ASTGraphNode::is<SVal>() const { return Id == NKI_SVal; }
template <> bool ASTGraphNode::is<const ExplodedNode *>() const {
  return Id == NKI_ExplodedNode;
}
template <> bool ASTGraphNode::is<DynTypedNode>() const {
  return Id == NKI_ASTType;
}
template <typename T> bool ASTGraphNode::is() const { return false; }

class GraphMatchFinder;
class GraphBoundNodeMap;
class GraphBoundNodesTreeBuilder {};
/*
class DynGraphNodeMatcherInterface {
  virtual ~GraphNodeMatcherInterface() = default;
  virtual bool dynMatches(const ASTGraphNode &Node, GraphMatchFinder *Finder,
                          GraphBoundNodesTreeBuilder *Builder) = 0;
};

template <typename NodeTy>
class GraphNodeMatcherInterface<NodeTy> : public DynGraphNodeMatcherInterface {
  virtual bool matches(const NodeTy &Node, GraphMatchFinder *Finder,
                       GraphBoundNodesTreeBuilder *Builder) = 0;
  virtual bool dynMatches(const ASTGraphNode &Node, GraphMatchFinder *Finder,
                          GraphBoundNodesTreeBuilder *Builder) {
    return matches(Node.castUnsafe<NodeTy>(), Finder, Builder);
  }
};
*/


class GraphBoundNodeMap : public StringMap<ASTGraphNode> {
public:
  using BoundRecordType = StringMap<ASTGraphNode>;
  using iterator = BoundRecordType::iterator;
  using const_iterator = BoundRecordType::const_iterator;
  /*
    iterator begin() { return Bounds.begin(); }
    iterator end() { return Bounds.end(); }
    const_iterator begin() const { return Bounds.begin(); }
    const_iterator end() const { return Bounds.end(); }
  */
  GraphBoundNodeMap advance(const ExplodedNode *N) { return *this; } // FIXME

private:
  // FoldingSet<ASTGraphNode> Allocator;
  DenseMap<const ExplodedNode *, BoundRecordType> Bounds;
};

/*
/// \brief Matcher that works on a \c DynTypedNode.
///
/// It is constructed from a \c Matcher<T> object and redirects most calls to
/// underlying matcher.
/// It checks whether the \c DynTypedNode is convertible into the type of the
/// underlying matcher and then do the actual match on the actual node, or
/// return false if it is not convertible.
class GraphDynTypedMatcher {
public:
  /// \brief Takes ownership of the provided implementation pointer.
  template <typename T>
  GraphDynTypedMatcher(GraphNodeMatcherInterface<T> *Implementation)
      : SupportedKind(ASTGraphNode::NodeKindId::getFromNodeKind<T>()),
        RestrictKind(SupportedKind), Implementation(Implementation) {}

  /// \brief Construct from a variadic function.
  enum VariadicOperator {
    /// \brief Matches nodes for which all provided matchers match.
    VO_AllOf,

    /// \brief Matches nodes for which at least one of the provided matchers
    /// matches.
    VO_AnyOf,

    /// \brief Matches nodes for which at least one of the provided matchers
    /// matches, but doesn't stop at the first match.
    VO_EachOf,

    /// \brief Matches nodes that do not match the provided matcher.
    ///
    /// Uses the variadic matcher interface, but fails if
    /// InnerMatchers.size() != 1.
    VO_UnaryNot
  };

  static DynTypedMatcher
  constructVariadic(VariadicOperator Op,
                    ast_type_traits::ASTNodeKind SupportedKind,
                    std::vector<DynTypedMatcher> InnerMatchers);

  /// \brief Get a "true" matcher for \p NodeKind.
  ///
  /// It only checks that the node is of the right kind.
  static DynTypedMatcher trueMatcher(ast_type_traits::ASTNodeKind NodeKind);

  void setAllowBind(bool AB) { AllowBind = AB; }

  /// \brief Check whether this matcher could ever match a node of kind \p Kind.
  /// \return \c false if this matcher will never match such a node. Otherwise,
  /// return \c true.
  bool canMatchNodesOfKind(ast_type_traits::ASTNodeKind Kind) const;

  /// \brief Return a matcher that points to the same implementation, but
  ///   restricts the node types for \p Kind.
  DynTypedMatcher dynCastTo(const ast_type_traits::ASTNodeKind Kind) const;

  /// \brief Returns true if the matcher matches the given \c DynNode.
  bool matches(const ast_type_traits::DynTypedNode &DynNode,
               ASTMatchFinder *Finder, BoundNodesTreeBuilder *Builder) const;

  /// \brief Same as matches(), but skips the kind check.
  ///
  /// It is faster, but the caller must ensure the node is valid for the
  /// kind of this matcher.
  bool matchesNoKindCheck(const ast_type_traits::DynTypedNode &DynNode,
                          ASTMatchFinder *Finder,
                          BoundNodesTreeBuilder *Builder) const;

  /// \brief Bind the specified \p ID to the matcher.
  /// \return A new matcher with the \p ID bound to it if this matcher supports
  ///   binding. Otherwise, returns an empty \c Optional<>.
  llvm::Optional<DynTypedMatcher> tryBind(StringRef ID) const;

  /// \brief Returns a unique \p ID for the matcher.
  ///
  /// Casting a Matcher<T> to Matcher<U> creates a matcher that has the
  /// same \c Implementation pointer, but different \c RestrictKind. We need to
  /// include both in the ID to make it unique.
  ///
  /// \c MatcherIDType supports operator< and provides strict weak ordering.
  using MatcherIDType = std::pair<ast_type_traits::ASTNodeKind, uint64_t>;
  MatcherIDType getID() const {
    /// FIXME: Document the requirements this imposes on matcher
    /// implementations (no new() implementation_ during a Matches()).
    return std::make_pair(RestrictKind,
                          reinterpret_cast<uint64_t>(Implementation.get()));
  }

  /// \brief Returns the type this matcher works on.
  ///
  /// \c matches() will always return false unless the node passed is of this
  /// or a derived type.
  ast_type_traits::ASTNodeKind getSupportedKind() const {
    return SupportedKind;
  }

  /// \brief Returns \c true if the passed \c DynTypedMatcher can be converted
  ///   to a \c Matcher<T>.
  ///
  /// This method verifies that the underlying matcher in \c Other can process
  /// nodes of types T.
  template <typename T> bool canConvertTo() const {
    return canConvertTo(ast_type_traits::ASTNodeKind::getFromNodeKind<T>());
  }
  bool canConvertTo(ast_type_traits::ASTNodeKind To) const;

  /// \brief Construct a \c Matcher<T> interface around the dynamic matcher.
  ///
  /// This method asserts that \c canConvertTo() is \c true. Callers
  /// should call \c canConvertTo() first to make sure that \c this is
  /// compatible with T.
  template <typename T> Matcher<T> convertTo() const {
    assert(canConvertTo<T>());
    return unconditionalConvertTo<T>();
  }

  /// \brief Same as \c convertTo(), but does not check that the underlying
  ///   matcher can handle a value of T.
  ///
  /// If it is not compatible, then this matcher will never match anything.
  template <typename T> Matcher<T> unconditionalConvertTo() const;

private:
 DynTypedMatcher(ast_type_traits::ASTNodeKind SupportedKind,
                 ast_type_traits::ASTNodeKind RestrictKind,
                 IntrusiveRefCntPtr<DynMatcherInterface> Implementation)
     : SupportedKind(SupportedKind), RestrictKind(RestrictKind),
       Implementation(std::move(Implementation)) {}

  bool AllowBind = false;
  ast_type_traits::ASTNodeKind SupportedKind;

  /// \brief A potentially stricter node kind.
  ///
  /// It allows to perform implicit and dynamic cast of matchers without
  /// needing to change \c Implementation.
  ast_type_traits::ASTNodeKind RestrictKind;
  IntrusiveRefCntPtr<DynMatcherInterface> Implementation;
};

/// \brief Wrapper base class for a wrapping matcher.
///
/// This is just a container for a DynTypedMatcher that can be used as a base
/// class for another matcher.
template <typename T>
class WrapperMatcherInterface : public MatcherInterface<T> {
protected:
  explicit WrapperMatcherInterface(DynTypedMatcher &&InnerMatcher)
      : InnerMatcher(std::move(InnerMatcher)) {}

  const DynTypedMatcher InnerMatcher;
};

*/
class ExplodedNodeMatcher {
public:
  virtual bool matches(const ExplodedNode *Node, GraphMatchFinder *Finder,
                       GraphBoundNodesTreeBuilder *Builder) const = 0;
  virtual bool isNegative() const = 0;
  bool isPositive() const { return !isNegative(); }
  virtual ~ExplodedNodeMatcher() = default;

private:
};

class PathMatcher;

enum class MatchAction { Accept, Advance, RejectSingle, RejectForever, Pass };

class BindEntry {
  GraphBoundNodeMap BoundItems;
  unsigned StateID = 0;

public:
  BindEntry(PathMatcher *Matcher, const GraphBoundNodeMap &Initial)
      : BoundItems(Initial), Matcher(Matcher) {}

  unsigned getStateID() { return StateID; }

  void advance() { ++StateID; }

  void setStateID(unsigned StateID) { this->StateID = StateID; }

  BindEntry addBinding(StringRef Key, ASTGraphNode Binding) {
    BindEntry New = *this;
    New.BoundItems.insert(std::make_pair(Key, Binding));
    return New;
  }

  MatchAction matchNewNode(const ExplodedNode *N, GraphMatchFinder *Finder,
                           GraphBoundNodesTreeBuilder *Builder);

  PathMatcher *Matcher;
};

class PathMatcher {
  using MatcherVector = std::vector<ExplodedNodeMatcher *>;
  MatcherVector InnerMatchers;

  std::pair<size_t, bool>
  matchNotMatchers(size_t StartIndex, const ExplodedNode *Node,
                   GraphMatchFinder *Finder,
                   GraphBoundNodesTreeBuilder *Builder) {
    size_t I = StartIndex;
    for (; I < InnerMatchers.size(); ++I) {
      if (!InnerMatchers[I]->isNegative())
        return {I, true};
      if (!InnerMatchers[I]->matches(Node, Finder, Builder))
        return {I, false};
    }
    return {I, true};
  }

  size_t skipNotMatchers(size_t Index) const {
    while (Index < InnerMatchers.size() && InnerMatchers[Index]->isNegative())
      ++Index;
    assert(Index != InnerMatchers.size() &&
           "Cannot skip terminating not matchers!");
    return Index;
  }

  size_t matcherIndexByStateID(unsigned StateID) const {
    size_t Index = 0, NumMatchers = InnerMatchers.size();
    unsigned State = 0;
    for (; State < StateID && Index < NumMatchers; ++State) {
      Index = skipNotMatchers(Index);
      ++Index;
    }
    assert(State == StateID && Index < NumMatchers &&
           "Cannot find the matcher corresponding to State ID!");
    return Index;
  }

public:
  PathMatcher(MatcherVector &&InnerMatchers) : InnerMatchers(InnerMatchers) {}
  PathMatcher(std::initializer_list<ExplodedNodeMatcher *> Matchers)
      : InnerMatchers(Matchers) {}

  bool isSingle() const { return InnerMatchers.size() == 1; }

  MatchAction matches(const ExplodedNode *Node, GraphMatchFinder *Finder,
                      GraphBoundNodesTreeBuilder *Builder, unsigned StateID) {
    size_t Index = matcherIndexByStateID(StateID);
    bool NegMatch = false;
    std::tie(Index, NegMatch) = matchNotMatchers(Index, Node, Finder, Builder);
    if (!NegMatch) {
      if (StateID == 0)
        return MatchAction::RejectForever;
      else
        return MatchAction::RejectSingle;
    }

    bool IsNodeLast = Node->succ_empty();
    // Negative matchers are matching.
    if (Index == InnerMatchers.size()) {
      if (IsNodeLast)
        // If the node is last and no matchers remain, the path match
        // is accepted.
        return MatchAction::Accept;
      else
        // If the node is not last but all final negative matchers match,
        // continue matching until the final node is met.
        return MatchAction::Pass;
    }

    // Next matcher should exist and it should be positive.
    assert(InnerMatchers[Index]->isPositive());
    bool IsLastMatcher = Index == InnerMatchers.size() - 1;
    if (IsNodeLast && !IsLastMatcher)
      return MatchAction::RejectSingle;

    bool PositiveMatch = InnerMatchers[Index]->matches(Node, Finder, Builder);
    if (PositiveMatch) {
      if (IsLastMatcher)
        return MatchAction::Accept;
      else
        return MatchAction::Advance;
    } else {
      return MatchAction::Pass;
    }
    llvm_unreachable("The result should be already defined and returned!");
  }
};

class PSMatchesCallback : public MatchFinder::MatchCallback {
public:
  void run(const MatchFinder::MatchResult &Result) override {
    Nodes.push_back(Result.Nodes);
    HasMatches = true;
  }
  SmallVector<BoundNodes, 1> Nodes;
  bool HasMatches = false;
};

template <typename MatcherTy>
class StatementNodeMatcher : public ExplodedNodeMatcher {
  MatcherTy InnerMatcher;

public:
  StatementNodeMatcher(MatcherTy Inner) : InnerMatcher(Inner) {}
  virtual bool matches(const ExplodedNode *Node, GraphMatchFinder *Finder,
                       GraphBoundNodesTreeBuilder *Builder) const override;
  virtual bool isNegative() const override { return false; }
};

class NotMatcher : public ExplodedNodeMatcher {
  ExplodedNodeMatcher *InnerMatcher;

public:
  NotMatcher(ExplodedNodeMatcher *Inner) : InnerMatcher(Inner) {}
  virtual bool matches(const ExplodedNode *Node, GraphMatchFinder *Finder,
                       GraphBoundNodesTreeBuilder *Builder) const override {
    return !InnerMatcher->matches(Node, Finder, Builder);
  }
  virtual bool isNegative() const override { return true; }
};

template <typename MatcherTy>
ExplodedNodeMatcher *statementNode(MatcherTy Inner) {
  return new StatementNodeMatcher<MatcherTy>(Inner);
}

ExplodedNodeMatcher *unlessPS(ExplodedNodeMatcher *Inner) {
  return new NotMatcher(Inner);
}

class PathMatchCallback;

class GraphMatchFinder {
  ASTContext &ASTCtx;
  std::vector<BindEntry> Entries;
  GraphBoundNodesTreeBuilder Builder;
  GraphBoundNodeMap BoundMap;
  std::map<PathMatcher *, PathMatchCallback *> PathMatchers;

public:
  void match(const Decl *D);
  void match(ExplodedGraph &G, BugReporter &BR, ExprEngine &Eng);
  void addMatcher(const PathMatcher &Matcher, PathMatchCallback *Callback) {
    PathMatcher *Copy = new PathMatcher(Matcher);
    PathMatchers[Copy] = Callback;
  }

  void advance(const ExplodedNode *Pred, const ExplodedNode *Succ);
  ASTContext &getASTContext() { return ASTCtx; }
  GraphMatchFinder(ASTContext &ASTCtx) : ASTCtx(ASTCtx) {}
};

class PathMatchCallback {
public:
  virtual void run() = 0;
};

MatchAction BindEntry::matchNewNode(const ExplodedNode *N,
                                    GraphMatchFinder *Finder,
                                    GraphBoundNodesTreeBuilder *Builder) {
  return Matcher->matches(N, Finder, Builder, StateID);
}

template <typename MatcherTy>
bool StatementNodeMatcher<MatcherTy>::matches(
    const ExplodedNode *Node, GraphMatchFinder *Finder,
    GraphBoundNodesTreeBuilder *Builder) const {
  if (const Stmt *S = PathDiagnosticLocation::getStmt(Node)) {
    MatchFinder ASTFinder;
    PSMatchesCallback BindCollector;
    ASTFinder.addMatcher(InnerMatcher, &BindCollector);
    ASTFinder.match(*S, Finder->getASTContext());
    // FIXME: add bindings
    return BindCollector.HasMatches;
  }
  return false;
}

void GraphMatchFinder::advance(const ExplodedNode *Pred,
                               const ExplodedNode *Succ) {
  // Advance and remove unmatched items if needed.
  size_t I = 0;
  while (I < Entries.size()) {
    BindEntry &Entry = Entries[I];
    MatchAction MatchRes = Entry.matchNewNode(Succ, this, &Builder);
    switch (MatchRes) {
    case MatchAction::Advance:
      Entry.advance();
      ++I;
      break;
    case MatchAction::Accept: {
      auto *Callback = PathMatchers[Entry.Matcher];
      Callback->run();
    } // Fall-through
    case MatchAction::RejectSingle:
      Entries.erase(Entries.begin() + I);
      break;
    case MatchAction::Pass:
      ++I;
      // Do nothing.
      break;
    case MatchAction::RejectForever:
      llvm_unreachable("Existing entries should never reveive RejectForever!");
    default:
      llvm_unreachable("Non-existing match result!");
    }
  }

  // Check if a new item (StateID == 0) should be added.
  for (auto &MatchItem : PathMatchers) {
    PathMatcher *Matcher = MatchItem.first;
    MatchAction Res = Matcher->matches(Succ, this, &Builder, 0);
    if (Res == MatchAction::Advance) {
      GraphBoundNodeMap Bounds;
      if (Matcher->isSingle()) {
        auto *Callback = PathMatchers[Matcher];
        Callback->run();
      } else {
        Entries.emplace_back(Matcher, Bounds);
      }
    }
  }
}

void GraphMatchFinder::match(ExplodedGraph &G, BugReporter &BR,
                             ExprEngine &Eng) {
  // Simple DFS on ExplodedGraph nodes.
  typedef const ExplodedNode *ENodeRef;
  typedef std::pair<ENodeRef, ENodeRef> VisitEntry;
  SmallVector<ENodeRef, 256> Stack;
  DenseSet<ENodeRef> Visited;
  for (ENodeRef Root : G.roots()) {
    advance(nullptr, Root);
    Stack.push_back(Root);
    Visited.insert(Root);
  }

  while (!Stack.empty()) {
    ENodeRef From = Stack.pop_back_val();
    for (ENodeRef Succ : From->successors()) {
      advance(From, Succ);
      if (Visited.insert(Succ).second) // Not visited before
        Stack.push_back(Succ);
    }
  }
}

/*
AST_MATCHER_P(FunctionDecl, isReachable,
              ast_matchers::internal::VariadicOperatorMatcherFunc<
              2, std::numeric_limits<unsigned>::max()> InnerMatcher) {
  InnerMatcher.
}

auto LockMatcher =
    isReachable(
      stmt(
        callExpr(
          hasDeclaration(
            functionDecl(hasName("pthread_mutex_lock"))),
          hasArgValue(0,
                      value(isKnown(),
                            ).bind("mutex")))),
      unless(
        stmt(
          callExpr(
            hasDeclaration(
              functionDecl(hasName("pthread_mutex_unlock"))),
            hasArgValue(0, equalsBoundNode("mutex"))))),
      stmt(
        callExpr(
          hasDeclaration(
            functionDecl(hasName("pthread_mutex_lock"))),
          hasArgValue(0,equalsBoundNode("mutex")))));
*/
class PthreadLockCheckerV2 : public Checker<check::EndAnalysis> {
  mutable std::unique_ptr<BugType> BT_doublelock;
  mutable std::unique_ptr<BugType> BT_doubleunlock;
  mutable std::unique_ptr<BugType> BT_destroylock;
  mutable std::unique_ptr<BugType> BT_initlock;
  mutable std::unique_ptr<BugType> BT_lor;
  enum LockingSemantics { NotApplicable = 0, PthreadSemantics, XNUSemantics };

public:
  void checkEndAnalysis(ExplodedGraph &G, BugReporter &BR,
                        ExprEngine &Eng) const;
  /*  void printState(raw_ostream &Out, ProgramStateRef State, const char *NL,
                    const char *Sep) const override;

    void AcquireLock(CheckerContext &C, const CallExpr *CE, SVal lock,
                     bool isTryLock, enum LockingSemantics semantics) const;

    void ReleaseLock(CheckerContext &C, const CallExpr *CE, SVal lock) const;
    void DestroyLock(CheckerContext &C, const CallExpr *CE, SVal Lock,
                     enum LockingSemantics semantics) const;
    void InitLock(CheckerContext &C, const CallExpr *CE, SVal Lock) const;
    void reportUseDestroyedBug(CheckerContext &C, const CallExpr *CE) const;
    ProgramStateRef resolvePossiblyDestroyedMutex(ProgramStateRef state,
                                                  const MemRegion *lockR,
                                                  const SymbolRef *sym)
    const;*/
};
} // end anonymous namespace

template <typename CalleeTy>
class ProxyMatchCallback : public PathMatchCallback {
  CalleeTy Callee;

public:
  ProxyMatchCallback(CalleeTy Callee) : Callee(Callee) {}
  virtual void run() override { Callee(); }
};

template <typename CalleeTy>
ProxyMatchCallback<CalleeTy> createProxyCallback(CalleeTy Callee) {
  return ProxyMatchCallback<CalleeTy>(Callee);
}

void PthreadLockCheckerV2::checkEndAnalysis(ExplodedGraph &G, BugReporter &BR,
                                            ExprEngine &Eng) const {
  ExplodedNode *Root = *G.roots_begin();
  const Decl *D = Root->getStackFrame()->getDecl();
  std::string FuncName;
  if (const NamedDecl *FD = dyn_cast<NamedDecl>(D))
    FuncName = FD->getQualifiedNameAsString();

  GraphMatchFinder Finder(BR.getContext());
  auto Callback = createProxyCallback(
      [&FuncName]() -> void { llvm::errs() << FuncName << " matches!\n"; });
  Finder.addMatcher(
      {statementNode(callExpr(callee(functionDecl(hasName("::chroot"))))),
       unlessPS(
           statementNode(callExpr(callee(functionDecl(hasName("::chdir")))))),
       statementNode(
           callExpr(unless(callee(functionDecl(hasName("::chdir"))))))},
      &Callback);
  Finder.match(G, BR, Eng);
}

void ento::registerPthreadLockCheckerV2(CheckerManager &Mgr) {
  Mgr.registerChecker<PthreadLockCheckerV2>();
}
