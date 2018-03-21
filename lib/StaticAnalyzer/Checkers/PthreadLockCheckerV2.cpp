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
#include "clang/ASTMatchers/ASTGraphTypeTraits.h"
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

////////////////////////////////////////////////////////////////////////////////

using namespace ento::ast_graph_type_traits;

class GraphMatchFinder;
class GraphBoundNodeMap;
class GraphBoundNodesTreeBuilder {};

class GraphBoundNodeMap : public StringMap<DynTypedNode> {
public:
  using BoundRecordType = StringMap<DynTypedNode>;
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

typedef size_t MatcherStateID;
const MatcherStateID StateInvalid = std::numeric_limits<MatcherStateID>::max();

enum class MatchAction { Accept, Advance, RejectSingle, RejectForever, Pass };

struct MatchResult {
  MatchAction Action;
  MatcherStateID NewStateID;
};

/// \brief Generic interface for all matchers.
///
/// Used by the implementation of Matcher<T> and DynTypedMatcher.
/// In general, implement MatcherInterface<T> or SingleNodeMatcherInterface<T>
/// instead.
class DynPathMatcherInterface
    : public llvm::ThreadSafeRefCountedBase<DynPathMatcherInterface> {
public:
  virtual ~DynPathMatcherInterface() = default;

  /// \brief Returns true if \p DynNode can be matched.
  ///
  /// May bind \p DynNode to an ID via \p Builder, or recurse into
  /// the AST via \p Finder.
  virtual MatchResult
  dynMatches(const ento::ast_graph_type_traits::DynTypedNode &DynGraph,
             GraphMatchFinder *Finder, GraphBoundNodesTreeBuilder *Builder,
             MatcherStateID StateID) const = 0;
};

template <typename T>
class PathMatcherInterface : public DynPathMatcherInterface {
public:
  /// \brief Returns true if 'Node' can be matched.
  ///
  /// May bind 'Node' to an ID via 'Builder', or recurse into
  /// the AST via 'Finder'.
  virtual bool matches(const T &GraphNode, GraphMatchFinder *Finder,
                       GraphBoundNodesTreeBuilder *Builder,
                       MatcherStateID StateID) const = 0;

  MatchResult
  dynMatches(const ento::ast_graph_type_traits::DynTypedNode &GraphNode,
             GraphMatchFinder *Finder, GraphBoundNodesTreeBuilder *Builder,
             MatcherStateID StateID) const override {
    return matches(GraphNode.getUnchecked<T>(), Finder, Builder, StateID);
  }
};

// Can be specialized for CFG or ExplodedGraph.
template <typename> class PathMatcher;

/// \brief Matcher that works on a \c DynTypedNode.
///
/// It is constructed from a \c Matcher<T> object and redirects most calls to
/// underlying matcher.
/// It checks whether the \c DynTypedNode is convertible into the type of the
/// underlying matcher and then do the actual match on the actual node, or
/// return false if it is not convertible.
class DynTypedPathMatcher {
public:
  /// \brief Takes ownership of the provided implementation pointer.
  template <typename T>
  DynTypedPathMatcher(PathMatcherInterface<T> *Implementation)
      : Implementation(Implementation) {}

  DynTypedPathMatcher(
      IntrusiveRefCntPtr<DynPathMatcherInterface> Implementation)
      : Implementation(std::move(Implementation)) {}

  void setAllowBind(bool AB) { AllowBind = AB; }

  /// \brief Returns true if the matcher matches the given \c DynNode.
  MatchResult matches(const ento::ast_graph_type_traits::DynTypedNode &DynNode,
                      GraphMatchFinder *Finder,
                      GraphBoundNodesTreeBuilder *Builder,
                      MatcherStateID StateID) const;

  /// \brief Bind the specified \p ID to the matcher.
  /// \return A new matcher with the \p ID bound to it if this matcher supports
  ///   binding. Otherwise, returns an empty \c Optional<>.
  llvm::Optional<DynTypedMatcher> tryBind(StringRef ID) const;

private:
  bool AllowBind = false;
  IntrusiveRefCntPtr<DynPathMatcherInterface> Implementation;
};

MatchResult DynTypedPathMatcher::matches(const DynTypedNode &DynNode,
                                         GraphMatchFinder *Finder,
                                         GraphBoundNodesTreeBuilder *Builder,
                                         MatcherStateID StateID) const {
  return Implementation->dynMatches(DynNode, Finder, Builder, StateID);
  // if (Implementation->dynMatches(DynNode, Finder, Builder, StateID))
  //  return true;

  // Delete all bindings when a matcher does not match.
  // This prevents unexpected exposure of bound nodes in unmatches
  // branches of the match tree.
  // FIXME!!!
  //  Builder->removeBindings([](const BoundNodesMap &) { return true; });
  // return false;
}
/// \brief Wrapper of a MatcherInterface<T> *that allows copying.
///
/// A Matcher<Base> can be used anywhere a Matcher<Derived> is
/// required. This establishes an is-a relationship which is reverse
/// to the AST hierarchy. In other words, Matcher<T> is contravariant
/// with respect to T. The relationship is built via a type conversion
/// operator rather than a type hierarchy to be able to templatize the
/// type hierarchy instead of spelling it out.
template <typename T> class PathMatcher {
public:
  /// \brief Takes ownership of the provided implementation pointer.
  explicit PathMatcher(PathMatcherInterface<T> *Implementation)
      : Implementation(Implementation) {}

  explicit PathMatcher(const DynTypedPathMatcher &Implementation)
      : Implementation(Implementation) {}

  /// \brief Implicitly converts \c Other to a Matcher<T>.
  ///
  /// Requires \c T to be derived from \c From.
  PathMatcher(const PathMatcher<T> &Other)
      : Implementation(Other.Implementation) {}

  /// \brief Forwards the call to the underlying MatcherInterface<T> pointer.
  MatchResult matches(const T &GraphNode, GraphMatchFinder *Finder,
                      GraphBoundNodesTreeBuilder *Builder,
                      MatcherStateID StateID) const {
    return Implementation.matches(
        ento::ast_graph_type_traits::DynTypedNode::create(GraphNode), Finder,
        Builder, StateID);
  }

  /// \brief Extract the dynamic matcher.
  ///
  /// The returned matcher keeps the same restrictions as \c this and remembers
  /// that it is meant to support nodes of type \c T.
  operator DynTypedPathMatcher() const { return Implementation; }

private:
  // For DynTypedMatcher::unconditionalConvertTo<T>.
  friend class DynTypedPathMatcher;

  DynTypedPathMatcher Implementation;
}; // class PathMatcher
/*
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
*/
template <typename NodeTy> class BindEntry {
  GraphBoundNodeMap BoundItems;
  MatcherStateID StateID = 0;

public:
  BindEntry(PathMatcher<NodeTy> *Matcher, const GraphBoundNodeMap &Initial,
            MatcherStateID InitialID = 0)
      : BoundItems(Initial), StateID(InitialID), Matcher(Matcher) {}

  unsigned getStateID() { return StateID; }

  void advance() { ++StateID; }
  void advance(MatcherStateID NewStateID) { StateID = NewStateID; }

  void setStateID(MatcherStateID StateID) { this->StateID = StateID; }

  BindEntry addBinding(StringRef Key, DynTypedNode Binding) {
    BindEntry New = *this;
    New.BoundItems.insert(std::make_pair(Key, Binding));
    return New;
  }

  MatchResult matchNewNode(const NodeTy &Node, GraphMatchFinder *Finder,
                           GraphBoundNodesTreeBuilder *Builder);

  PathMatcher<NodeTy> *Matcher;
};
/*
class PathMatcher {
  using MatcherVector = std::vector<ExplodedNodeMatcher *>;
  MatcherVector InnerMatchers;

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
*/
class PSMatchesCallback : public MatchFinder::MatchCallback {
public:
  void run(const MatchFinder::MatchResult &Result) override {
    Nodes.push_back(Result.Nodes);
    HasMatches = true;
  }
  SmallVector<BoundNodes, 1> Nodes;
  bool HasMatches = false;
};
/*
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
*/
using ExplodedNodeMatcher = Matcher<ExplodedNode>;

VariadicAllOfMatcher<ExplodedNode> explodedNode;

AST_MATCHER_P(ExplodedNode, statementNode, StatementMatcher, Inner) {
  if (auto StmtPP = Node.getLocationAs<StmtPoint>())
    return Inner.matches(*StmtPP->getStmt(), Finder, Builder);
  return false;
}
/*
#define PROGRAM_POINT_MATCHER(Type, Name)                                      \
  AST_MATCHER_P(ExplodedNode, Name, ExplodedNodeMatcher, Inner) {              \
    if (auto PP = Node.getLocationAs<Type>())                                  \
      return Inner.matches(Node, Finder, Builder);                             \
    return false;                                                              \
  }

PROGRAM_POINT_MATCHER(PreStmt, preStmtNode)*/

AST_MATCHER_P(ExplodedNode, preStmtNode, ExplodedNodeMatcher, Inner) {
  if (Node.getLocationAs<PreStmt>())
    return Inner.matches(Node, Finder, Builder);
  return false;
}

AST_MATCHER_P(ExplodedNode, postStmtNode, ExplodedNodeMatcher, Inner) {
  if (Node.getLocationAs<PostStmt>())
    return Inner.matches(Node, Finder, Builder);
  return false;
}

AST_MATCHER_P(ExplodedNode, callEnterNode, StatementMatcher, Inner) {
  if (auto CallEnterPP = Node.getLocationAs<CallEnter>())
    if (const Stmt *CE = CallEnterPP->getCallExpr())
      return Inner.matches(*CE, Finder, Builder);
  return false;
}

static bool isLastNode(const DynTypedNode &Node) {
  if (const ExplodedNode *N = Node.get<ExplodedNode>())
    return N->succ_empty();
  return true;
}

using PathVariadicOperatorFunction = MatchResult (*)(
    const ento::ast_graph_type_traits::DynTypedNode &DynNode,
    GraphMatchFinder *Finder, GraphBoundNodesTreeBuilder *Builder,
    ArrayRef<DynTypedMatcher> InnerMatchers, MatcherStateID StateID);

template <PathVariadicOperatorFunction Func>
class VariadicPathMatcher : public DynPathMatcherInterface {
public:
  VariadicPathMatcher(std::vector<DynTypedMatcher> InnerMatchers)
      : InnerMatchers(std::move(InnerMatchers)) {}

  MatchResult
  dynMatches(const ento::ast_graph_type_traits::DynTypedNode &DynNode,
             GraphMatchFinder *Finder, GraphBoundNodesTreeBuilder *Builder,
             MatcherStateID StateID) const override {
    return Func(DynNode, Finder, Builder, InnerMatchers, StateID);
  }

private:
  std::vector<DynTypedMatcher> InnerMatchers;
};

/// \brief Polymorphic matcher object that uses a \c
/// DynTypedMatcher::VariadicOperator operator.
///
/// Input matchers can have any type (including other polymorphic matcher
/// types), and the actual Matcher<T> is generated on demand with an implicit
/// coversion operator.
template <PathVariadicOperatorFunction Func, typename... Ps>
class VariadicOperatorPathMatcher {
public:
  VariadicOperatorPathMatcher(Ps &&... Params)
      : Params(std::forward<Ps>(Params)...) {}

  template <typename NodeTy> operator PathMatcher<NodeTy>() const {
    return PathMatcher<NodeTy>(
        DynTypedPathMatcher(new VariadicPathMatcher<Func>(
            getMatchers<NodeTy>(llvm::index_sequence_for<Ps...>()))));
  }

private:
  // Helper method to unpack the tuple into a vector.
  template <typename T, std::size_t... Is>
  std::vector<DynTypedMatcher> getMatchers(llvm::index_sequence<Is...>) const {
    return {Matcher<T>(std::get<Is>(Params))...};
  }

  // const DynTypedMatcher::VariadicOperator Op;
  std::tuple<Ps...> Params;
};

/// \brief Overloaded function object to generate VariadicOperatorMatcher
///   objects from arbitrary matchers.
template <PathVariadicOperatorFunction Func, unsigned MinCount,
          unsigned MaxCount>
struct VariadicOperatorPathMatcherFunc {
  //  DynTypedMatcher::VariadicOperator Op;

  template <typename... Ms>
  VariadicOperatorPathMatcher<Func, Ms...> operator()(Ms &&... Ps) const {
    static_assert(MinCount <= sizeof...(Ms) && sizeof...(Ms) <= MaxCount,
                  "invalid number of parameters for variadic matcher");
    return VariadicOperatorPathMatcher<Func, Ms...>(std::forward<Ms>(Ps)...);
  }
};

/*
template <typename MatcherTy>
ExplodedNodeMatcher *statementNode(MatcherTy Inner) {
  return new StatementNodeMatcher<MatcherTy>(Inner);
}

ExplodedNodeMatcher *unlessPS(ExplodedNodeMatcher *Inner) {
  return new NotMatcher(Inner);
}
*/

class PathMatchCallback;

using PathSensMatcher = PathMatcher<ExplodedNode>;

class GraphMatchFinder {
  ASTContext &ASTCtx;
  std::vector<BindEntry<ExplodedNode>> Entries;
  GraphBoundNodesTreeBuilder Builder;
  GraphBoundNodeMap BoundMap;
  std::map<PathSensMatcher *, PathMatchCallback *> PathSensMatchers;

public:
  void match(const Decl *D);
  void match(ExplodedGraph &G, BugReporter &BR, ExprEngine &Eng);
  void addMatcher(const PathSensMatcher &Matcher, PathMatchCallback *Callback) {
    PathSensMatcher *Copy = new PathSensMatcher(Matcher);
    PathSensMatchers[Copy] = Callback;
  }

  void advance(const ExplodedNode *Pred, const ExplodedNode *Succ);
  ASTContext &getASTContext() { return ASTCtx; }
  GraphMatchFinder(ASTContext &ASTCtx) : ASTCtx(ASTCtx) {}
};

static std::pair<size_t, bool>
matchNotMatchers(size_t StartIndex, const DynTypedNode &Node, ASTContext &Ctx,
                 ArrayRef<DynTypedMatcher> Matchers) {
  size_t I = StartIndex;
  for (; I < Matchers.size(); ++I) {
    if (!Matchers[I].isNegative())
      return {I, true};
    MatchFinder Finder;
    // Currently, negative matchers are not allowed to add bound nodes.
    // FIXME: design and implement this.
    CollectMatchesCallback Callback;
    Finder.addDynamicMatcher(Matchers[I], &Callback);
    Finder.match(Node, Ctx);
    if (!Callback.HasMatches)
      // match(Matchers[I], Node.getUnchecked<T>(), Ctx);
      //   if (!match(Matchers[I], Node, Ctx))
      //  if (!Matchers[I].matches(Node, Finder, Builder))
      return {I, false};
  }
  return {I, true};
}

static size_t skipNotMatchers(size_t Index,
                              ArrayRef<DynTypedMatcher> Matchers) {
  while (Index < Matchers.size() && Matchers[Index].isNegative())
    ++Index;
  assert(Index != Matchers.size() && "Cannot skip terminating not matchers!");
  return Index;
}

static size_t matcherIndexByStateID(unsigned StateID,
                                    ArrayRef<DynTypedMatcher> Matchers) {
  size_t Index = 0, NumMatchers = Matchers.size();
  unsigned State = 0;
  for (; State < StateID && Index < NumMatchers; ++State) {
    Index = skipNotMatchers(Index, Matchers);
    ++Index;
  }
  assert(State == StateID && Index < NumMatchers &&
         "Cannot find the matcher corresponding to State ID!");
  return Index;
}

MatchResult SequenceVariadicOperator(
    const ento::ast_graph_type_traits::DynTypedNode &DynNode,
    GraphMatchFinder *Finder, GraphBoundNodesTreeBuilder *Builder,
    ArrayRef<DynTypedMatcher> InnerMatchers, MatcherStateID StateID) {
  size_t Index = matcherIndexByStateID(StateID, InnerMatchers);
  bool NegMatch = false;
  std::tie(Index, NegMatch) =
      matchNotMatchers(Index, DynNode, Finder->getASTContext(), InnerMatchers);
  if (!NegMatch) {
    if (StateID == 0)
      return {MatchAction::RejectForever, StateInvalid};
    else
      return {MatchAction::RejectSingle, StateInvalid};
  }

  bool IsNodeLast = isLastNode(DynNode);
  // Negative matchers are matching.
  if (Index == InnerMatchers.size()) {
    if (IsNodeLast)
      // If the node is last and no matchers remain, the path match
      // is accepted.
      return {MatchAction::Accept, Index};
    else
      // If the node is not last but all final negative matchers match,
      // continue matching until the final node is met.
      return {MatchAction::Pass, StateID};
  }

  // Next matcher should exist and it should be positive.
  assert(InnerMatchers[Index].isPositive());
  bool IsLastMatcher = Index == InnerMatchers.size() - 1;
  if (IsNodeLast && !IsLastMatcher)
    return {MatchAction::RejectSingle, StateInvalid};

  MatchFinder NodeFinder;
  CollectMatchesCallback CB;
  NodeFinder.addDynamicMatcher(InnerMatchers[Index], &CB);
  NodeFinder.match(DynNode, Finder->getASTContext());
  bool PositiveMatch =
      // InnerMatchers[Index].matches(DynNode, Finder->BasicFinder, Builder);
      CB.HasMatches;

  if (PositiveMatch) {
    if (IsLastMatcher)
      return {MatchAction::Accept, Index};
    else
      return {MatchAction::Advance, Index + 1};
  } else {
    return {MatchAction::Pass, StateID};
  }
  llvm_unreachable("The result should be already defined and returned!");
}

/// \brief Creates a Matcher<T> that matches if all inner matchers match.
template <typename NodeTy>
PathMatcher<NodeTy>
makeSequentialComposite(ArrayRef<const Matcher<NodeTy> *> InnerMatchers) {
  // For the size() == 0 case, we return a "true" matcher.
  if (InnerMatchers.empty()) {
    //   return PathMatcher<T>(TrueMatcher());
    assert(false && "Not implemented yet!");
  }
  // For the size() == 1 case, we simply return that one matcher.
  // No need to wrap it in a variadic operation.
  if (InnerMatchers.size() == 1) {
    assert(false && "Not implemented yet!");
    // return BindableMatcher<T>(*InnerMatchers[0]);
  }

  using PI = llvm::pointee_iterator<const Matcher<NodeTy> *const *>;

  std::vector<DynTypedMatcher> DynMatchers(PI(InnerMatchers.begin()),
                                           PI(InnerMatchers.end()));
  return PathMatcher<NodeTy>(
      DynTypedPathMatcher(new VariadicPathMatcher<SequenceVariadicOperator>(
          std::move(DynMatchers))));
}

///
/// FIXME: add a useful description.
template <typename NodeTy>
class VariadicSequentialPathMatcher
    : public VariadicFunction<PathMatcher<NodeTy>, Matcher<NodeTy>,
                              makeSequentialComposite<NodeTy>> {
public:
  VariadicSequentialPathMatcher() {}
};

// template <typename NodeTy>
const VariadicOperatorPathMatcherFunc<SequenceVariadicOperator, 1,
                                      std::numeric_limits<unsigned>::max()>
    hasSequence;

class PathMatchCallback {
public:
  virtual void run() = 0;
};

template <typename NodeTy>
MatchResult
BindEntry<NodeTy>::matchNewNode(const NodeTy &Node, GraphMatchFinder *Finder,
                                GraphBoundNodesTreeBuilder *Builder) {
  return Matcher->matches(Node, Finder, Builder, StateID);
}
/*
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
*/
void GraphMatchFinder::advance(const ExplodedNode *Pred,
                               const ExplodedNode *Succ) {
  // Advance and remove unmatched items if needed.
  size_t I = 0;
  while (I < Entries.size()) {
    BindEntry<ExplodedNode> &Entry = Entries[I];
    MatchResult MatchRes = Entry.matchNewNode(*Succ, this, &Builder);
    switch (MatchRes.Action) {
    case MatchAction::Advance:
      Entry.advance(MatchRes.NewStateID);
      ++I;
      break;
    case MatchAction::Accept: {
      auto *Callback = PathSensMatchers[Entry.Matcher];
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
      llvm_unreachable("Existing entries should never receive RejectForever!");
    default:
      llvm_unreachable("Non-existing match result!");
    }
  }

  // Check if a new item (StateID == 0) should be added.
  for (auto &MatchItem : PathSensMatchers) {
    PathSensMatcher *Matcher = MatchItem.first;
    MatchResult Res = Matcher->matches(*Succ, this, &Builder, 0);
    if (Res.Action == MatchAction::Advance) {
      GraphBoundNodeMap Bounds;
      Entries.emplace_back(Matcher, Bounds, Res.NewStateID);
    } else if (Res.Action == MatchAction::Accept) {
      auto *Callback = PathSensMatchers[Matcher];
      Callback->run();
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

  StatementMatcher NotChdir =
      callExpr(unless(callee(functionDecl(hasName("::chdir")))));
  Finder.addMatcher(
      hasSequence(postStmtNode(statementNode(
                      callExpr(callee(functionDecl(hasName("::chroot")))))),
                  unless(statementNode(
                      callExpr(callee(functionDecl(hasName("::chdir"))),
                               hasArgument(0, stringLiteral(hasSize(1)))))),
                  explodedNode(anyOf(postStmtNode(statementNode(NotChdir)),
                                     callEnterNode(NotChdir)))),
      &Callback);
  Finder.match(G, BR, Eng);
}

void ento::registerPthreadLockCheckerV2(CheckerManager &Mgr) {
  Mgr.registerChecker<PthreadLockCheckerV2>();
}
