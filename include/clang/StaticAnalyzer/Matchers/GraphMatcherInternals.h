//===- GraphMatchersInternal.h - Structural query framework ------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  Implements the base layer of the path matcher framework.
//
//  The way how path-sensitive matchers work is very similar to AST matchers,
//  with one difference: their matches() method also takes a parameter
//  identifying the current state.
//  FIXME: We have to unify this code with ASTMatcherInternals.h after it
//  stopped being a sandbox.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_ASTMATCHERS_GRAPHMATCHERSINTERNAL_H
#define LLVM_CLANG_ASTMATCHERS_GRAPHMATCHERSINTERNAL_H

#include "clang/ASTMatchers/ASTGraphTypeTraits.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramStateTrait.h"
#include "clang/StaticAnalyzer/Matchers/EGraphContext.h"

#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "llvm/ADT/StringMap.h"

namespace clang {

namespace ento {

namespace path_matchers {

class GraphMatchFinder;

namespace internal {

class GraphBoundNodeMap;
class GraphBoundNodesTreeBuilder {};

class GraphBoundNodeMap
    : public llvm::StringMap<ast_graph_type_traits::DynTypedNode> {
public:
  using BoundRecordType = StringMap<ast_graph_type_traits::DynTypedNode>;
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
  llvm::DenseMap<const ExplodedNode *, BoundRecordType> Bounds;
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
  llvm::Optional<DynTypedPathMatcher> tryBind(StringRef ID) const;

private:
  bool AllowBind = false;
  IntrusiveRefCntPtr<DynPathMatcherInterface> Implementation;
};

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

using PathVariadicOperatorFunction = MatchResult (*)(
    const ast_graph_type_traits::DynTypedNode &DynNode,
    GraphMatchFinder *Finder, GraphBoundNodesTreeBuilder *Builder,
    ArrayRef<ast_matchers::internal::DynTypedMatcher> InnerMatchers,
    MatcherStateID StateID);

template <PathVariadicOperatorFunction Func>
class VariadicPathMatcher : public DynPathMatcherInterface {
public:
  VariadicPathMatcher(
      std::vector<ast_matchers::internal::DynTypedMatcher> InnerMatchers)
      : InnerMatchers(std::move(InnerMatchers)) {}

  MatchResult dynMatches(const ast_graph_type_traits::DynTypedNode &DynNode,
                         GraphMatchFinder *Finder,
                         GraphBoundNodesTreeBuilder *Builder,
                         MatcherStateID StateID) const override {
    return Func(DynNode, Finder, Builder, InnerMatchers, StateID);
  }

private:
  std::vector<ast_matchers::internal::DynTypedMatcher> InnerMatchers;
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
  std::vector<ast_matchers::internal::DynTypedMatcher>
  getMatchers(llvm::index_sequence<Is...>) const {
    return {ast_matchers::internal::Matcher<T>(std::get<Is>(Params))...};
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

class PathMatchCallback;

using PathSensMatcher = PathMatcher<ExplodedNode>;

MatchResult SequenceVariadicOperator(
    const ast_graph_type_traits::DynTypedNode &DynNode,
    GraphMatchFinder *Finder, GraphBoundNodesTreeBuilder *Builder,
    ArrayRef<ast_matchers::internal::DynTypedMatcher> InnerMatchers,
    MatcherStateID StateID);

/// \brief Creates a Matcher<T> that matches if all inner matchers match.
template <typename NodeTy>
PathMatcher<NodeTy> makeSequentialComposite(
    ArrayRef<const ast_matchers::internal::Matcher<NodeTy> *> InnerMatchers) {
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

  using PI = llvm::pointee_iterator<
      const ast_matchers::internal::Matcher<NodeTy> *const *>;

  std::vector<ast_matchers::internal::DynTypedMatcher> DynMatchers(
      PI(InnerMatchers.begin()), PI(InnerMatchers.end()));
  return PathMatcher<NodeTy>(
      DynTypedPathMatcher(new VariadicPathMatcher<SequenceVariadicOperator>(
          std::move(DynMatchers))));
}

///
/// FIXME: add a useful description.
template <typename NodeTy>
class VariadicSequentialPathMatcher
    : public ast_matchers::internal::VariadicFunction<
          PathMatcher<NodeTy>, ast_matchers::internal::Matcher<NodeTy>,
          makeSequentialComposite<NodeTy>> {
public:
  VariadicSequentialPathMatcher() {}
};

class PathMatchCallback {
public:
  virtual void run() = 0;
};

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

  BindEntry addBinding(StringRef Key,
                       ento::ast_graph_type_traits::DynTypedNode Binding) {
    BindEntry New = *this;
    New.BoundItems.insert(std::make_pair(Key, Binding));
    return New;
  }

  MatchResult matchNewNode(const NodeTy &Node, GraphMatchFinder *Finder,
                           GraphBoundNodesTreeBuilder *Builder);

  PathMatcher<NodeTy> *Matcher;
};

template <typename NodeTy>
MatchResult
BindEntry<NodeTy>::matchNewNode(const NodeTy &Node, GraphMatchFinder *Finder,
                                GraphBoundNodesTreeBuilder *Builder) {
  return Matcher->matches(Node, Finder, Builder, StateID);
}

} // end namespace internal

} // end namespace path_matchers

} // end namespace ento

} // end namespace clang

#endif // LLVM_CLANG_ASTMATCHERS_GRAPHMATCHERSINTERNAL_H
