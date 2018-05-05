//===- GraphMatchersInternal.cpp - Structural query framework -------------===//
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
//===----------------------------------------------------------------------===//

#include "clang/StaticAnalyzer/Matchers/GraphMatchFinder.h"

using namespace clang;
using namespace ento;
using namespace ast_graph_type_traits;
using namespace ast_matchers;
namespace astm_internal = ast_matchers::internal;

namespace clang {

namespace ento {

namespace path_matchers {

namespace internal {

constexpr MatcherID GraphBoundNodesTreeBuilder::TemporaryID;

void GraphBoundNodesTreeBuilder::addMatches(ArrayRef<BoundNodes> Nodes) {
  if (!Nodes.empty() && !Nodes[0].getMap().empty())
    Bounds.addMatches(CurrentNode, CurrentID, Nodes[0]);
}

void GraphBoundNodesTreeBuilder::acceptTemporary(MatcherID NewID) {
  auto &GDM = Bounds.getGDM(CurrentNode);
  auto TempIter = GDM.find(TemporaryID);
  if (TempIter != GDM.end()) {
    GDM[NewID] = TempIter->second;
    GDM.erase(TempIter);
  }
}

DynTypedNode GraphBoundNodesTreeBuilder::getBoundNode(StringRef ID) {
  auto &GDM = Bounds.getGDM(CurrentNode);
  auto MatcherNodes = GDM.find(CurrentID);
  if (MatcherNodes == GDM.end())
    return DynTypedNode();
  return MatcherNodes->second.getNode(ID);
}

namespace {

bool isLastNode(const DynTypedNode &Node) {
  if (const ExplodedNode *N = Node.get<ExplodedNode>())
    return N->succ_empty();
  return true;
}

static std::pair<size_t, bool>
matchNotMatchers(size_t StartIndex, const DynTypedNode &Node,
                 GraphBoundNodesTreeBuilder *Builder, ASTContext &Ctx,
                 ArrayRef<astm_internal::DynTypedMatcher> Matchers) {
  size_t I = StartIndex;
  for (; I < Matchers.size(); ++I) {
    if (!Matchers[I].isNegative())
      return {I, true};
    MatchFinder Finder;
    // Currently, negative matchers are not allowed to add bound nodes.
    // FIXME: design and implement this.
    astm_internal::CollectMatchesCallback Callback;
    Finder.addDynamicMatcher(Matchers[I], &Callback);
    std::unique_ptr<EGraphContext> EGContext;
    if (const ExplodedNode *ENode = Node.get<ExplodedNode>()) {
      EGContext.reset(new EGraphContext(*Builder, ENode));
      Finder.addContext(EGContext.get());
    }
    Finder.match(Node, Ctx);
    if (!Callback.HasMatches)
      // match(Matchers[I], Node.getUnchecked<T>(), Ctx);
      //   if (!match(Matchers[I], Node, Ctx))
      //  if (!Matchers[I].matches(Node, Finder, Builder))
      return {I, false};
  }
  return {I, true};
}

static size_t
skipNotMatchers(size_t Index,
                ArrayRef<ast_matchers::internal::DynTypedMatcher> Matchers) {
  while (Index < Matchers.size() && Matchers[Index].isNegative())
    ++Index;
  assert(Index != Matchers.size() && "Cannot skip terminating not matchers!");
  return Index;
}

static size_t
matcherIndexByStateID(unsigned StateID,
                      ArrayRef<astm_internal::DynTypedMatcher> Matchers) {
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

} // end anonymous namespace

MatchResult
SequenceVariadicOperator(const DynTypedNode &DynNode, GraphMatchFinder *Finder,
                         GraphBoundNodesTreeBuilder *Builder,
                         ArrayRef<astm_internal::DynTypedMatcher> InnerMatchers,
                         MatcherStateID StateID) {
  size_t Index = matcherIndexByStateID(StateID, InnerMatchers);
  bool NegMatch = false;
  std::tie(Index, NegMatch) = matchNotMatchers(
      Index, DynNode, Builder, Finder->getASTContext(), InnerMatchers);
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
  astm_internal::CollectMatchesCallback CB;
  NodeFinder.addDynamicMatcher(InnerMatchers[Index], &CB);
  std::unique_ptr<EGraphContext> EGContext;
  if (const ExplodedNode *ENode = DynNode.get<ExplodedNode>()) {
    EGContext.reset(new EGraphContext(*Builder, ENode));
    NodeFinder.addContext(EGContext.get());
  }
  NodeFinder.match(DynNode, Finder->getASTContext());
  bool PositiveMatch =
      // InnerMatchers[Index].matches(DynNode, Finder->BasicFinder, Builder);
      CB.HasMatches;

  if (PositiveMatch) {
    Builder->addMatches(CB.Nodes);
    if (IsLastMatcher)
      return {MatchAction::Accept, Index};
    else
      return {MatchAction::Advance, Index + 1};
  } else {
    return {MatchAction::Pass, StateID};
  }
  llvm_unreachable("The result should be already defined and returned!");
}

} // end namespace internal

const astm_internal::VariadicAllOfMatcher<ExplodedNode> explodedNode;
const astm_internal::VariadicDynCastAllOfMatcher<SVal, DefinedSVal> definedSVal;
const astm_internal::VariadicDynCastAllOfMatcher<MemRegion, StringRegion>
    stringRegion;
const astm_internal::VariadicDynCastAllOfMatcher<LocationContext,
                                                 StackFrameContext>
    stackFrameContext;
const astm_internal::VariadicAllOfMatcher<ProgramPoint> programPoint;
const astm_internal::VariadicDynCastAllOfMatcher<ProgramPoint, PreStmt> preStmt;
const astm_internal::VariadicDynCastAllOfMatcher<ProgramPoint, PostStmt>
    postStmt;
const astm_internal::VariadicDynCastAllOfMatcher<ProgramPoint, BlockEdge>
    blockEdge;
const astm_internal::VariadicDynCastAllOfMatcher<ProgramPoint, PostCondition>
    postCondition;
const astm_internal::VariadicDynCastAllOfMatcher<ProgramPoint, StmtPoint>
    stmtPoint;
const astm_internal::VariadicDynCastAllOfMatcher<ProgramPoint, CallEnter>
    callEnter;
} // end namespace path_matchers

} // end namespace ento

} // end namespace clang
