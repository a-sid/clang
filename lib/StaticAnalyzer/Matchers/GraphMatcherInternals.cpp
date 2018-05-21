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
  auto MatcherNodes = Bounds.getMatches(CurrentNode, CurrentID);
  if (!MatcherNodes.second)
    return DynTypedNode();
  return MatcherNodes.first->second.getNode(ID);
}

astm_internal::BoundNodesMap GraphBoundNodesTreeBuilder::getBoundNodes() {
  auto MatcherNodes = Bounds.getMatches(CurrentNode, CurrentID);
  return MatcherNodes.second ? MatcherNodes.first->second
                             : astm_internal::BoundNodesMap();
}

namespace {

static bool isLastNode(const DynTypedNode &Node) {
  if (const ExplodedNode *N = Node.get<ExplodedNode>())
    return N->succ_empty();
  return true;
}

static astm_internal::CollectMatchesCallback
getASTMatches(const DynTypedNode &DynNode,
              const astm_internal::DynTypedMatcher &Matcher, ASTContext &ACtx,
              GraphBoundNodesTreeBuilder *Builder) {
  MatchFinder NodeFinder;
  static int t = 0; ++t;
  astm_internal::CollectMatchesCallback CB;
  NodeFinder.addDynamicMatcher(Matcher, &CB);
  std::unique_ptr<EGraphContext> EGContext;
  if (const ExplodedNode *ENode = DynNode.get<ExplodedNode>()) {
    EGContext.reset(new EGraphContext(*Builder, ENode));
    NodeFinder.addContext(EGContext.get());
  }
  NodeFinder.match(DynNode, ACtx);
  return CB;
}

std::pair<size_t, bool>
matchNotMatchers(size_t StartIndex, const DynTypedNode &Node,
                 GraphBoundNodesTreeBuilder *Builder, ASTContext &ACtx,
                 ArrayRef<astm_internal::DynTypedMatcher> Matchers) {
  size_t I = StartIndex;
  for (; I < Matchers.size(); ++I) {
    if (!Matchers[I].isNegative())
      return {I, true};

    // Currently, negative matchers are not allowed to add bound nodes.
    auto Callback = getASTMatches(Node, Matchers[I], ACtx, Builder);
    if (!Callback.HasMatches)
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
      return {MatchAction::Accept, static_cast<MatcherStateID>(Index)};
    else
      // If the node is not last but all final negative matchers match,
      // continue matching until the final node is met.
      return {MatchAction::Pass, StateID};
  }

  // Next matcher should exist and it should be positive.
  assert(InnerMatchers[Index].isPositive());
  bool IsLastMatcher = Index == InnerMatchers.size() - 1;
  bool IsNewMatch = StateID == 0;

  if (IsNodeLast && !IsLastMatcher)
    return {MatchAction::RejectSingle, StateInvalid};

  auto Callback = getASTMatches(DynNode, InnerMatchers[Index],
                                Finder->getASTContext(), Builder);
  bool PositiveMatch = Callback.HasMatches;
  if (PositiveMatch) {
    Builder->addMatches(Callback.Nodes);
    if (IsLastMatcher)
      return {MatchAction::Accept, static_cast<MatcherStateID>(Index)};
    else if (IsNewMatch)
      return {MatchAction::StartNew, static_cast<MatcherStateID>(Index + 1)};
    else
      return {MatchAction::Advance, static_cast<MatcherStateID>(Index + 1)};
  } else {
    return {MatchAction::Pass, StateID};
  }
  llvm_unreachable("The result should be already defined and returned!");
}

MatchResult CountingPathMatcher::dynMatches(const DynTypedNode &DynNode,
                                            GraphMatchFinder *Finder,
                                            GraphBoundNodesTreeBuilder *Builder,
                                            MatcherStateID StateID) const {
  ASTContext &ACtx = Finder->getASTContext();
  auto IncCallback = getASTMatches(DynNode, IncrementMatcher, ACtx, Builder);
  if (IncCallback.HasMatches) {
    Builder->addMatches(IncCallback.Nodes);
    MatcherStateID NewState = StateID;
    if (NewState < UpperLimit) {
      ++NewState;
      if (NewState == MatchCounter)
        return {MatchAction::Accept, NewState};
      return {MatchAction::Advance, NewState};
    }
    return {MatchAction::Pass, StateID};
  }

  auto DecCallback = getASTMatches(DynNode, DecrementMatcher, ACtx, Builder);
  if (DecCallback.HasMatches) {
    Builder->addMatches(DecCallback.Nodes);
    MatcherStateID NewState = StateID;
    if (NewState > LowerLimit) {
      --NewState;
      if (NewState == MatchCounter)
        return {MatchAction::Accept, NewState};
      return {MatchAction::Advance, NewState};
    }
    return {MatchAction::Pass, StateID};
  }

  // FIXME: Determine what to do if action matchers and start matchers match
  // same node.
  auto AddCallback = getASTMatches(DynNode, StartMatcher, ACtx, Builder);
  if (AddCallback.HasMatches) {
    Builder->addMatches(AddCallback.Nodes);
    return {MatchAction::StartNew, InitialCounter};
  }

  return {MatchAction::Pass, StateID};
}

} // end namespace internal

const astm_internal::VariadicAllOfMatcher<ExplodedNode> explodedNode;
const astm_internal::VariadicDynCastAllOfMatcher<SVal, DefinedSVal> definedSVal;
const astm_internal::VariadicAllOfMatcher<MemRegion> memRegion;
const astm_internal::VariadicDynCastAllOfMatcher<MemRegion, StringRegion>
    stringRegion;
const astm_internal::VariadicAllOfMatcher<LocationContext> locationContext;
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
const astm_internal::VariadicDynCastAllOfMatcher<ProgramPoint, CallExitEnd>
    callExitEnd;

} // end namespace path_matchers

} // end namespace ento

} // end namespace clang
