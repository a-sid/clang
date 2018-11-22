//===--- GraphMatchFinder.cpp - Structural query framework ----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  Implements an algorithm to search for matches on AST-based graphs.
//  Uses memoization to support recursive matches like HasDescendant.
//
//  The general idea is to visit all graph nodes with a given visitor (not
//  implemented yet!). Matcher callback matches() is called on each new node
//  discovered by the traversal algorithm.
//
//===----------------------------------------------------------------------===//

#include "clang/StaticAnalyzer/Matchers/GraphMatchFinder.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ExprEngine.h"

using namespace clang;
using namespace ento;
using namespace path_matchers;
using namespace internal;

void GraphMatchFinder::advanceSingleEntry(size_t &Index,
                                          const ExplodedNode *N) {
  BindEntry<ExplodedNode> &Entry = Entries[Index];
  GraphBoundNodesTreeBuilder Builder(BoundMap, Entry.getMatchID(), N);
  MatchResult MatchRes = Entry.matchNewNode(*N, this, &Builder);
  switch (MatchRes.Action) {
  case MatchAction::Advance:
    Entry.advance(MatchRes.NewStateID);
    ++Index;
    break;
  case MatchAction::Accept: {
    auto *Callback = PathSensMatchers[Entry.Matcher];
    Callback->run(*CurrentEngine, Builder.getBoundNodes(), this);
  } // Fall-through
  case MatchAction::RejectSingle:
    Entries.erase(Entries.begin() + Index);
    break;
  case MatchAction::Pass:
  case MatchAction::StartNew:
    ++Index;
    // Do nothing.
    break;
  case MatchAction::RejectForever:
    llvm_unreachable(
        "Existing entries should never receive RejectForever!");
  default:
    llvm_unreachable("Non-existing match result!");
  }
}

void GraphMatchFinder::tryStartNewMatch(PathSensMatcher *Matcher,
                                        PathMatchCallback *Callback,
                                        const ExplodedNode *N) {
  if (RejectedMatchers.isRejectedForever(N, Matcher))
    return;

  auto Builder = GraphBoundNodesTreeBuilder::getTemporary(BoundMap, N);
  MatchResult Res = Matcher->matches(*N, this, &Builder, 0);
  if (Res.isStartNew()) {
    const auto &NewEntry = Entries.addMatch(Matcher, Res.NewStateID);
    Builder.acceptTemporary(NewEntry.getMatchID());

  } else if (Res.isAccept()) {
    Callback->run(*CurrentEngine, Builder.getBoundNodes(), this);

  } else if (Res.Action == MatchAction::RejectForever) {
    RejectedMatchers.rejectMatcher(N, Matcher);
  }
}

void GraphMatchFinder::runOfflineChecks(const ExplodedNode *Pred,
                                        const ExplodedNode *Succ) {
  assert(CurrentEngine && "Should set current graph before matching!");

  // Advance and remove unmatched items if needed.
  BoundMap.advance(Pred, Succ);
  RejectedMatchers.advance(Pred, Succ);

  size_t I = 0;
  while (I < Entries.size())
    advanceSingleEntry(I, Succ);

  // Check if a new item (StateID == 0) should be added.
  for (auto &MatchItem : PathSensMatchers)
    tryStartNewMatch(MatchItem.first, MatchItem.second, Succ);
}

void GraphMatchFinder::runOnlineChecks(ExplodedNode *Pred, ExplodedNode *Succ,
                                       ExplodedNodeSet &Dst) {
  assert(CurrentEngine && "Should set current graph before matching!");

  ExplodedNodeSet Tmp1, Tmp2;
  Tmp1.Add(Succ);
  ExplodedNodeSet *PrevSet = &Tmp1;

  // Advance and remove unmatched items if needed.
  size_t I = 0;
  while (I < Entries.size()) {
    ExplodedNodeSet *CurrSet = (PrevSet == &Tmp2) ? &Tmp1 : &Tmp2;
    CurrSet->clear();

    NodeBuilderWithSinks NB(*PrevSet, *CurrSet,
                            CurrentEngine->getBuilderContext(),
                            (*PrevSet->begin())->getLocation());
    setNodeBuilder(&NB);

    for (ExplodedNode *N : *PrevSet)
      advanceSingleEntry(I, N);

    if (CurrSet->empty()) {
      resetNodeBuilder();
      return;
    }
    PrevSet = CurrSet;
  }

  // Check if a new item (StateID == 0) should be added.
  for (auto &MatchItem : PathSensMatchers) {
    ExplodedNodeSet *CurrSet = (PrevSet == &Tmp2) ? &Tmp1 : &Tmp2;
    CurrSet->clear();

    NodeBuilderWithSinks NB(*PrevSet, *CurrSet,
                            CurrentEngine->getBuilderContext(),
                            (*PrevSet->begin())->getLocation());
    setNodeBuilder(&NB);

    for (const ExplodedNode *N : *PrevSet)
      tryStartNewMatch(MatchItem.first, MatchItem.second, N);

    PrevSet = CurrSet;
  }

  // The analysis is over.
  Dst = *PrevSet;
  resetNodeBuilder();
}

void GraphMatchFinder::match(ExplodedGraph &G, ExprEngine &Eng) {
  reset(&Eng);
  // Simple DFS on ExplodedGraph nodes.
  // FIXME: Make the visitor configurable.
  using ENodeRef = const ExplodedNode *;
  SmallVector<ENodeRef, 256> Stack;
  llvm::DenseSet<ENodeRef> Visited;
  for (ENodeRef Root : G.roots()) {
    runOfflineChecks(nullptr, Root);
    Stack.push_back(Root);
    Visited.insert(Root);
  }

  while (!Stack.empty()) {
    ENodeRef From = Stack.pop_back_val();
    for (ENodeRef Succ : From->successors()) {
      if (Visited.insert(Succ).second) { // Not visited before
        runOfflineChecks(From, Succ);
        Stack.push_back(Succ);
      }
    }
  }
}

MatchResult
DynTypedPathMatcher::matches(const ast_graph_type_traits::DynTypedNode &DynNode,
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
