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

using namespace clang;
using namespace ento;
using namespace path_matchers;
using namespace internal;

void GraphMatchFinder::advance(const ExplodedNode *Pred,
                               const ExplodedNode *Succ) {
  // Advance and remove unmatched items if needed.
  size_t I = 0;
  BoundMap.advance(Pred, Succ);
  while (I < Entries.size()) {
    BindEntry<ExplodedNode> &Entry = Entries[I];
    GraphBoundNodesTreeBuilder Builder(BoundMap, Entry.getMatchID(), Succ);
    MatchResult MatchRes = Entry.matchNewNode(*Succ, this, &Builder);
    switch (MatchRes.Action) {
    case MatchAction::Advance:
      Entry.advance(MatchRes.NewStateID);
      ++I;
      break;
    case MatchAction::Accept: {
      auto *Callback = PathSensMatchers[Entry.Matcher];
      Callback->run(Builder.getBoundNodes());
    } // Fall-through
    case MatchAction::RejectSingle:
      Entries.erase(Entries.begin() + I);
      break;
    case MatchAction::Pass:
    case MatchAction::StartNew:
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
    if (RejectedMatchers.count(Matcher))
      continue;

    auto Builder = GraphBoundNodesTreeBuilder::getTemporary(BoundMap, Succ);
    MatchResult Res = Matcher->matches(*Succ, this, &Builder, 0);
    if (Res.isStartNew()) {
      const auto &NewEntry = Entries.addMatch(Matcher, Res.NewStateID);
      Builder.acceptTemporary(NewEntry.getMatchID());

    } else if (Res.isAccept()) {
      auto *Callback = PathSensMatchers[Matcher];
      Callback->run(Builder.getBoundNodes());

    } else if (Res.Action == MatchAction::RejectForever) {
      RejectedMatchers.insert(Matcher);
    }
  }
}

void GraphMatchFinder::match(const ExplodedGraph &G) {
  // Simple DFS on ExplodedGraph nodes.
  // FIXME: Make the visitor configurable.
  typedef const ExplodedNode *ENodeRef;
  typedef std::pair<ENodeRef, ENodeRef> VisitEntry;
  SmallVector<ENodeRef, 256> Stack;
  llvm::DenseSet<ENodeRef> Visited;
  for (ENodeRef Root : G.roots()) {
    advance(nullptr, Root);
    Stack.push_back(Root);
    Visited.insert(Root);
  }

  while (!Stack.empty()) {
    ENodeRef From = Stack.pop_back_val();
    for (ENodeRef Succ : From->successors()) {
      if (Visited.insert(Succ).second) { // Not visited before
        advance(From, Succ);
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
