//===- GraphMatcherFinder.h - Structural query framework --------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  A graph search engine allowing to match paths inside a given graph that
//  satisfy some give conditions.
//
//  GraphMatchFinder performs a graph traversal and notifies its matchers about
//  each new node discovered. Matchers should return the result of the match
//  so finder can update the state of the match object or remove it
//  as non-matching anymore. The exact logic of state transition should be
//  encapsulated into matchers.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_ENTO_MATCHERS_GRAPHMATCHFINDER_H
#define LLVM_CLANG_ENTO_MATCHERS_GRAPHMATCHFINDER_H

#include "clang/ASTMatchers/ASTGraphTypeTraits.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramStateTrait.h"
#include "clang/StaticAnalyzer/Matchers/EGraphContext.h"
#include "clang/StaticAnalyzer/Matchers/GraphMatchers.h"

#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "llvm/ADT/StringMap.h"

namespace clang {

namespace ento {

class BugReporter;
class ExprEngine;

namespace path_matchers {

// template <typename NodeTy>
class GraphBoundNodesMap {
public:
  using NodeTy = const ExplodedNode *;
  using StoredItemTy = ast_matchers::internal::BoundNodesMap;
  using GDMTy = std::map<internal::MatcherID, StoredItemTy>;
  using GraphGDMTy = std::map<const ExplodedNode *, GDMTy>;

  GraphBoundNodesMap() : GraphGDM{{nullptr, GDMTy()}} {}

  void advance(NodeTy Pred, NodeTy Succ) {
    assert(GraphGDM.find(Pred) != GraphGDM.end() &&
           "Cannot advance from non-existing node");
    assert(GraphGDM.find(Succ) == GraphGDM.end() &&
           "Successor already was processed!");
    GraphGDM[Succ] = GraphGDM[Pred];
  }

  GDMTy &getGDM(NodeTy Node) {
    auto Found = GraphGDM.find(Node);
    assert(Found != GraphGDM.end() && "Requested GDM for non-existing node!");
    return Found->second;
  }

  void addMatches(NodeTy Node, internal::MatcherID MatchID,
                  const ast_matchers::BoundNodes &Nodes) {
    auto &GDM = getGDM(Node);
    StoredItemTy &Entry = GDM[MatchID]; // Create if doesn't exist.
    for (const auto &Item : Nodes.getMap())
      Entry.addNode(Item.first, Item.second);
  }

private:
  GraphGDMTy GraphGDM;
};

class GraphMatchFinder {
  using EntryTy = internal::BindEntry<ExplodedNode>;

  class EntriesTy : public std::vector<EntryTy> {
    internal::MatcherID AddCounter = 0;

  public:
    const EntryTy &addMatch(internal::PathSensMatcher *Matcher,
                            internal::MatcherStateID StateID) {
      emplace_back(Matcher, StateID, AddCounter++);
      return back();
    }
  };

  ASTContext &ASTCtx;
  EntriesTy Entries;
  GraphBoundNodesMap BoundMap;
  std::map<internal::PathSensMatcher *, internal::PathMatchCallback *>
      PathSensMatchers;

public:
  void match(const Decl *D);
  void match(ExplodedGraph &G, BugReporter &BR, ExprEngine &Eng);
  void addMatcher(const internal::PathSensMatcher &Matcher,
                  internal::PathMatchCallback *Callback) {
    internal::PathSensMatcher *Copy = new internal::PathSensMatcher(Matcher);
    PathSensMatchers[Copy] = Callback;
  }

  void advance(const ExplodedNode *Pred, const ExplodedNode *Succ);
  ASTContext &getASTContext() { return ASTCtx; }
  GraphMatchFinder(ASTContext &ASTCtx) : ASTCtx(ASTCtx) {}
};

} // end namespace path_matchers

} // end namespace ento

} // end namespace clang

#endif // LLVM_CLANG_ENTO_MATCHERS_GRAPHMATCHFINDER_H
