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
#include "clang/StaticAnalyzer/Matchers/GraphMatchers.h"

#include "clang/ASTMatchers/ASTMatchersInternal.h"

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

  StoredItemTy &getOrCreateMatches(NodeTy Node, internal::MatcherID MatchID) {
    return getGDM(Node)[MatchID];
  }

  std::pair<GDMTy::const_iterator, bool>
  getMatches(NodeTy Node, internal::MatcherID MatchID) {
    auto &GDM = getGDM(Node);
    auto Found = GDM.find(MatchID);
    return {Found, Found != GDM.end()};
  }

  void addMatches(NodeTy Node, internal::MatcherID MatchID,
                  const ast_matchers::BoundNodes &Nodes) {
    auto &Entry = getOrCreateMatches(Node, MatchID);
    for (const auto &Item : Nodes.getMap())
      Entry.addNode(Item.first, Item.second);
  }

private:
  GraphGDMTy GraphGDM;
};

class GraphMatchFinder {
public:
  class PathMatchCallback {
  public:
    virtual void run(const GraphBoundNodesMap::StoredItemTy &BoundNodes) = 0;
  };

private:
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
  std::map<internal::PathSensMatcher *, PathMatchCallback *> PathSensMatchers;

public:
  void match(const Decl *D);
  void match(ExplodedGraph &G, BugReporter &BR, ExprEngine &Eng);
  void addMatcher(const internal::PathSensMatcher &Matcher,
                  PathMatchCallback *Callback) {
    internal::PathSensMatcher *Copy = new internal::PathSensMatcher(Matcher);
    PathSensMatchers[Copy] = Callback;
  }

  void advance(const ExplodedNode *Pred, const ExplodedNode *Succ);
  ASTContext &getASTContext() { return ASTCtx; }
  GraphMatchFinder(ASTContext &ASTCtx) : ASTCtx(ASTCtx) {}
};

template <typename CalleeTy>
class ProxyMatchCallback : public GraphMatchFinder::PathMatchCallback {
  CalleeTy Callee;

public:
  ProxyMatchCallback(CalleeTy Callee) : Callee(Callee) {}

  virtual void
  run(const GraphBoundNodesMap::StoredItemTy &BoundNodes) override {
    Callee(BoundNodes);
  }
};

template <typename CalleeTy>
ProxyMatchCallback<CalleeTy> createProxyCallback(CalleeTy Callee) {
  return ProxyMatchCallback<CalleeTy>(Callee);
}

} // end namespace path_matchers

} // end namespace ento

} // end namespace clang

#endif // LLVM_CLANG_ENTO_MATCHERS_GRAPHMATCHFINDER_H
