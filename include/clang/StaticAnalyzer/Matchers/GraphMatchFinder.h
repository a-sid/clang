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
#include "clang/ASTMatchers/ASTMatchersInternal.h"
#include "clang/StaticAnalyzer/Matchers/GraphMatcherInternals.h"
#include "llvm/ADT/StringMap.h"

namespace llvm {

template <>
struct FoldingSetTrait<clang::ast_matchers::internal::BoundNodesMap>
    : DefaultFoldingSetTrait<clang::ast_matchers::internal::BoundNodesMap> {
  using StoredItemTy = clang::ast_matchers::internal::BoundNodesMap;

  static void Profile(const StoredItemTy &X, FoldingSetNodeID &ID) {
    for (const auto &Entry : X.getMap()) {
        ID.AddString(Entry.first);
        ID.AddInteger(clang::ento::ast_graph_type_traits::DynTypedNode::
                          DenseMapInfo::getHashValue(Entry.second));
      }
  }
};

} // namespace llvm

namespace clang {

namespace ento {

class BugReporter;
class ExprEngine;
class NodeBuilder;

namespace path_matchers {


// template <typename NodeTy>
class GraphBoundNodesMap {
public:
  using NodeTy = const ExplodedNode *;
  using StoredItemTy = ast_matchers::internal::BoundNodesMap;
  using GDMTy = llvm::ImmutableMap<internal::MatcherID, StoredItemTy>;
  using GDMFactory = GDMTy::Factory;
  using GraphGDMTy = std::map<const ExplodedNode *, GDMTy>;

  GraphGDMTy::iterator insertOrUpdate(NodeTy Node, GDMTy NewGDM) {
    auto Found = GraphGDM.insert({Node, NewGDM});
    if (!Found.second) {
      Found.first->second = NewGDM;
    }
    return Found.first;
  }

  GraphBoundNodesMap()
      : Factory(), GraphGDM{{nullptr, Factory.getEmptyMap()}} {}

  void advance(NodeTy Pred, NodeTy Succ) {
    assert(GraphGDM.find(Pred) != GraphGDM.end() &&
           "Cannot advance from non-existing node");
    auto GDM = getGDM(Pred);
    insertOrUpdate(Succ, GDM);
  }

  GDMTy &getGDM(NodeTy Node) {
    auto Found = GraphGDM.find(Node);
    assert(Found != GraphGDM.end() && "Requested GDM for non-existing node!");
    return Found->second;
  }

  const StoredItemTy &getOrCreateMatches(NodeTy Node,
                                         internal::MatcherID MatchID) {
    auto GDM = getGDM(Node);
    if (auto *Value = GDM.lookup(MatchID))
      return *Value;

    GDM = Factory.add(GDM, MatchID, StoredItemTy());
    insertOrUpdate(Node, GDM);
    return *GDM.lookup(MatchID);
  }

  const StoredItemTy *getMatches(NodeTy Node, internal::MatcherID MatchID) {
    auto &GDM = getGDM(Node);
    return GDM.lookup(MatchID);
  }

  void addMatches(NodeTy Node, internal::MatcherID MatchID,
                  const ast_matchers::BoundNodes &Nodes) {
    auto Entry = getOrCreateMatches(Node, MatchID);
    assert(!Nodes.getMap().empty());
    for (const auto &Item : Nodes.getMap())
      Entry.addNode(Item.first, Item.second);
    auto NewMap = Factory.add(getGDM(Node), MatchID, Entry);
    insertOrUpdate(Node, NewMap);
  }

  void resetMatches(NodeTy Node, internal::MatcherID MatchID) {
    auto GDM = getGDM(Node);
    GDM = Factory.remove(GDM, MatchID);
    insertOrUpdate(Node, GDM);
  }

  void reset() { GraphGDM = {{nullptr, Factory.getEmptyMap()}}; }

private:
  GDMFactory Factory;
  GraphGDMTy GraphGDM;
};

class GraphMatchFinder {
public:
  class PathMatchCallback {
  public:
    virtual void run(ExprEngine &Eng,
                     const GraphBoundNodesMap::StoredItemTy &BoundNodes,
                     GraphMatchFinder *Finder) = 0;
    virtual ~PathMatchCallback() = default;
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

  // FIXME: entries should be bound to nodes because they can be different
  // for different execution branches. Putting them here was a mistake.
  EntriesTy Entries;
  GraphBoundNodesMap BoundMap;
  std::map<internal::PathSensMatcher *, PathMatchCallback *> PathSensMatchers;
  llvm::SmallPtrSet<internal::PathSensMatcher *, 4> RejectedMatchers;
  ExprEngine *CurrentEngine = nullptr;
  NodeBuilder *CurrentNodeBuilder = nullptr;

  void advanceSingleEntry(size_t &Index, const ExplodedNode *N);
  void tryStartNewMatch(internal::PathSensMatcher *Matcher,
                        PathMatchCallback *Callback, const ExplodedNode *N);

public:
  void match(const Decl *D);
  void match(ExplodedGraph &G, ExprEngine &Eng);
  void addMatcher(const internal::PathSensMatcher &Matcher,
                  PathMatchCallback *Callback) {
    internal::PathSensMatcher *Copy = new internal::PathSensMatcher(Matcher);
    PathSensMatchers[Copy] = Callback;
  }

  void runOfflineChecks(const ExplodedNode *Pred, const ExplodedNode *Succ);
  void runOnlineChecks(ExplodedNode *Pred, ExplodedNode *Succ,
                       ExplodedNodeSet &Dst);
  void advanceWithoutChecking(const ExplodedNode *Pred,
                              const ExplodedNode *Succ) {
    BoundMap.advance(Pred, Succ);
  }

  ASTContext &getASTContext() { return ASTCtx; }
  GraphMatchFinder(ASTContext &ASTCtx) : ASTCtx(ASTCtx) {}

  void reset(ExprEngine *CurrentEngine = nullptr) {
    BoundMap.reset();
    this->CurrentEngine = CurrentEngine;
  }

  NodeBuilder *getNodeBuilder() { return CurrentNodeBuilder; }
  void setNodeBuilder(NodeBuilder *Builder) { CurrentNodeBuilder = Builder; }
  void resetNodeBuilder() { CurrentNodeBuilder = nullptr; }
};

template <typename CalleeTy>
class ProxyMatchCallback : public GraphMatchFinder::PathMatchCallback {
  CalleeTy Callee;

public:
  ProxyMatchCallback(CalleeTy Callee) : Callee(Callee) {}

  virtual void run(ExprEngine &Eng,
                   const GraphBoundNodesMap::StoredItemTy &BoundNodes,
                   GraphMatchFinder *Finder) override {
    Callee(Eng, BoundNodes, Finder);
  }
};

template <typename CalleeTy>
ProxyMatchCallback<CalleeTy> createProxyCallback(CalleeTy Callee) {
  return ProxyMatchCallback<CalleeTy>(Callee);
}

template <typename CalleeTy>
ProxyMatchCallback<CalleeTy> *allocProxyCallback(CalleeTy Callee) {
  return new ProxyMatchCallback<CalleeTy>(Callee);
}

struct MatcherCallbackPair {
  path_matchers::internal::PathSensMatcher Matcher;
  GraphMatchFinder::PathMatchCallback *Callback;
};

} // end namespace path_matchers

} // end namespace ento

} // end namespace clang

#endif // LLVM_CLANG_ENTO_MATCHERS_GRAPHMATCHFINDER_H
