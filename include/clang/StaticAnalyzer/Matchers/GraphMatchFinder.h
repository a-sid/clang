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

template <typename ImmutableTy> class MapOnImmutableType {
  template <typename StoredTy> struct ImmutableTraits {};

  template <typename KeyTy, typename ValueTy>
  struct ImmutableTraits<llvm::ImmutableMap<KeyTy, ValueTy>> {
    static llvm::ImmutableMap<KeyTy, ValueTy>
    getEmpty(typename llvm::ImmutableMap<KeyTy, ValueTy>::Factory &F) {
      return F.getEmptyMap();
    }
  };

  template <typename StoredTy>
  struct ImmutableTraits<llvm::ImmutableSet<StoredTy>> {
    static llvm::ImmutableSet<StoredTy>
    getEmpty(typename llvm::ImmutableSet<StoredTy>::Factory &F) {
      return F.getEmptySet();
    }
  };

  using Factory = typename ImmutableTy::Factory;
  using NodeTy = const ExplodedNode *;
  using MapTy = std::map<NodeTy, ImmutableTy>;

  Factory F;
  MapTy Map;

public:
  ImmutableTy *lookupEntry(NodeTy Node) {
    auto Found = Map.find(Node);
    return Found != Map.end() ? &Found->second : nullptr;
  }

  ImmutableTy getOrCreateEntry(NodeTy Node) {
    auto *Found = lookupEntry(Node);
    if (Found)
      return *Found;
    return ImmutableTraits<ImmutableTy>::getEmpty(F);
  }

  void insertOrUpdate(NodeTy Node, ImmutableTy NewStored) {
    auto Found = Map.insert({Node, NewStored});
    if (!Found.second)
      Found.first->second = NewStored;
  }

  template <typename KeyTy>
  bool contains(NodeTy Node, const KeyTy &Key) const {
    auto Found = Map.find(Node);
    return Found != Map.end() && Found->second.contains(Key);
  }

  template <typename... Ts> void addEntry(NodeTy Node, Ts &&... KeyValue) {
    auto CurrSet = getOrCreateEntry(Node);
    auto NewSet = F.add(CurrSet, std::forward<Ts>(KeyValue)...);
    insertOrUpdate(Node, NewSet);
  }

  template <typename KeyTy> void removeEntry(NodeTy Node, const KeyTy &Key) {
    auto CurrSet = getOrCreateEntry(Node);
    auto NewSet = F.remove(CurrSet, Key);
    insertOrUpdate(Node, NewSet);
  }

  void advance(NodeTy From, NodeTy To) {
    assert(Map.find(From) != Map.end() &&
           "Cannot advance from non-existing node");
    auto Set = getOrCreateEntry(From);
    Map.insert({To, Set});
  }

  void reset() { Map = {{nullptr, ImmutableTraits<ImmutableTy>::getEmpty(F)}}; }
};

// template <typename NodeTy>
class GraphBoundNodesMap {
public:
  using NodeTy = const ExplodedNode *;
  using StoredItemTy = ast_matchers::internal::BoundNodesMap;
  using GDMTy = llvm::ImmutableMap<internal::MatcherID, StoredItemTy>;

  GraphBoundNodesMap() { Impl.reset(); }

  void advance(NodeTy Pred, NodeTy Succ) { Impl.advance(Pred, Succ); }

  GDMTy getGDM(NodeTy Node) {
    auto *Found = Impl.lookupEntry(Node);
    assert(Found && "Requested GDM for non-existing node!");
    return *Found;
  }

  StoredItemTy getOrCreateMatches(NodeTy Node, internal::MatcherID MatchID) {
    auto GDM = Impl.getOrCreateEntry(Node);
    if (auto *Value = GDM.lookup(MatchID))
      return *Value;
    return StoredItemTy();
  }

  const StoredItemTy *getMatches(NodeTy Node, internal::MatcherID MatchID) {
    auto GDM = getGDM(Node);
    return GDM.lookup(MatchID);
  }

  void addMatches(NodeTy Node, internal::MatcherID MatchID,
                  const ast_matchers::BoundNodes &Nodes) {
    auto Entry = getOrCreateMatches(Node, MatchID);
    assert(!Nodes.getMap().empty());
    for (const auto &Item : Nodes.getMap())
      Entry.addNode(Item.first, Item.second);
    Impl.addEntry(Node, MatchID, Entry);
  }

  void resetMatches(NodeTy Node, internal::MatcherID MatchID) {
    Impl.removeEntry(Node, MatchID);
  }

  void reset() { Impl.reset(); }

private:
  MapOnImmutableType<GDMTy> Impl;
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

  class EntryMap {
    using NodeTy = const ExplodedNode *;
    using EntryNodeSetTy = llvm::ImmutableSet<EntryTy>;
    using EntriesTy = MapOnImmutableType<EntryNodeSetTy>;

    EntriesTy Impl;
    internal::MatcherID MatchCounter = 0;

  public:
    void advance(NodeTy From, NodeTy To) {
      Impl.advance(From, To);
    }

    internal::MatcherID addMatch(NodeTy Node,
                                 internal::PathSensMatcher *Matcher,
                                 internal::MatcherStateID StateID) {
      Impl.addEntry(Node, EntryTy{Matcher, StateID, MatchCounter});
      return MatchCounter++;
    }

    EntryNodeSetTy getEntries(NodeTy Node) {
      return Impl.getOrCreateEntry(Node);
    }

    void removeEntry(NodeTy Node, const EntryTy &Entry) {
      Impl.removeEntry(Node, Entry);
    }

    void replaceEntry(NodeTy Node, const EntryTy &OldEntry,
                      const EntryTy &NewEntry) {
      Impl.removeEntry(Node, OldEntry);
      Impl.addEntry(Node, NewEntry);
    }

    void reset() { Impl.reset(); }
  };

  class RejectedMatchersMap {
    using RejMatchersTy = llvm::ImmutableSet<const internal::PathSensMatcher *>;
    using NodeTy = const ExplodedNode *;

    MapOnImmutableType<RejMatchersTy> Impl;

  public:
    bool isRejectedForever(NodeTy Node,
                           const internal::PathSensMatcher *Matcher) const {
      return Impl.contains(Node, Matcher);
    }

    void rejectMatcher(NodeTy Node, const internal::PathSensMatcher *Matcher) {
      Impl.addEntry(Node, Matcher);
    }

    void advance(NodeTy From, NodeTy To) { Impl.advance(From, To); }

    void reset() { Impl.reset(); }
  };

  ASTContext &ASTCtx;

  EntryMap Entries;
  GraphBoundNodesMap BoundMap;
  // FIXME: Replace with a DenseMap.
  std::map<internal::PathSensMatcher *, PathMatchCallback *> PathSensMatchers;
  RejectedMatchersMap RejectedMatchers;
  ExprEngine *CurrentEngine = nullptr;
  NodeBuilder *CurrentNodeBuilder = nullptr;

  void advanceSingleEntry(const EntryTy &Entry, const ExplodedNode *N);
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
    RejectedMatchers.advance(Pred, Succ);
    Entries.advance(Pred, Succ);
  }

  ASTContext &getASTContext() { return ASTCtx; }
  GraphMatchFinder(ASTContext &ASTCtx) : ASTCtx(ASTCtx) {}

  void reset(ExprEngine *CurrentEngine = nullptr) {
    BoundMap.reset();
    RejectedMatchers.reset();
    Entries.reset();
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
