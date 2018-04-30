//===--- EGraphContext.h ----------------------------------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  Provides an accessor to the path-sensitive engine for ASTMatchFinder.
//  Matchers that require some state information or access to helper classes
//  responsible for path-sensitive analysis can use this class.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_ENTO_MATCHERS_EGRAPHCONTEXT_H
#define LLVM_CLANG_ENTO_MATCHERS_EGRAPHCONTEXT_H

#include "clang/ASTMatchers/MatchFinderContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ExplodedGraph.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/MemRegion.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramState_Fwd.h"
#include "clang/StaticAnalyzer/Matchers/GraphMatcherInternals.h"

namespace llvm {

class raw_ostream;
}

namespace clang {

namespace ento {

class EGraphContext : public ast_matchers::internal::MatchFinderContext {
public:
  EGraphContext(path_matchers::internal::GraphBoundNodesTreeBuilder &Builder,
                const ExplodedNode *CurrentNode)
      : CurrentNode(CurrentNode), State(CurrentNode->getState()),
        StateMgr(CurrentNode->getState()->getStateManager()), Builder(Builder) {
    assert(CurrentNode &&
           "Cannot use ExplodedGraph node accessors without a node!");
    assert(State && "ExplodedNode cannot have null State!");
  }

  static void *getTag() {
    static int X = 0;
    return &X;
  }

  const ExplodedNode *getCurrentNode() { return CurrentNode; }
  ProgramStateRef getState() { return State; }
  ProgramPoint getProgramPoint() { return CurrentNode->getLocation(); }

  const LocationContext *getLocationContext() {
    return CurrentNode->getLocationContext();
  }

  const StackFrameContext *getStackFrameContext() {
    return CurrentNode->getStackFrame();
  }

  SVal getSVal(const Stmt *S) {
    return State->getSVal(S, getLocationContext());
  }

  ProgramStateManager &getStateManager() { return StateMgr; }

  ConstraintManager &getConstraintManager() {
    return State->getConstraintManager();
  }

  const MemRegionManager &getRegionManager() {
    return StateMgr.getRegionManager();
  }

  StoreManager &getStoreManager() { return StateMgr.getStoreManager(); }

  SValBuilder &getSValBuilder() { return StateMgr.getSValBuilder(); }

  virtual ast_graph_type_traits::DynTypedNode
  getBoundNode(StringRef ID) override;

private:
  const ExplodedNode *CurrentNode;
  ProgramStateRef State;
  ProgramStateManager &StateMgr;
  path_matchers::internal::GraphBoundNodesTreeBuilder &Builder;
};
} // end namespace ento
} // end namepace clang

#endif // LLVM_CLANG_ENTO_MATCHERS_EGRAPHCONTEXT_H
