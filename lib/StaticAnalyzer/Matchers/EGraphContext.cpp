//===--- EGraphContext.cpp --------------------------------------*- C++ -*-===//
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

#include "clang/StaticAnalyzer/Matchers/EGraphContext.h"
#include "clang/Analysis/AnalysisDeclContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/AnalysisManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramState.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/SubEngine.h"

using namespace clang;
using namespace clang::ento;

ast_graph_type_traits::DynTypedNode
EGraphContext::getBoundNode(llvm::StringRef ID) {
  return Builder.getBoundNode(ID);
}

AnalysisManager &EGraphContext::getAnalysisManager() {
  return StateMgr.getOwningEngine()->getAnalysisManager();
}

AnalysisDeclContext *EGraphContext::getAnalysisDeclContext(const Decl *D) {
  return getAnalysisManager().getAnalysisDeclContext(D);
}
