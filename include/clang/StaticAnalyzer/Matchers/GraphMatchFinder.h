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

class GraphMatchFinder {
  ASTContext &ASTCtx;
  std::vector<internal::BindEntry<ExplodedNode>> Entries;
  internal::GraphBoundNodesTreeBuilder Builder;
  internal::GraphBoundNodeMap BoundMap;
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
