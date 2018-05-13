//===- ChrootCheckerV2.cpp ------ Basic security checks ---------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  This file defines chroot checker, which checks improper use of chroot.
//  This version of the checker is based on path-sensitive AST Matchers and uses
//  traversal on the ExplodedGraph.
//
//===----------------------------------------------------------------------===//

#include "ClangSACheckers.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugReporter.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Matchers/GraphMatchFinder.h"

using namespace clang;
using namespace ento;
using namespace ast_matchers;
using namespace path_matchers;

namespace {
class ChrootCheckerV2 : public Checker<check::EndAnalysis> {
  mutable std::unique_ptr<BuiltinBug> BT_BreakJail;

public:
  void checkEndAnalysis(ExplodedGraph &G, BugReporter &BR,
                        ExprEngine &Eng) const;
};
} // end anonymous namespace

void ChrootCheckerV2::checkEndAnalysis(ExplodedGraph &G, BugReporter &BR,
                                       ExprEngine &Eng) const {
  path_matchers::GraphMatchFinder Finder(BR.getContext());
  auto Callback = createProxyCallback(
      [&BR, this](const GraphBoundNodesMap::StoredItemTy &BoundNodes) {
        const ExplodedNode *N = BoundNodes.getNodeAs<ExplodedNode>("bug_node");
        if (!BT_BreakJail)
          BT_BreakJail.reset(new BuiltinBug(
              this, "Break out of jail",
              "No call of chdir(\"/\") immediately after chroot"));
        BR.emitReport(llvm::make_unique<BugReport>(
            *BT_BreakJail, BT_BreakJail->getDescription(), N));
      });

  StatementMatcher NotChdir =
      callExpr(unless(callee(functionDecl(hasName("::chdir")))));
  Finder.addMatcher(
      hasSequence(
          postStmt(hasStatement(
              callExpr(callee(functionDecl(hasName("::chroot")))))),
          unless(stmtPoint(hasStatement(callExpr(
              callee(functionDecl(hasName("::chdir"))),
              hasArgument(0, hasValue(stringRegion(refersString("/")))))))),
          explodedNode(anyOf(postStmt(hasStatement(NotChdir)),
                             callEnter(hasCallExpr(NotChdir))))
              .bind("bug_node")),
      &Callback);
  Finder.match(G);
}

void ento::registerChrootCheckerV2(CheckerManager &Mgr) {
  Mgr.registerChecker<ChrootCheckerV2>();
}
