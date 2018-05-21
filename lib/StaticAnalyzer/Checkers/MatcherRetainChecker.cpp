//== MatcherRetainChecker.cpp - Test after division by zero checker -*-==//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This defines MatcherRetainChecker, a matcher-based builtin check that
// performs checks for division by zero where the division occurs before
// comparison with zero.
//
//===----------------------------------------------------------------------===//

#include "ClangSACheckers.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugReporter.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Matchers/GraphMatchFinder.h"

using namespace clang;
using namespace ento;
using namespace ast_matchers;
using namespace path_matchers;

namespace {

class MatcherRetainChecker : public Checker<check::EndAnalysis> {
  mutable std::unique_ptr<BuiltinBug> RetainBug;

public:
  void checkEndAnalysis(ExplodedGraph &G, BugReporter &BR,
                        ExprEngine &Eng) const;
};
} // namespace

void MatcherRetainChecker::checkEndAnalysis(ExplodedGraph &G, BugReporter &BR,
                                            ExprEngine &Eng) const {
  path_matchers::GraphMatchFinder Finder(BR.getContext());
  auto Callback = createProxyCallback(
      [&BR, this](const GraphBoundNodesMap::StoredItemTy &BoundNodes) {
        if (!RetainBug)
          RetainBug.reset(new BuiltinBug(this, "Too many releases"));

        const ExplodedNode *LastReleaseNode =
            BoundNodes.getNodeAs<ExplodedNode>("last_release");
        auto R = llvm::make_unique<BugReport>(
            *RetainBug, "Number of releases is greater than number of retains",
            LastReleaseNode);
        BR.emitReport(std::move(R));
      });

  Finder.addMatcher(
      achievesCountOnPath(
          // FIXME: There is a weird situation where same statement is matched
          // by both increment and start matchers. So, we advance and existing
          // match and add a new one immediately.
          postStmt(hasStatement(cxxMemberCallExpr(
              callee(functionDecl(hasName("startCounting"))),
              on(expr(hasValue(memRegion().bind("object"))))))),
          postStmt(hasStatement(cxxMemberCallExpr(
              callee(functionDecl(hasName("retain"))),
              on(expr(hasValue(memRegion(equalsBoundNode("object")))))))),
          explodedNode(
              postStmt(hasStatement(cxxMemberCallExpr(
                  callee(functionDecl(hasName("release"))),
                  on(expr(hasValue(memRegion(equalsBoundNode("object")))))))))
              .bind("last_release"),
          1, 0),
      &Callback);
  Finder.match(G);
}

void ento::registerMatcherRetainChecker(CheckerManager &mgr) {
  mgr.registerChecker<MatcherRetainChecker>();
}
