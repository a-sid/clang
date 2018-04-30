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
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramStateTrait.h"
#include "clang/StaticAnalyzer/Matchers/EGraphContext.h"
#include "clang/StaticAnalyzer/Matchers/GraphMatchFinder.h"

#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

using namespace clang;
using namespace ento;
using namespace llvm;
using namespace ast_matchers;
using namespace path_matchers;

namespace {

////////////////////////////////////////////////////////////////////////////////


/*
AST_MATCHER_P(FunctionDecl, isReachable,
              ast_matchers::internal::VariadicOperatorMatcherFunc<
              2, std::numeric_limits<unsigned>::max()> InnerMatcher) {
  InnerMatcher.
}

auto LockMatcher =
    isReachable(
      stmt(
        callExpr(
          hasDeclaration(
            functionDecl(hasName("pthread_mutex_lock"))),
          hasArgValue(0,
                      value(isKnown(),
                            ).bind("mutex")))),
      unless(
        stmt(
          callExpr(
            hasDeclaration(
              functionDecl(hasName("pthread_mutex_unlock"))),
            hasArgValue(0, equalsBoundNode("mutex"))))),
      stmt(
        callExpr(
          hasDeclaration(
            functionDecl(hasName("pthread_mutex_lock"))),
          hasArgValue(0,equalsBoundNode("mutex")))));
*/
class ChrootCheckerV2 : public Checker<check::EndAnalysis> {

public:
  void checkEndAnalysis(ExplodedGraph &G, BugReporter &BR,
                        ExprEngine &Eng) const;
};
} // end anonymous namespace


void ChrootCheckerV2::checkEndAnalysis(ExplodedGraph &G, BugReporter &BR,
                                       ExprEngine &Eng) const {
  ExplodedNode *Root = *G.roots_begin();
  const Decl *D = Root->getStackFrame()->getDecl();
  std::string FuncName;
  if (const NamedDecl *FD = dyn_cast<NamedDecl>(D))
    FuncName = FD->getQualifiedNameAsString();

  path_matchers::GraphMatchFinder Finder(BR.getContext());
  auto Callback = path_matchers::internal::createProxyCallback(
      [&FuncName]() -> void { llvm::errs() << FuncName << " matches!\n"; });

  StatementMatcher NotChdir =
      callExpr(unless(callee(functionDecl(hasName("::chdir")))));
  Finder.addMatcher(
      hasSequence(
          postStmtNode(statementNode(
              callExpr(callee(functionDecl(hasName("::chroot")))))),
          unless(statementNode(callExpr(
              callee(functionDecl(hasName("::chdir"))),
              hasArgument(0, hasValue(stringRegion(refersString("/"))))))),
          explodedNode(anyOf(postStmtNode(statementNode(NotChdir)),
                             callEnterNode(NotChdir)))),
      &Callback);
  Finder.match(G, BR, Eng);
}

void ento::registerChrootCheckerV2(CheckerManager &Mgr) {
  Mgr.registerChecker<ChrootCheckerV2>();
}
