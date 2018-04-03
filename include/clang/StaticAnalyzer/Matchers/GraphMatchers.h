//===- GraphMatchers.h - Structural query framework -------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  Implements the base layer of the path matcher framework.
//
//  The way how path-sensitive matchers work is very similar to AST matchers,
//  with one difference: their matches() method also takes a parameter
//  identifying the current state.
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_ENTO_MATCHERS_GRAPHMATCHERS_H
#define LLVM_CLANG_ENTO_MATCHERS_GRAPHMATCHERS_H

#include "clang/ASTMatchers/ASTGraphTypeTraits.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramStateTrait.h"
#include "clang/StaticAnalyzer/Matchers/EGraphContext.h"
#include "clang/StaticAnalyzer/Matchers/PathMatcherInternals.h"

#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "llvm/ADT/StringMap.h"

namespace clang {

namespace ento {

namespace path_matchers {

class PSMatchesCallback : public ast_matchers::MatchFinder::MatchCallback {
public:
  void run(const ast_matchers::MatchFinder::MatchResult &Result) override {
    Nodes.push_back(Result.Nodes);
    HasMatches = true;
  }
  SmallVector<ast_matchers::BoundNodes, 1> Nodes;
  bool HasMatches = false;
};

// template <typename NodeTy>
const internal::VariadicOperatorPathMatcherFunc<
    internal::SequenceVariadicOperator, 1, std::numeric_limits<unsigned>::max()>
    hasSequence;

using ExplodedNodeMatcher = ast_matchers::internal::Matcher<ExplodedNode>;

extern const ast_matchers::internal::VariadicAllOfMatcher<ExplodedNode>
    explodedNode;

extern const ast_matchers::internal::VariadicDynCastAllOfMatcher<MemRegion,
                                                                 StringRegion>
    stringRegion;

AST_MATCHER_P(ExplodedNode, statementNode, ast_matchers::StatementMatcher,
              Inner) {
  if (auto StmtPP = Node.getLocationAs<StmtPoint>())
    return Inner.matches(*StmtPP->getStmt(), Finder, Builder);
  return false;
}

#define PROGRAM_POINT_MATCHER(Type, Name)                                      \
  AST_MATCHER_P(ExplodedNode, Name, ExplodedNodeMatcher, Inner) {              \
    if (auto PP = Node.getLocationAs<Type>())                                  \
      return Inner.matches(Node, Finder, Builder);                             \
    return false;                                                              \
  }

PROGRAM_POINT_MATCHER(PreStmt, preStmtNode)
PROGRAM_POINT_MATCHER(PostStmt, postStmtNode)

#undef PROGRAM_POINT_MATCHER

AST_MATCHER_P(ExplodedNode, callEnterNode, ast_matchers::StatementMatcher,
              Inner) {
  if (auto CallEnterPP = Node.getLocationAs<CallEnter>())
    if (const Stmt *CE = CallEnterPP->getCallExpr())
      return Inner.matches(*CE, Finder, Builder);
  return false;
}

AST_MATCHER_P(Stmt, hasValue, ast_matchers::internal::Matcher<SVal>, Inner) {
  EGraphContext *Context = Finder->getContext<EGraphContext>();
  ProgramStateRef State = Context->getState();
  SVal Res = State->getSVal(&Node, Context->getLocationContext());
  return Inner.matches(Res, Finder, Builder);
}

AST_MATCHER_P(StringRegion, refersString, std::string, String) {
  return Node.getStringLiteral()->getString() == String;
}

} // end namespace path_matchers

} // end namespace ento

} // end namespace clang

#endif // LLVM_CLANG_ENTO_MATCHERS_GRAPHMATCHERS_H
