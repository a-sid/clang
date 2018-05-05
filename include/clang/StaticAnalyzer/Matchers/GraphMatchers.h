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
#include "clang/StaticAnalyzer/Matchers/GraphMatcherInternals.h"

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

extern const ast_matchers::internal::VariadicDynCastAllOfMatcher<SVal,
                                                                 DefinedSVal>
    definedSVal;

extern const ast_matchers::internal::VariadicDynCastAllOfMatcher<MemRegion,
                                                                 StringRegion>
    stringRegion;

extern const ast_matchers::internal::VariadicAllOfMatcher<LocationContext>
    locationContext;

extern const ast_matchers::internal::VariadicDynCastAllOfMatcher<
    LocationContext, StackFrameContext>
    stackFrameContext;

extern const ast_matchers::internal::VariadicAllOfMatcher<ProgramPoint>
    programPoint;

extern const ast_matchers::internal::VariadicDynCastAllOfMatcher<ProgramPoint,
                                                                 PreStmt>
    preStmt;

extern const ast_matchers::internal::VariadicDynCastAllOfMatcher<ProgramPoint,
                                                                 PostStmt>
    postStmt;

extern const ast_matchers::internal::VariadicDynCastAllOfMatcher<ProgramPoint,
                                                                 BlockEdge>
    blockEdge;

extern const ast_matchers::internal::VariadicDynCastAllOfMatcher<ProgramPoint,
                                                                 PostCondition>
    postCondition;

extern const ast_matchers::internal::VariadicDynCastAllOfMatcher<ProgramPoint,
                                                                 StmtPoint>
    stmtPoint;

extern const ast_matchers::internal::VariadicDynCastAllOfMatcher<ProgramPoint,
                                                                 CallEnter>
    callEnter;

extern const ast_matchers::internal::VariadicDynCastAllOfMatcher<ProgramPoint,
                                                                 CallExitEnd>
    callExitEnd;

AST_MATCHER_P(StmtPoint, hasStatement, ast_matchers::StatementMatcher, Inner) {
  return Inner.matches(*Node.getStmt(), Finder, Builder);
}

AST_MATCHER_P(ExplodedNode, hasProgramPoint,
              ast_matchers::internal::Matcher<ProgramPoint>, Inner) {
  return Inner.matches(Node.getLocation(), Finder, Builder);
}

AST_MATCHER_P(CallEnter, hasCallExpr, ast_matchers::StatementMatcher, Inner) {
  const Stmt *CE = Node.getCallExpr();
  return CE ? Inner.matches(*CE, Finder, Builder) : false;
}

AST_POLYMORPHIC_MATCHER_P(hasLocationContext,
                          AST_POLYMORPHIC_SUPPORTED_TYPES(ExplodedNode,
                                                          ProgramPoint),
                          ast_matchers::internal::Matcher<LocationContext>,
                          Inner) {
  return Inner.matches(*Node.getLocationContext(), Finder, Builder);
}

AST_MATCHER_P(ExplodedNode, hasStackFrame,
              ast_matchers::internal::Matcher<StackFrameContext>, Inner) {
  return Inner.matches(*Node.getStackFrame(), Finder, Builder);
}

AST_MATCHER_P(LocationContext, isParentOfBound, std::string, ID) {
  EGraphContext *Context = Finder->getContext<EGraphContext>();
  auto Found = Context->getBoundNode(ID);
  if (const auto *LCtx = Found.get<LocationContext>())
    return Node.isParentOf(LCtx);
  return false;
}

AST_MATCHER_P(LocationContext, isAncestorOfBound, std::string, ID) {
  EGraphContext *Context = Finder->getContext<EGraphContext>();
  auto Found = Context->getBoundNode(ID);
  if (const auto *LCtx = Found.get<LocationContext>())
    return LCtx->isParentOf(&Node);
  return false;
}

AST_MATCHER_P(LocationContext, hasCallee, ast_matchers::internal::Matcher<Decl>,
              Inner) {
  return Node.getDecl() && Inner.matches(*Node.getDecl(), Finder, Builder);
}

AST_MATCHER_P(CallExitEnd, hasCalleeContext,
              ast_matchers::internal::Matcher<StackFrameContext>, Inner) {
  return Inner.matches(*Node.getCalleeContext(), Finder, Builder);
}

AST_MATCHER_P(Stmt, hasValue, ast_matchers::internal::Matcher<SVal>, Inner) {
  EGraphContext *Context = Finder->getContext<EGraphContext>();
  SVal Res = Context->getSVal(&Node);
  return Inner.matches(Res, Finder, Builder);
}

AST_MATCHER_P(StringRegion, refersString, std::string, String) {
  return Node.getStringLiteral()->getString() == String;
}

} // end namespace path_matchers

} // end namespace ento

} // end namespace clang

#endif // LLVM_CLANG_ENTO_MATCHERS_GRAPHMATCHERS_H
