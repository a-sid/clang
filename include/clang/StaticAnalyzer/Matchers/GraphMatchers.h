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
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Analysis/Analyses/Dominators.h"
#include "clang/Analysis/CFGStmtMap.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramStateTrait.h"
#include "clang/StaticAnalyzer/Matchers/EGraphContext.h"
#include "clang/StaticAnalyzer/Matchers/GraphMatchFinder.h"

#include "llvm/ADT/StringMap.h"

namespace clang {

namespace ento {

namespace path_matchers {

// template <typename NodeTy>
const internal::VariadicOperatorPathMatcherFunc<
    internal::SequenceVariadicOperator, 1, std::numeric_limits<unsigned>::max()>
    hasSequence;

inline internal::PathSensMatcher
achievesCountOnPath(ast_matchers::internal::DynTypedMatcher StartMatcher,
                    ast_matchers::internal::DynTypedMatcher IncrementMatcher,
                    ast_matchers::internal::DynTypedMatcher DecrementMatcher,
                    ssize_t InitialCounter, ssize_t MatchCounter,
                    ssize_t LowerBound = std::numeric_limits<ssize_t>::min(),
                    ssize_t UpperBound = std::numeric_limits<ssize_t>::max()) {
  return internal::PathSensMatcher(internal::DynTypedPathMatcher(
      new internal::CountingPathMatcher(StartMatcher, IncrementMatcher,
                                        DecrementMatcher, InitialCounter,
                                        MatchCounter, LowerBound, UpperBound)));
}

using ExplodedNodeMatcher = ast_matchers::internal::Matcher<ExplodedNode>;

extern const ast_matchers::internal::VariadicAllOfMatcher<ExplodedNode>
    explodedNode;

extern const ast_matchers::internal::VariadicDynCastAllOfMatcher<SVal,
                                                                 DefinedSVal>
    definedSVal;

extern const ast_matchers::internal::VariadicAllOfMatcher<MemRegion> memRegion;

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

struct CFGBlockFromFinder {
  const CFGBlock *BoundBlock;
  const Stmt *BoundStmt;
  const CFGBlock *NodeBlock;
  AnalysisDeclContext *ADC;

  static Optional<CFGBlockFromFinder>
  extract(::clang::ast_matchers::internal::ASTMatchFinder *Finder,
          const std::string &ID, const Stmt *Node) {
    EGraphContext *Context = Finder->getContext<EGraphContext>();
    auto Found = Context->getBoundNode(ID);
    const Stmt *Bound = Found.get<Stmt>();
    if (!Bound)
      return None;

    // FIXME: Finder can already have a memoization data for parents, reuse it.
    ASTContext &ASTCtx = Finder->getASTContext();
    const Decl *NodeParentFunc = internal::getParentFunction(ASTCtx, Node),
               *BoundParentFunc = internal::getParentFunction(ASTCtx, Bound);
    if (NodeParentFunc != BoundParentFunc)
      return None;

    auto *ADC = Context->getAnalysisDeclContext(NodeParentFunc);
    if (!ADC)
      return None;

    CFG *Cfg = ADC->getCFG();
    if (!Cfg)
      return None;

    CFGStmtMap *CSMap = ADC->getCFGStmtMap();
    assert(CSMap && "Can only be null if CFG is nullptr!");

    const CFGBlock *NodeBlock = CSMap->getBlock(Node),
                   *BoundBlock = CSMap->getBlock(Bound);
    return CFGBlockFromFinder{BoundBlock, Bound, NodeBlock, ADC};
  }
};

AST_MATCHER_P(Stmt, postDominatesBoundLocal, std::string, ID) {
  auto ExtractedCFG = CFGBlockFromFinder::extract(Finder, ID, &Node);
  if (!ExtractedCFG)
    return false;

  const CFGBlock *BoundBlock = ExtractedCFG->BoundBlock,
                 *NodeBlock = ExtractedCFG->NodeBlock;
  AnalysisDeclContext *ADC = ExtractedCFG->ADC;
  const Stmt *Bound = ExtractedCFG->BoundStmt;

  if (NodeBlock == BoundBlock)
    return internal::getCFGBlockIndex(*NodeBlock, &Node) >=
           internal::getCFGBlockIndex(*NodeBlock, Bound);

  DominatorTree</* IsPostDom= */true> Dom;
  Dom.buildDominatorTree(*ADC);
  return Dom.dominates(NodeBlock, BoundBlock);
}

AST_MATCHER_P(Stmt, isDominatedByBoundLocal, std::string, ID) {
  auto ExtractedCFG = CFGBlockFromFinder::extract(Finder, ID, &Node);
  if (!ExtractedCFG)
    return false;

  const CFGBlock *BoundBlock = ExtractedCFG->BoundBlock,
                 *NodeBlock = ExtractedCFG->NodeBlock;
  AnalysisDeclContext *ADC = ExtractedCFG->ADC;
  const Stmt *Bound = ExtractedCFG->BoundStmt;

  if (NodeBlock == BoundBlock)
    return internal::getCFGBlockIndex(*NodeBlock, &Node) >=
           internal::getCFGBlockIndex(*NodeBlock, Bound);

  DominatorTree</* IsPostDom= */false> Dom;
  Dom.buildDominatorTree(*ADC);
  return Dom.dominates(BoundBlock, NodeBlock);
}
} // end namespace path_matchers

} // namespace ento

} // namespace clang

#endif // LLVM_CLANG_ENTO_MATCHERS_GRAPHMATCHERS_H
