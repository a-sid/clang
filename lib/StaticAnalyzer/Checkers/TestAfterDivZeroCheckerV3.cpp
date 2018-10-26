//== TestAfterDivZeroCheckerV3.cpp - Test after division by zero checker -*-==//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This defines TestAfterDivZeroCheckerV3, a matcher-based builtin check that
// performs checks for division by zero where the division occurs before
// comparison with zero.
//
//===----------------------------------------------------------------------===//

#include "ClangSACheckers.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugReporter.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Matchers/EGraphContext.h"
#include "clang/StaticAnalyzer/Matchers/GraphMatchFinder.h"
#include "clang/StaticAnalyzer/Matchers/GraphMatchers.h"
#include "llvm/ADT/FoldingSet.h"

using namespace clang;
using namespace ento;
using namespace ast_matchers;
using namespace path_matchers;
template <typename T> using Matcher = ast_matchers::internal::Matcher<T>;

namespace {

class DivisionBRVisitorV2 : public BugReporterVisitor {
  const ExplodedNode *DivisionNode;

public:
  DivisionBRVisitorV2(const ExplodedNode *DivisionNode)
      : DivisionNode(DivisionNode) {}

  void Profile(llvm::FoldingSetNodeID &ID) const override {
    ID.AddPointer(DivisionNode);
  }

  virtual std::shared_ptr<PathDiagnosticPiece>
  VisitNode(const ExplodedNode *Succ, const ExplodedNode *Pred,
            BugReporterContext &BRC, BugReport &BR) override {
    if (BRC.getNodeResolver().getOriginalNode(Succ) != DivisionNode)
      return nullptr;

    // Construct a new PathDiagnosticPiece.
    ProgramPoint P = Succ->getLocation();
    PathDiagnosticLocation L =
        PathDiagnosticLocation::create(P, BRC.getSourceManager());

    if (!L.isValid() || !L.asLocation().isValid())
      return nullptr;

    return std::make_shared<PathDiagnosticEventPiece>(
        L, "Division with compared value made here");
  }
};

class TestAfterDivZeroCheckerV3
    : public Checker<check::ASTDecl<TranslationUnitDecl>> {
  mutable std::unique_ptr<BuiltinBug> DivZeroBug;

public:
  void checkASTDecl(const TranslationUnitDecl *TU, AnalysisManager &Mgr,
                    BugReporter &BR) const;
};

AST_MATCHER(DefinedSVal, canBeZero) {
  auto *Context = Finder->getContext<EGraphContext>();
  ConstraintManager &CM = Context->getConstraintManager();
  ProgramStateRef StTrue, StFalse;
  std::tie(StTrue, StFalse) = CM.assumeDual(Context->getState(), Node);
  return StTrue && StFalse;
}

AST_MATCHER(BinaryOperator, isDivisionOp) {
  BinaryOperator::Opcode Op = Node.getOpcode();
  return Op == BO_Div || Op == BO_Rem || Op == BO_DivAssign ||
         Op == BO_RemAssign;
}

AST_MATCHER(BinaryOperator, isComparisonOp) { return Node.isComparisonOp(); }

/// \brief Matches if either the left hand side or the right hand side of a
/// binary operator matches.
inline Matcher<BinaryOperator> hasBothOperands(const Matcher<Expr> &Matcher1,
                                               const Matcher<Expr> &Matcher2) {
  return anyOf(allOf(hasLHS(Matcher1), hasRHS(Matcher2)),
               allOf(hasLHS(Matcher2), hasRHS(Matcher1)));
}
} // namespace

void TestAfterDivZeroCheckerV3::checkASTDecl(const TranslationUnitDecl *TU,
                                             AnalysisManager &Mgr,
                                             BugReporter &BR) const {
  auto *Callback = allocProxyCallback(
        [this](ExprEngine &Eng,
               const GraphBoundNodesMap::StoredItemTy &BoundNodes,
               GraphMatchFinder *Finder) {
    if (!DivZeroBug)
      DivZeroBug.reset(new BuiltinBug(this, "Division by zero"));

    const ExplodedNode *CompNode =
                           BoundNodes.getNodeAs<ExplodedNode>("comp_node"),
                       *DivNode =
                           BoundNodes.getNodeAs<ExplodedNode>("div_node");
    assert(CompNode && DivNode);
    Finder->getNodeBuilder()->generateSink(
        CompNode->getLocation(), CompNode->getState(),
        const_cast<ExplodedNode *>(CompNode));

    auto R = llvm::make_unique<BugReport>(
        *DivZeroBug,
        "Value being compared against zero has already been used for division",
        CompNode);
    Eng.getBugReporter().emitReport(std::move(R));
  });

  Mgr.getCheckerManager()->registerPathMatcher(
      {hasSequence(
           explodedNode(
               postStmt(hasStatement(
                   binaryOperator(
                       isDivisionOp(),
                       hasRHS(hasValue(definedSVal(canBeZero()).bind("value"))))
                       .bind("div_binop"))),
               hasStackFrame(stackFrameContext().bind("loc_ctx")))
               .bind("div_node"),
           unless(callExitEnd(hasCalleeContext(equalsBoundNode("loc_ctx")))),
           explodedNode(
               postCondition(hasStatement(allOf(
                   anyOf(
                       binaryOperator(
                           isComparisonOp(),
                           hasBothOperands(
                               ignoringParenImpCasts(integerLiteral(equals(0))),
                               expr(hasValue(equalsBoundNode("value"))))),
                       unaryOperator(
                           hasOperatorName("!"),
                           hasUnaryOperand(anyOf(
                               hasValue(equalsBoundNode("value")),
                               implicitCastExpr(hasSourceExpression(
                                   hasValue(equalsBoundNode("value"))))))),
                       implicitCastExpr(
                           anyOf(hasValue(equalsBoundNode("value")),
                                 hasSourceExpression(
                                     hasValue(equalsBoundNode("value")))))),
                   postDominatesBoundLocal("div_binop")))))
               .bind("comp_node")),
       Callback},
      BR.getContext());
}

void ento::registerTestAfterDivZeroCheckerV3(CheckerManager &mgr) {
  mgr.registerChecker<TestAfterDivZeroCheckerV3>();
}
