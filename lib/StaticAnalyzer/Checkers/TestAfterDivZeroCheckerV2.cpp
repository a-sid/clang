//== TestAfterDivZeroCheckerV2.cpp - Test after division by zero checker -*-==//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This defines TestAfterDivZeroCheckerV2, a matcher-based builtin check that
// performs checks for division by zero where the division occurs before
// comparison with zero.
// TODO: Support CFG-based analysis.
//
//===----------------------------------------------------------------------===//

#include "ClangSACheckers.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Matchers/EGraphContext.h"
#include "clang/StaticAnalyzer/Matchers/GraphMatchFinder.h"
#include "llvm/ADT/FoldingSet.h"

using namespace clang;
using namespace ento;
using namespace ast_matchers;
using namespace path_matchers;
template <typename T> using Matcher = ast_matchers::internal::Matcher<T>;

namespace {

class DivisionBRVisitorV2 : public BugReporterVisitorImpl<DivisionBRVisitorV2> {
  const ExplodedNode *DivisionNode;

public:
  DivisionBRVisitorV2(const ExplodedNode *DivisionNode)
      : DivisionNode(DivisionNode) {}

  void Profile(llvm::FoldingSetNodeID &ID) const override {
    ID.AddPointer(DivisionNode);
  }

  virtual std::shared_ptr<PathDiagnosticPiece>
  VisitNode(const ExplodedNode *Succ, const ExplodedNode *Pred,
            BugReporterContext &BRC, BugReport &BR) override;
};

class TestAfterDivZeroCheckerV2 : public Checker<check::EndAnalysis> {
  mutable std::unique_ptr<BuiltinBug> DivZeroBug;

public:
  void checkEndAnalysis(ExplodedGraph &G, BugReporter &BR,
                        ExprEngine &Eng) const;
};
} // end anonymous namespace

std::shared_ptr<PathDiagnosticPiece>
DivisionBRVisitorV2::VisitNode(const ExplodedNode *Succ,
                               const ExplodedNode *Pred,
                               BugReporterContext &BRC, BugReport &BR) {

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

namespace {
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

void TestAfterDivZeroCheckerV2::checkEndAnalysis(ExplodedGraph &G,
                                                 BugReporter &BR,
                                                 ExprEngine &Eng) const {
  ExplodedNode *Root = *G.roots_begin();
  const Decl *D = Root->getStackFrame()->getDecl();
  std::string FuncName;
  if (const NamedDecl *FD = dyn_cast<NamedDecl>(D))
    FuncName = FD->getQualifiedNameAsString();

  path_matchers::GraphMatchFinder Finder(BR.getContext());
  auto Callback = createProxyCallback(
        [&BR, this](const GraphBoundNodesMap::StoredItemTy &BoundNodes) {
    if (!DivZeroBug)
      DivZeroBug.reset(new BuiltinBug(this, "Division by zero"));

    const ExplodedNode *CompNode = BoundNodes.getNodeAs<ExplodedNode>("comp"),
                       *DivNode = BoundNodes.getNodeAs<ExplodedNode>("div");
    assert(CompNode && DivNode);
    auto R = llvm::make_unique<BugReport>(
        *DivZeroBug,
        "Value being compared against zero has already been used for division",
        CompNode);

    R->addVisitor(llvm::make_unique<DivisionBRVisitorV2>(DivNode));
    BR.emitReport(std::move(R));
  });

  Finder.addMatcher(
      hasSequence(
          explodedNode(
              postStmt(hasStatement(binaryOperator(
                  isDivisionOp(),
                  hasRHS(hasValue(definedSVal(canBeZero()).bind("value")))))),
              hasStackFrame(stackFrameContext().bind("loc_ctx")))
              .bind("div"),
          unless(callExitEnd(hasCalleeContext(equalsBoundNode("loc_ctx")))),
          explodedNode(
              postCondition(hasStatement(anyOf(
                  binaryOperator(
                      isComparisonOp(),
                      hasBothOperands(
                          ignoringParenImpCasts(integerLiteral(equals(0))),
                          expr(hasValue(equalsBoundNode("value"))))),
                  unaryOperator(hasOperatorName("!"),
                                hasUnaryOperand(anyOf(
                                    hasValue(equalsBoundNode("value")),
                                    implicitCastExpr(hasSourceExpression(
                                        hasValue(equalsBoundNode("value"))))))),
                  implicitCastExpr(anyOf(hasValue(equalsBoundNode("value")),
                                         hasSourceExpression(hasValue(
                                             equalsBoundNode("value")))))))))
              .bind("comp")),
      &Callback);
  Finder.match(G, BR, Eng);
}

void ento::registerTestAfterDivZeroCheckerV2(CheckerManager &mgr) {
  mgr.registerChecker<TestAfterDivZeroCheckerV2>();
}
