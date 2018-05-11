//===--- ASTGraphTypeTraits.cpp ---------------------------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  Provides a dynamic type identifier and a dynamically typed node container
//  that can be used to store an AST graph base node at runtime in the same
//  storage in a type safe way.
//
//  FIXME: This may need to be merged into ASTTypeTraits to avoid massive
//  code duplication.
//
//===----------------------------------------------------------------------===//

#include "clang/ASTMatchers/ASTGraphTypeTraits.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclCXX.h"

namespace clang {
namespace ento {
namespace ast_graph_type_traits {

const ASTGraphNodeKind::KindInfo ASTGraphNodeKind::AllKindInfo[] = {
    {NKI_None, "<None>"},
    {NKI_None, "TemplateArgument"},
    {NKI_None, "TemplateName"},
    {NKI_None, "NestedNameSpecifierLoc"},
    {NKI_None, "QualType"},
    {NKI_None, "TypeLoc"},
    {NKI_None, "CXXCtorInitializer"},
    {NKI_None, "NestedNameSpecifier"},
    {NKI_None, "Decl"},
#define DECL(DERIVED, BASE) {NKI_##BASE, #DERIVED "Decl"},
#include "clang/AST/DeclNodes.inc"
    {NKI_None, "Stmt"},
#define STMT(DERIVED, BASE) {NKI_##BASE, #DERIVED},
#include "clang/AST/StmtNodes.inc"
    {NKI_None, "Type"},
#define TYPE(DERIVED, BASE) {NKI_##BASE, #DERIVED "Type"},
#include "clang/AST/TypeNodes.def"
    {NKI_None, "CFGBlock"},
    {NKI_None, "CFGElement"},
    {NKI_None, "ExplodedNode"},
    {NKI_None, "ProgramState"},
    {NKI_None, "MemRegion"},
#define REGION(DERIVED, BASE) {NKI_##BASE, #DERIVED},
#define ABSTRACT_REGION(DERIVED, BASE) REGION(DERIVED, BASE)
#include "clang/StaticAnalyzer/Core/PathSensitive/Regions.def"
    {NKI_None, "SymExpr"},
#define SYMBOL(DERIVED, BASE) {NKI_##BASE, #DERIVED},
#define ABSTRACT_SYMBOL(Id, Parent) SYMBOL(Id, Parent)
#include "clang/StaticAnalyzer/Core/PathSensitive/Symbols.def"
    {NKI_None, "LocationContext"},
    {NKI_LocationContext, "StackFrameContext"},
    {NKI_LocationContext, "ScopeContext"},
    {NKI_LocationContext, "BlockInvocationContext"},
    {NKI_None, "ExplodedGraph"},
    {NKI_None, "CFG"},
    {NKI_None, "SVal"},
#define BASIC_SVAL(DERIVED, BASE) {NKI_##BASE, #DERIVED},
#define ABSTRACT_SVAL(DERIVED, BASE) {NKI_##BASE, #DERIVED},
#define LOC_SVAL(DERIVED, BASE) {NKI_##BASE, #DERIVED},
#define NONLOC_SVAL(DERIVED, BASE) {NKI_##BASE, #DERIVED},
#include "clang/StaticAnalyzer/Core/PathSensitive/SVals.def"
    {NKI_None, "ProgramPoint"},
#define PROGRAM_POINT(DERIVED, BASE) {NKI_##BASE, #DERIVED},
#define ABSTRACT_PROGRAM_POINT(Id, Parent) PROGRAM_POINT(Id, Parent)
#include "clang/Analysis/ProgramPoint.def"

};

bool ASTGraphNodeKind::isBaseOf(ASTGraphNodeKind Other,
                                unsigned *Distance) const {
  return isBaseOf(KindId, Other.KindId, Distance);
}

bool ASTGraphNodeKind::isBaseOf(NodeKindId Base, NodeKindId Derived,
                                unsigned *Distance) {
  if (Base == NKI_None || Derived == NKI_None)
    return false;
  unsigned Dist = 0;
  while (Derived != Base && Derived != NKI_None) {
    Derived = AllKindInfo[Derived].ParentId;
    ++Dist;
  }
  if (Distance)
    *Distance = Dist;
  return Derived == Base;
}

StringRef ASTGraphNodeKind::asStringRef() const {
  return AllKindInfo[KindId].Name;
}

ASTGraphNodeKind ASTGraphNodeKind::getMostDerivedType(ASTGraphNodeKind Kind1,
                                                      ASTGraphNodeKind Kind2) {
  if (Kind1.isBaseOf(Kind2))
    return Kind2;
  if (Kind2.isBaseOf(Kind1))
    return Kind1;
  return ASTGraphNodeKind();
}

ASTGraphNodeKind
ASTGraphNodeKind::getMostDerivedCommonAncestor(ASTGraphNodeKind Kind1,
                                               ASTGraphNodeKind Kind2) {
  NodeKindId Parent = Kind1.KindId;
  while (!isBaseOf(Parent, Kind2.KindId, nullptr) && Parent != NKI_None) {
    Parent = AllKindInfo[Parent].ParentId;
  }
  return ASTGraphNodeKind(Parent);
}

ASTGraphNodeKind ASTGraphNodeKind::getFromNode(const Decl &D) {
  switch (D.getKind()) {
#define DECL(DERIVED, BASE)                                                    \
  case Decl::DERIVED:                                                          \
    return ASTGraphNodeKind(NKI_##DERIVED##Decl);
#define ABSTRACT_DECL(D)
#include "clang/AST/DeclNodes.inc"
  };
  llvm_unreachable("invalid decl kind");
}

ASTGraphNodeKind ASTGraphNodeKind::getFromNode(const Stmt &S) {
  switch (S.getStmtClass()) {
  case Stmt::NoStmtClass:
    return NKI_None;
#define STMT(CLASS, PARENT)                                                    \
  case Stmt::CLASS##Class:                                                     \
    return ASTGraphNodeKind(NKI_##CLASS);
#define ABSTRACT_STMT(S)
#include "clang/AST/StmtNodes.inc"
  }
  llvm_unreachable("invalid stmt kind");
}

ASTGraphNodeKind ASTGraphNodeKind::getFromNode(const Type &T) {
  switch (T.getTypeClass()) {
#define TYPE(Class, Base)                                                      \
  case Type::Class:                                                            \
    return ASTGraphNodeKind(NKI_##Class##Type);
#define ABSTRACT_TYPE(Class, Base)
#include "clang/AST/TypeNodes.def"
  }
  llvm_unreachable("invalid type kind");
}

ASTGraphNodeKind ASTGraphNodeKind::getFromNode(const SVal &SV) {
  switch (SV.getBaseKind()) {
#define BASIC_SVAL(Id, Parent)                                                 \
  case SVal::Id##Kind:                                                         \
    return ASTGraphNodeKind(NKI_##Id);
#include "clang/StaticAnalyzer/Core/PathSensitive/SVals.def"
  case SVal::NonLocKind: {
    switch (SV.getSubKind()) {
#define NONLOC_SVAL(Id, Parent)                                                \
  case nonloc::Id##Kind:                                                       \
    return ASTGraphNodeKind(NKI_nonloc_##Id);
#include "clang/StaticAnalyzer/Core/PathSensitive/SVals.def"
    }
  }
  case SVal::LocKind: {
    switch (SV.getSubKind()) {
#define LOC_SVAL(Id, Parent)                                                   \
  case loc::Id##Kind:                                                          \
    return ASTGraphNodeKind(NKI_loc_##Id);
#include "clang/StaticAnalyzer/Core/PathSensitive/SVals.def"
    }
  }
  }
  llvm_unreachable("Invalid SVal kind");
}

ASTGraphNodeKind ASTGraphNodeKind::getFromNode(const MemRegion &Region) {
  switch (Region.getKind()) {
#define REGION(Id, Parent)                                                     \
  case MemRegion::Id##Kind:                                                    \
    return ASTGraphNodeKind(NKI_##Id);
#define ABSTRACT_REGION(Id, Parent) REGION(Id, Parent)
#include "clang/StaticAnalyzer/Core/PathSensitive/Regions.def"
  }
  llvm_unreachable("Invalid MemRegion kind");
}

ASTGraphNodeKind ASTGraphNodeKind::getFromNode(const SymExpr &Sym) {
  switch (Sym.getKind()) {
#define SYMBOL(Id, Parent)                                                     \
  case SymExpr::Id##Kind:                                                      \
    return ASTGraphNodeKind(NKI_##Id);
#define ABSTRACT_SYMBOL(Id, Parent) SYMBOL(Id, Parent)
#include "clang/StaticAnalyzer/Core/PathSensitive/Symbols.def"
  }
  llvm_unreachable("Invalid SymExpr kind");
}

ASTGraphNodeKind ASTGraphNodeKind::getFromNode(const LocationContext &LCtx) {
  switch (LCtx.getKind()) {
  case LocationContext::StackFrame:
    return ASTGraphNodeKind(NKI_StackFrameContext);
  case LocationContext::Scope:
    return ASTGraphNodeKind(NKI_ScopeContext);
  case LocationContext::Block:
    return ASTGraphNodeKind(NKI_BlockInvocationContext);
  }
  llvm_unreachable("Invalid LocationContext kind");
}

ASTGraphNodeKind ASTGraphNodeKind::getFromNode(const ProgramPoint &PP) {
  switch (PP.getKind()) {
#define PROGRAM_POINT(Id, Parent)                                              \
  case ProgramPoint::Id##Kind:                                                 \
    return ASTGraphNodeKind(NKI_##Id);
#define ABSTRACT_PROGRAM_POINT(Id, Parent) PROGRAM_POINT(Id, Parent)
#include "clang/Analysis/ProgramPoint.def"
  }
  llvm_unreachable("Invalid Program point kind");
}

void DynTypedNode::print(llvm::raw_ostream &OS,
                         const PrintingPolicy &PP) const {
  if (const TemplateArgument *TA = get<TemplateArgument>())
    TA->print(PP, OS);
  else if (const TemplateName *TN = get<TemplateName>())
    TN->print(OS, PP);
  else if (const NestedNameSpecifier *NNS = get<NestedNameSpecifier>())
    NNS->print(OS, PP);
  else if (const NestedNameSpecifierLoc *NNSL = get<NestedNameSpecifierLoc>())
    NNSL->getNestedNameSpecifier()->print(OS, PP);
  else if (const QualType *QT = get<QualType>())
    QT->print(OS, PP);
  else if (const TypeLoc *TL = get<TypeLoc>())
    TL->getType().print(OS, PP);
  else if (const Decl *D = get<Decl>())
    D->print(OS, PP);
  else if (const Stmt *S = get<Stmt>())
    S->printPretty(OS, nullptr, PP);
  else if (const Type *T = get<Type>())
    QualType(T, 0).print(OS, PP);
  else if (const ProgramState *State = get<ProgramState>())
    State->print(OS);
  else if (const SVal *SV = get<SVal>())
    SV->dumpToStream(OS);
  else if (const MemRegion *MR = get<MemRegion>())
    MR->printPretty(OS);
  else if (const SymExpr *SE = get<SymExpr>())
    SE->dumpToStream(OS);
  else
    // FIXME:ProgramPoint, etc.
    OS << "Unable to print values of type " << NodeKind.asStringRef() << "\n";
}

void DynTypedNode::dump(llvm::raw_ostream &OS, SourceManager &SM) const {
  if (const Decl *D = get<Decl>())
    D->dump(OS);
  else if (const Stmt *S = get<Stmt>())
    S->dump(OS, SM);
  else if (const Type *T = get<Type>())
    T->dump(OS);
  else if (const ProgramState *State = get<ProgramState>())
    State->print(OS);
  else if (const SVal *SV = get<SVal>())
    SV->dumpToStream(OS);
  else if (const MemRegion *MR = get<MemRegion>())
    MR->printPretty(OS);
  else if (const SymExpr *SE = get<SymExpr>())
    SE->dumpToStream(OS);
  else
    OS << "Unable to dump values of type " << NodeKind.asStringRef() << "\n";
}

SourceRange DynTypedNode::getSourceRange() const {
  if (const CXXCtorInitializer *CCI = get<CXXCtorInitializer>())
    return CCI->getSourceRange();
  if (const NestedNameSpecifierLoc *NNSL = get<NestedNameSpecifierLoc>())
    return NNSL->getSourceRange();
  if (const TypeLoc *TL = get<TypeLoc>())
    return TL->getSourceRange();
  if (const Decl *D = get<Decl>())
    return D->getSourceRange();
  if (const Stmt *S = get<Stmt>())
    return S->getSourceRange();
  // Graph nodes don't have source ranges because they don't relate
  // to the source code.
  return SourceRange();
}

} // namespace ast_graph_type_traits
} // end namespace ento
} // end namespace clang
