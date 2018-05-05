//===--- ASTTypeTraits.h ----------------------------------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  Provides a dynamic type identifier and a dynamically typed node container
//  that can be used to store an AST base node at runtime in the same storage in
//  a type safe way.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_AST_ASTGRAPHTYPETRAITS_H
#define LLVM_CLANG_AST_ASTGRAPHTYPETRAITS_H

#include "clang/AST/ASTFwd.h"
#include "clang/AST/Decl.h"
#include "clang/AST/NestedNameSpecifier.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/TemplateBase.h"
#include "clang/AST/TypeLoc.h"
#include "clang/Basic/LLVM.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ExplodedGraph.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/MemRegion.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/SVals.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/SymExpr.h"
#include "llvm/ADT/DenseMapInfo.h"
#include "llvm/Support/AlignOf.h"

namespace llvm {

class raw_ostream;
}

namespace clang {

struct PrintingPolicy;

namespace ento {

class ProgramState;

namespace ast_graph_type_traits {

/// \brief Kind identifier.
///
/// It can be constructed from any node kind and allows for runtime type
/// hierarchy checks.
/// Use getFromNodeKind<T>() to construct them.
class ASTGraphNodeKind {
public:
  /// \brief Empty identifier. It matches nothing.
  ASTGraphNodeKind() : KindId(NKI_None) {}

  /// \brief Construct an identifier for T.
  template <class T> static ASTGraphNodeKind getFromNodeKind() {
    return ASTGraphNodeKind(KindToKindId<T>::Id);
  }

  /// \{
  /// \brief Construct an identifier for the dynamic type of the node
  static ASTGraphNodeKind getFromNode(const Decl &D);
  static ASTGraphNodeKind getFromNode(const Stmt &S);
  static ASTGraphNodeKind getFromNode(const Type &T);
  static ASTGraphNodeKind getFromNode(const ProgramState &State);
  static ASTGraphNodeKind getFromNode(const SVal &SV);
  static ASTGraphNodeKind getFromNode(const ExplodedNode &N);
  static ASTGraphNodeKind getFromNode(const MemRegion &Region);
  static ASTGraphNodeKind getFromNode(const SymExpr &Sym);
  static ASTGraphNodeKind getFromNode(const LocationContext &LCtx);
  static ASTGraphNodeKind getFromNode(const ProgramPoint &PP);

  /// \}

  /// \brief Returns \c true if \c this and \c Other represent the same kind.
  bool isSame(ASTGraphNodeKind Other) const {
    return KindId != NKI_None && KindId == Other.KindId;
  }

  /// \brief Returns \c true only for the default \c ASTNodeKind()
  bool isNone() const { return KindId == NKI_None; }

  /// \brief Returns \c true if \c this is a base kind of (or same as) \c Other.
  /// \param Distance If non-null, used to return the distance between \c this
  /// and \c Other in the class hierarchy.
  bool isBaseOf(ASTGraphNodeKind Other, unsigned *Distance = nullptr) const;

  /// \brief String representation of the kind.
  StringRef asStringRef() const;

  /// \brief Strict weak ordering for ASTNodeKind.
  bool operator<(const ASTGraphNodeKind &Other) const {
    return KindId < Other.KindId;
  }

  /// \brief Return the most derived type between \p Kind1 and \p Kind2.
  ///
  /// Return ASTNodeKind() if they are not related.
  static ASTGraphNodeKind getMostDerivedType(ASTGraphNodeKind Kind1,
                                             ASTGraphNodeKind Kind2);

  /// \brief Return the most derived common ancestor between Kind1 and Kind2.
  ///
  /// Return ASTNodeKind() if they are not related.
  static ASTGraphNodeKind getMostDerivedCommonAncestor(ASTGraphNodeKind Kind1,
                                                       ASTGraphNodeKind Kind2);

  /// \brief Hooks for using ASTNodeKind as a key in a DenseMap.
  struct DenseMapInfo {
    // ASTGraphNodeKind() is a good empty key because it is represented as a 0.
    static inline ASTGraphNodeKind getEmptyKey() { return ASTGraphNodeKind(); }
    // NKI_NumberOfKinds is not a valid value, so it is good for a
    // tombstone key.
    static inline ASTGraphNodeKind getTombstoneKey() {
      return ASTGraphNodeKind(NKI_NumberOfKinds);
    }
    static unsigned getHashValue(const ASTGraphNodeKind &Val) {
      return Val.KindId;
    }
    static bool isEqual(const ASTGraphNodeKind &LHS,
                        const ASTGraphNodeKind &RHS) {
      return LHS.KindId == RHS.KindId;
    }
  };

  /// Check if the given ASTNodeKind identifies a type that offers pointer
  /// identity. This is useful for the fast path in DynTypedNode.
  bool hasPointerIdentity() const {
    return KindId > NKI_LastKindWithoutPointerIdentity && KindId < NKI_SVal;
  }

  /// \brief Kind ids.
  ///
  /// Includes all possible base and derived kinds.
  enum NodeKindId {
    NKI_None,
    NKI_TemplateArgument,
    NKI_TemplateName,
    NKI_NestedNameSpecifierLoc,
    NKI_QualType,
    NKI_TypeLoc,
    NKI_LastKindWithoutPointerIdentity = NKI_TypeLoc,
    NKI_CXXCtorInitializer,
    NKI_NestedNameSpecifier,
    NKI_Decl,
#define DECL(DERIVED, BASE) NKI_##DERIVED##Decl,
#include "clang/AST/DeclNodes.inc"
    NKI_Stmt,
#define STMT(DERIVED, BASE) NKI_##DERIVED,
#include "clang/AST/StmtNodes.inc"
    NKI_Type,
#define TYPE(DERIVED, BASE) NKI_##DERIVED##Type,
#include "clang/AST/TypeNodes.def"
    NKI_ExplodedNode,
    NKI_ProgramState,
    NKI_MemRegion,
#define REGION(Id, Parent) NKI_##Id,
#define ABSTRACT_REGION(Id, Parent) REGION(Id, Parent)
#include "clang/StaticAnalyzer/Core/PathSensitive/Regions.def"
    NKI_SymExpr,
#define SYMBOL(Id, Parent) NKI_##Id,
#define ABSTRACT_SYMBOL(Id, Parent) SYMBOL(Id, Parent)
#include "clang/StaticAnalyzer/Core/PathSensitive/Symbols.def"

    NKI_LocationContext,
    NKI_StackFrameContext,
    NKI_ScopeContext,
    NKI_BlockInvocationContext,

    NKI_ExplodedGraph,
    NKI_CFG,

    NKI_SVal,
#define BASIC_SVAL(Id, Parent) NKI_##Id,
#define ABSTRACT_SVAL(Id, Parent) BASIC_SVAL(Id, Parent)
#define LOC_SVAL(Id, Parent) NKI_loc_##Id,
#define NONLOC_SVAL(Id, Parent) NKI_nonloc_##Id,
#include "clang/StaticAnalyzer/Core/PathSensitive/SVals.def"

    NKI_ProgramPoint,
#define PROGRAM_POINT(Id, Parent) NKI_##Id,
#define ABSTRACT_PROGRAM_POINT(Id, Parent) PROGRAM_POINT(Id, Parent)
#include "clang/Analysis/ProgramPoint.def"

    NKI_NumberOfKinds
  };

  /// \brief Use getFromNodeKind<T>() to construct the kind.
  ASTGraphNodeKind(NodeKindId KindId) : KindId(KindId) {}

  /// \brief Returns \c true if \c Base is a base kind of (or same as) \c
  ///   Derived.
  /// \param Distance If non-null, used to return the distance between \c Base
  /// and \c Derived in the class hierarchy.
  static bool isBaseOf(NodeKindId Base, NodeKindId Derived, unsigned *Distance);

  /// \brief Helper meta-function to convert a kind T to its enum value.
  ///
  /// This struct is specialized below for all known kinds.
  template <class T> struct KindToKindId {
    static const NodeKindId Id = NKI_None;
  };
  template <class T> struct KindToKindId<const T> : KindToKindId<T> {};

  /// \brief Per kind info.
  struct KindInfo {
    /// \brief The id of the parent kind, or None if it has no parent.
    NodeKindId ParentId;
    /// \brief Name of the kind.
    const char *Name;
  };
  static const KindInfo AllKindInfo[NKI_NumberOfKinds];

  NodeKindId KindId;
};

#define KIND_TO_KIND_ID(Class)                                                 \
  template <> struct ASTGraphNodeKind::KindToKindId<Class> {                   \
    static const NodeKindId Id = NKI_##Class;                                  \
  };

KIND_TO_KIND_ID(CXXCtorInitializer)
KIND_TO_KIND_ID(TemplateArgument)
KIND_TO_KIND_ID(TemplateName)
KIND_TO_KIND_ID(NestedNameSpecifier)
KIND_TO_KIND_ID(NestedNameSpecifierLoc)
KIND_TO_KIND_ID(QualType)
KIND_TO_KIND_ID(TypeLoc)
KIND_TO_KIND_ID(Decl)
KIND_TO_KIND_ID(Stmt)
KIND_TO_KIND_ID(Type)
#define DECL(DERIVED, BASE) KIND_TO_KIND_ID(DERIVED##Decl)
#include "clang/AST/DeclNodes.inc"
#define STMT(DERIVED, BASE) KIND_TO_KIND_ID(DERIVED)
#include "clang/AST/StmtNodes.inc"
#define TYPE(DERIVED, BASE) KIND_TO_KIND_ID(DERIVED##Type)
#include "clang/AST/TypeNodes.def"

KIND_TO_KIND_ID(ExplodedNode)
KIND_TO_KIND_ID(ProgramState)
KIND_TO_KIND_ID(SVal)
KIND_TO_KIND_ID(MemRegion)
KIND_TO_KIND_ID(SymExpr)
KIND_TO_KIND_ID(ProgramPoint)

KIND_TO_KIND_ID(LocationContext)
KIND_TO_KIND_ID(StackFrameContext)
KIND_TO_KIND_ID(ScopeContext)
KIND_TO_KIND_ID(BlockInvocationContext)

#define SVAL_KIND_TO_KIND_ID(Namespace, Class)                                 \
  template <> struct ASTGraphNodeKind::KindToKindId<Namespace::Class> {        \
    static const NodeKindId Id = NKI_##Namespace##_##Class;                    \
  };

#define BASIC_SVAL(Id, Parent) KIND_TO_KIND_ID(Id)
#define ABSTRACT_SVAL(Id, Parent) BASIC_SVAL(Id, Parent)
#define LOC_SVAL(Id, Parent) SVAL_KIND_TO_KIND_ID(loc, Id)
#define NONLOC_SVAL(Id, Parent) SVAL_KIND_TO_KIND_ID(nonloc, Id)
#include "clang/StaticAnalyzer/Core/PathSensitive/SVals.def"

#define PROGRAM_POINT(Id, Parent) KIND_TO_KIND_ID(Id)
#define ABSTRACT_PROGRAM_POINT(Id, Parent) PROGRAM_POINT(Id, Parent)
#include "clang/Analysis/ProgramPoint.def"

#define REGION(Id, Parent) KIND_TO_KIND_ID(Id)
#define ABSTRACT_REGION(Id, Parent) REGION(Id, Parent)
#include "clang/StaticAnalyzer/Core/PathSensitive/Regions.def"

#define SYMBOL(Id, Parent) KIND_TO_KIND_ID(Id)
#define ABSTRACT_SYMBOL(Id, Parent) SYMBOL(Id, Parent)
#include "clang/StaticAnalyzer/Core/PathSensitive/Symbols.def"
#undef SVAL_KIND_TO_KIND_ID

KIND_TO_KIND_ID(ExplodedGraph)
KIND_TO_KIND_ID(CFG)
#undef KIND_TO_KIND_ID

inline raw_ostream &operator<<(raw_ostream &OS, ASTGraphNodeKind K) {
  OS << K.asStringRef();
  return OS;
}

/// \brief A dynamically typed AST graph node container.
///
/// Stores a ASTGraph node in a type safe way. This allows writing code that
/// works with different kinds of AST nodes, despite the fact that they don't
/// have a common base class.
///
/// Use \c create(Node) to create a \c DynGraphTypedNode from an AST graph node,
/// and \c get<T>() to retrieve the node as type T if the types match.
///
/// See \c ASTGraphNodeKind for which node base types are currently supported;
/// You can create DynTypedNodes for all nodes in the inheritance hierarchy of
/// the supported base types.
class DynTypedNode {
public:
  /// \brief Creates a \c DynTypedNode from \c Node.
  template <typename T> static DynTypedNode create(const T &Node);

  ast_type_traits::DynTypedNode getAsASTTypeTrait() const {
    ast_type_traits::DynTypedNode Result;
    Result.NodeKind =
        static_cast<ast_type_traits::ASTNodeKind::NodeKindId>(NodeKind.KindId);
    memcpy(Result.Storage.buffer, this->Storage.buffer,
           sizeof(Result.Storage.buffer));
    return Result;
  }

  /// \brief Retrieve the stored node as type \c T.
  ///
  /// Returns NULL if the stored node does not have a type that is
  /// convertible to \c T.
  ///
  /// For types that have identity via their pointer in the AST
  /// (like \c Stmt, \c Decl, \c Type and \c NestedNameSpecifier) the returned
  /// pointer points to the referenced AST node.
  /// For other types (like \c QualType) the value is stored directly
  /// in the \c DynTypedNode, and the returned pointer points at
  /// the storage inside DynTypedNode. For those nodes, do not
  /// use the pointer outside the scope of the DynTypedNode.
  template <typename T> const T *get() const {
    return BaseConverter<T>::get(NodeKind, Storage.buffer);
  }

  /// \brief Retrieve the stored node as type \c T.
  ///
  /// Similar to \c get(), but asserts that the type is what we are expecting.
  template <typename T> const T &getUnchecked() const {
    return BaseConverter<T>::getUnchecked(NodeKind, Storage.buffer);
  }

  ASTGraphNodeKind getNodeKind() const { return NodeKind; }

  /// \brief Returns a pointer that identifies the stored AST node.
  ///
  /// Note that this is not supported by all AST nodes. For AST nodes
  /// that don't have a pointer-defined identity inside the AST, this
  /// method returns NULL.
  const void *getMemoizationData() const {
    return NodeKind.hasPointerIdentity()
               ? *reinterpret_cast<void *const *>(Storage.buffer)
               : nullptr;
  }

  /// \brief Prints the node to the given output stream.
  void print(llvm::raw_ostream &OS, const PrintingPolicy &PP) const;

  /// \brief Dumps the node to the given output stream.
  void dump(llvm::raw_ostream &OS, SourceManager &SM) const;

  /// \brief For nodes which represent textual entities in the source code,
  /// return their SourceRange.  For all other nodes, return SourceRange().
  SourceRange getSourceRange() const;

  /// @{
  /// \brief Imposes an order on \c DynTypedNode.
  ///
  /// Supports comparison of nodes that support memoization.
  /// FIXME: Implement comparsion for other node types (currently
  /// only Stmt, Decl, Type and NestedNameSpecifier return memoization data).
  bool operator<(const DynTypedNode &Other) const {
    if (!NodeKind.isSame(Other.NodeKind))
      return NodeKind < Other.NodeKind;

    if (ASTGraphNodeKind::getFromNodeKind<QualType>().isSame(NodeKind))
      return getUnchecked<QualType>().getAsOpaquePtr() <
             Other.getUnchecked<QualType>().getAsOpaquePtr();

    if (ASTGraphNodeKind::getFromNodeKind<TypeLoc>().isSame(NodeKind)) {
      auto TLA = getUnchecked<TypeLoc>();
      auto TLB = Other.getUnchecked<TypeLoc>();
      return std::make_pair(TLA.getType().getAsOpaquePtr(),
                            TLA.getOpaqueData()) <
             std::make_pair(TLB.getType().getAsOpaquePtr(),
                            TLB.getOpaqueData());
    }

    if (ASTGraphNodeKind::getFromNodeKind<NestedNameSpecifierLoc>().isSame(
            NodeKind)) {
      auto NNSLA = getUnchecked<NestedNameSpecifierLoc>();
      auto NNSLB = Other.getUnchecked<NestedNameSpecifierLoc>();
      return std::make_pair(NNSLA.getNestedNameSpecifier(),
                            NNSLA.getOpaqueData()) <
             std::make_pair(NNSLB.getNestedNameSpecifier(),
                            NNSLB.getOpaqueData());
    }

    if (ASTGraphNodeKind::getFromNodeKind<SVal>().isBaseOf(NodeKind))
      return getUnchecked<SVal>() < Other.getUnchecked<SVal>();

    if (ASTGraphNodeKind::getFromNodeKind<ProgramPoint>().isBaseOf(NodeKind))
      return getUnchecked<ProgramPoint>() < Other.getUnchecked<ProgramPoint>();

    assert(getMemoizationData() && Other.getMemoizationData());
    return getMemoizationData() < Other.getMemoizationData();
  }
  DynTypedNode &operator=(const DynTypedNode &Other) = default;
  DynTypedNode &operator=(const ast_type_traits::DynTypedNode &Other) {
    this->NodeKind.KindId =
        static_cast<ento::ast_graph_type_traits::ASTGraphNodeKind::NodeKindId>(
            Other.NodeKind.KindId);
    memcpy(this->Storage.buffer, Other.Storage.buffer,
           sizeof(Other.Storage.buffer));
    return *this;
  }

  bool operator==(const DynTypedNode &Other) const {
    // DynTypedNode::create() stores the exact kind of the node in NodeKind.
    // If they contain the same node, their NodeKind must be the same.
    if (!NodeKind.isSame(Other.NodeKind))
      return false;

    // FIXME: Implement for other types.
    if (ASTGraphNodeKind::getFromNodeKind<QualType>().isSame(NodeKind))
      return getUnchecked<QualType>() == Other.getUnchecked<QualType>();

    if (ASTGraphNodeKind::getFromNodeKind<TypeLoc>().isSame(NodeKind))
      return getUnchecked<TypeLoc>() == Other.getUnchecked<TypeLoc>();

    if (ASTGraphNodeKind::getFromNodeKind<NestedNameSpecifierLoc>().isSame(
            NodeKind))
      return getUnchecked<NestedNameSpecifierLoc>() ==
             Other.getUnchecked<NestedNameSpecifierLoc>();

    if (ASTGraphNodeKind::getFromNodeKind<SVal>().isBaseOf(NodeKind))
      return getUnchecked<SVal>() == Other.getUnchecked<SVal>();

    assert(getMemoizationData() && Other.getMemoizationData());
    return getMemoizationData() == Other.getMemoizationData();
  }
  bool operator!=(const DynTypedNode &Other) const {
    return !operator==(Other);
  }
  /// @}

  /// \brief Hooks for using DynTypedNode as a key in a DenseMap.
  struct DenseMapInfo {
    static inline DynTypedNode getEmptyKey() {
      DynTypedNode Node;
      Node.NodeKind = ASTGraphNodeKind::DenseMapInfo::getEmptyKey();
      return Node;
    }
    static inline DynTypedNode getTombstoneKey() {
      DynTypedNode Node;
      Node.NodeKind = ASTGraphNodeKind::DenseMapInfo::getTombstoneKey();
      return Node;
    }
    static unsigned getHashValue(const DynTypedNode &Val) {
      // FIXME: Add hashing support for the remaining types.
      if (ASTGraphNodeKind::getFromNodeKind<TypeLoc>().isSame(Val.NodeKind)) {
        auto TL = Val.getUnchecked<TypeLoc>();
        return llvm::hash_combine(TL.getType().getAsOpaquePtr(),
                                  TL.getOpaqueData());
      }

      if (ASTGraphNodeKind::getFromNodeKind<NestedNameSpecifierLoc>().isSame(
              Val.NodeKind)) {
        auto NNSL = Val.getUnchecked<NestedNameSpecifierLoc>();
        return llvm::hash_combine(NNSL.getNestedNameSpecifier(),
                                  NNSL.getOpaqueData());
      }

      assert(Val.getMemoizationData());
      return llvm::hash_value(Val.getMemoizationData());
    }
    static bool isEqual(const DynTypedNode &LHS, const DynTypedNode &RHS) {
      auto Empty = ASTGraphNodeKind::DenseMapInfo::getEmptyKey();
      auto TombStone = ASTGraphNodeKind::DenseMapInfo::getTombstoneKey();
      return (ASTGraphNodeKind::DenseMapInfo::isEqual(LHS.NodeKind, Empty) &&
              ASTGraphNodeKind::DenseMapInfo::isEqual(RHS.NodeKind, Empty)) ||
             (ASTGraphNodeKind::DenseMapInfo::isEqual(LHS.NodeKind,
                                                      TombStone) &&
              ASTGraphNodeKind::DenseMapInfo::isEqual(RHS.NodeKind,
                                                      TombStone)) ||
             LHS == RHS;
    }
  };

private:
  /// \brief Takes care of converting from and to \c T.
  template <typename T, typename EnablerT = void> struct BaseConverter;

  /// \brief Converter that uses dyn_cast<T> from a stored BaseT*.
  template <typename T, typename BaseT> struct DynCastPtrConverter {
    static const T *get(ASTGraphNodeKind NodeKind, const char Storage[]) {
      if (ASTGraphNodeKind::getFromNodeKind<T>().isBaseOf(NodeKind))
        return &getUnchecked(NodeKind, Storage);
      return nullptr;
    }
    static const T &getUnchecked(ASTGraphNodeKind NodeKind,
                                 const char Storage[]) {
      assert(ASTGraphNodeKind::getFromNodeKind<T>().isBaseOf(NodeKind));
      return *cast<T>(static_cast<const BaseT *>(
          *reinterpret_cast<const void *const *>(Storage)));
    }
    static DynTypedNode create(const BaseT &Node) {
      DynTypedNode Result;
      Result.NodeKind = ASTGraphNodeKind::getFromNode(Node);
      new (Result.Storage.buffer) const void *(&Node);
      return Result;
    }
  };

  /// \brief Converter that uses dyn_cast<T> from a stored BaseT*.
  template <typename T, typename BaseT> struct DynCastValueConverter {
    static const T *get(ASTGraphNodeKind NodeKind, const char Storage[]) {
      if (ASTGraphNodeKind::getFromNodeKind<T>().isBaseOf(NodeKind))
        return &getUnchecked(NodeKind, Storage);
      return nullptr;
    }
    static const T &getUnchecked(ASTGraphNodeKind NodeKind,
                                 const char Storage[]) {
      assert(ASTGraphNodeKind::getFromNodeKind<T>().isBaseOf(NodeKind));
      return cast<T>(*reinterpret_cast<const BaseT *>(Storage));
    }
    static DynTypedNode create(const BaseT &Node) {
      DynTypedNode Result;
      Result.NodeKind = ASTGraphNodeKind::getFromNode(Node);
      new (Result.Storage.buffer) BaseT(Node);
      return Result;
    }
  };

  /// \brief Converter that stores T* (by pointer).
  template <typename T> struct PtrConverter {
    static const T *get(ASTGraphNodeKind NodeKind, const char Storage[]) {
      if (ASTGraphNodeKind::getFromNodeKind<T>().isSame(NodeKind))
        return &getUnchecked(NodeKind, Storage);
      return nullptr;
    }
    static const T &getUnchecked(ASTGraphNodeKind NodeKind,
                                 const char Storage[]) {
      assert(ASTGraphNodeKind::getFromNodeKind<T>().isSame(NodeKind));
      return *static_cast<const T *>(
          *reinterpret_cast<const void *const *>(Storage));
    }
    static DynTypedNode create(const T &Node) {
      DynTypedNode Result;
      Result.NodeKind = ASTGraphNodeKind::getFromNodeKind<T>();
      new (Result.Storage.buffer) const void *(&Node);
      return Result;
    }
  };

  /// \brief Converter that stores T (by value).
  template <typename T> struct ValueConverter {
    static const T *get(ASTGraphNodeKind NodeKind, const char Storage[]) {
      if (ASTGraphNodeKind::getFromNodeKind<T>().isSame(NodeKind))
        return reinterpret_cast<const T *>(Storage);
      return nullptr;
    }
    static const T &getUnchecked(ASTGraphNodeKind NodeKind,
                                 const char Storage[]) {
      assert(ASTGraphNodeKind::getFromNodeKind<T>().isSame(NodeKind));
      return *reinterpret_cast<const T *>(Storage);
    }
    static DynTypedNode create(const T &Node) {
      DynTypedNode Result;
      Result.NodeKind = ASTGraphNodeKind::getFromNodeKind<T>();
      new (Result.Storage.buffer) T(Node);
      return Result;
    }
  };

  ASTGraphNodeKind NodeKind;

  /// \brief Stores the data of the node.
  ///
  /// Note that we can store \c Decls, \c Stmts, \c Types,
  /// \c NestedNameSpecifiers and \c CXXCtorInitializer by pointer as they are
  /// guaranteed to be unique pointers pointing to dedicated storage in the AST.
  /// \c QualTypes, \c NestedNameSpecifierLocs, \c TypeLocs and
  /// \c TemplateArguments on the other hand do not have storage or unique
  /// pointers and thus need to be stored by value.
  llvm::AlignedCharArrayUnion<const void *, TemplateArgument,
                              NestedNameSpecifierLoc, QualType, TypeLoc, SVal,
                              ProgramPoint>
      Storage;
};

template <>
inline DynTypedNode DynTypedNode::create<ast_type_traits::DynTypedNode>(
    const ast_type_traits::DynTypedNode &Node) {
  DynTypedNode NewNode;
  NewNode = Node;
  return NewNode;
}

template <typename T> DynTypedNode DynTypedNode::create(const T &Node) {
  return BaseConverter<T>::create(Node);
}

template <typename T>
struct DynTypedNode::BaseConverter<
    T, typename std::enable_if<std::is_base_of<Decl, T>::value>::type>
    : public DynCastPtrConverter<T, Decl> {};

template <typename T>
struct DynTypedNode::BaseConverter<
    T, typename std::enable_if<std::is_base_of<Stmt, T>::value>::type>
    : public DynCastPtrConverter<T, Stmt> {};

template <typename T>
struct DynTypedNode::BaseConverter<
    T, typename std::enable_if<std::is_base_of<Type, T>::value>::type>
    : public DynCastPtrConverter<T, Type> {};

template <>
struct DynTypedNode::BaseConverter<NestedNameSpecifier, void>
    : public PtrConverter<NestedNameSpecifier> {};

template <>
struct DynTypedNode::BaseConverter<CXXCtorInitializer, void>
    : public PtrConverter<CXXCtorInitializer> {};

template <>
struct DynTypedNode::BaseConverter<TemplateArgument, void>
    : public ValueConverter<TemplateArgument> {};

template <>
struct DynTypedNode::BaseConverter<TemplateName, void>
    : public ValueConverter<TemplateName> {};

template <>
struct DynTypedNode::BaseConverter<NestedNameSpecifierLoc, void>
    : public ValueConverter<NestedNameSpecifierLoc> {};

template <>
struct DynTypedNode::BaseConverter<QualType, void>
    : public ValueConverter<QualType> {};

template <>
struct DynTypedNode::BaseConverter<TypeLoc, void>
    : public ValueConverter<TypeLoc> {};

template <>
struct DynTypedNode::BaseConverter<ExplodedNode, void>
    : public PtrConverter<ExplodedNode> {};

template <>
struct DynTypedNode::BaseConverter<ExplodedGraph, void>
    : public PtrConverter<ExplodedGraph> {};

template <>
struct DynTypedNode::BaseConverter<ProgramState, void>
    : public PtrConverter<ProgramState> {};

template <typename T>
struct DynTypedNode::BaseConverter<
    T, typename std::enable_if<std::is_base_of<SVal, T>::value>::type>
    : public DynCastValueConverter<T, SVal> {};

template <typename T>
struct DynTypedNode::BaseConverter<
    T, typename std::enable_if<std::is_base_of<ProgramPoint, T>::value>::type>
    : public DynCastValueConverter<T, ProgramPoint> {};

template <typename T>
struct DynTypedNode::BaseConverter<
    T, typename std::enable_if<std::is_base_of<MemRegion, T>::value>::type>
    : public DynCastPtrConverter<T, MemRegion> {};

template <typename T>
struct DynTypedNode::BaseConverter<
    T, typename std::enable_if<std::is_base_of<SymExpr, T>::value>::type>
    : public DynCastPtrConverter<T, SymExpr> {};

template <typename T>
struct DynTypedNode::BaseConverter<
    T,
    typename std::enable_if<std::is_base_of<LocationContext, T>::value>::type>
    : public DynCastPtrConverter<T, LocationContext> {};

// The only operation we allow on unsupported types is \c get.
// This allows to conveniently use \c DynTypedNode when having an arbitrary
// AST node that is not supported, but prevents misuse - a user cannot create
// a DynTypedNode from arbitrary types.
template <typename T, typename EnablerT> struct DynTypedNode::BaseConverter {
  static const T *get(ASTGraphNodeKind NodeKind, const char Storage[]) {
    return nullptr;
  }
};

} // end namespace ast_graph_type_traits
} // end namespace ento
} // end namespace clang

namespace llvm {

template <>
struct DenseMapInfo<clang::ento::ast_graph_type_traits::ASTGraphNodeKind>
    : clang::ento::ast_graph_type_traits::ASTGraphNodeKind::DenseMapInfo {};

template <>
struct DenseMapInfo<clang::ento::ast_graph_type_traits::DynTypedNode>
    : clang::ento::ast_graph_type_traits::ASTGraphNodeKind::DenseMapInfo {};

} // end namespace llvm

#endif // LLVM_CLANG_AST_ASTGRAPHTYPETRAITS_H
