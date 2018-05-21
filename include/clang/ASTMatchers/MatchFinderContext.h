//===--- MatchFinderContext.h -----------------------------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  Provides a basic class for accessors that can be used by ASTMatchFinder.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_ENTO_MATCHERS_MATCHFINDERCONTEXT_H
#define LLVM_CLANG_ENTO_MATCHERS_MATCHFINDERCONTEXT_H

#include "clang/ASTMatchers/ASTGraphTypeTraits.h"

namespace clang {

namespace ast_matchers {

namespace internal {

class MatchFinderContext {
public:
  virtual ento::ast_graph_type_traits::DynTypedNode
  getBoundNode(StringRef ID) = 0;
  virtual ~MatchFinderContext() = default;
};

} // end namespace internal
} // end namespace ast_matchers
} // end namepace clang

#endif // LLVM_CLANG_ENTO_MATCHERS_MATCHFINDERCONTEXT_H
