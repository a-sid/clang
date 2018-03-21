add_subdirectory(Dynamic)

set(LLVM_LINK_COMPONENTS support)

add_clang_library(clangASTMatchers
  ASTGraphTypeTraits.cpp
  ASTMatchFinder.cpp
  ASTMatchersInternal.cpp

  LINK_LIBS
  clangAST
  clangBasic
  )
