set(LLVM_LINK_COMPONENTS support)

add_clang_library(clangStaticAnalyzerMatchers
  GraphMatchFinder.cpp
  GraphMatcherInternals.cpp
  
  LINK_LIBS
  clangAST
  clangASTMatchers
  clangAnalysis
  clangBasic
  clangLex
  clangRewrite
  clangStaticAnalyzerCore
  ${Z3_LINK_FILES}
  )
