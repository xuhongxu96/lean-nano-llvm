import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem switch_const_match :
    [llvm-definition|
      define i32 @f() {
      entry:
        switch i32 1, label %dflt [i32 0, label %l0 i32 1, label %l1]
      l0:
        ret i32 10
      l1:
        ret i32 20
      dflt:
        ret i32 30
      }
    ] ⊒ [llvm-definition|
      define i32 @f() {
      entry:
        ret i32 20
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
