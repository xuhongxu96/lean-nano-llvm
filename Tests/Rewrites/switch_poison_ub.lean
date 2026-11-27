import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem switch_poison_ub :
    [llvm-definition|
      define i32 @f() {
      entry:
        switch i32 poison, label %dflt [i32 0, label %l0]
      l0:
        ret i32 10
      dflt:
        ret i32 30
      }
    ] ⊒ [llvm-definition|
      define i32 @f() {
      entry:
        ret i32 42
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
