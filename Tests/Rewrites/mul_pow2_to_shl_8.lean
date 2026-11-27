import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem mul_pow2_to_shl_8 :
    [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %r = mul i32 %x, 8
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %r = shl i32 %x, 3
        ret i32 %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
