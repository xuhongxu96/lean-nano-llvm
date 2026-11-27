import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem mul_pow2_to_shl_16 :
    [llvm-definition|
      define i64 @f(i64 %x) {
      entry:
        %r = mul i64 %x, 16
        ret i64 %r
      }
    ] ⊒ [llvm-definition|
      define i64 @f(i64 %x) {
      entry:
        %r = shl i64 %x, 4
        ret i64 %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
