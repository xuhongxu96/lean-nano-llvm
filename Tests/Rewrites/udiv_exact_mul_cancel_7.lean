import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem udiv_exact_mul_cancel_7 :
    [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %a = udiv exact i32 %x, 7
        %r = mul i32 %a, 7
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        ret i32 %x
      }
    ] := by
  llvm_refine
  intro h; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_eq] at h; simp; omega

end LeanNanoLlvm.Tests.Rewrites
