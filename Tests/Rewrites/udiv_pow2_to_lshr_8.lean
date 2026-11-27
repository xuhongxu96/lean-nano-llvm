import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem udiv_pow2_to_lshr_8 :
    [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %r = udiv i32 %x, 8
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %r = lshr i32 %x, 3
        ret i32 %r
      }
    ] := by
  llvm_refine
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

end LeanNanoLlvm.Tests.Rewrites
