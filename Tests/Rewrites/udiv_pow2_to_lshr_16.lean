import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem udiv_pow2_to_lshr_16 :
    [llvm-definition|
      define i64 @f(i64 %x) {
      entry:
        %r = udiv i64 %x, 16
        ret i64 %r
      }
    ] ⊒ [llvm-definition|
      define i64 @f(i64 %x) {
      entry:
        %r = lshr i64 %x, 4
        ret i64 %r
      }
    ] := by
  llvm_refine
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

end LeanNanoLlvm.Tests.Rewrites
