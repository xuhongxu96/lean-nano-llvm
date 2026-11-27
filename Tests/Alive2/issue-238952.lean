import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM Issue #238952: `[InstCombine] Missed unsigned division elimination for a zero-extended divisor`
https://github.com/llvm/llvm-project/issues/238952
Alive2: https://alive2.llvm.org/ce/z/vdnMOu
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem issue_238952 :
    [llvm-definition|
      define i1 @f(i32 %a, i16 %y) {
      entry:
        %b = zext i16 %y to i32
        %d = udiv i32 %a, %b
        %c = icmp ugt i32 %d, 1
        ret i1 %c
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i32 %a, i16 %y) {
      entry:
        %b = zext i16 %y to i32
        %t = shl i32 %b, 1
        %c = icmp uge i32 %a, %t
        ret i1 %c
      }
    ] := by
  llvm_refine
  rename_i a y
  have hy0 : 0 < y.toNat := by
    have : y.toNat ≠ 0 := by
      intro h0; apply h_ite_sym; apply BitVec.eq_of_toNat_eq; simp [h0]
    omega
  have hylt := y.isLt
  simp only [BitVec.lt_def, BitVec.le_def, BitVec.toNat_udiv, BitVec.toNat_shiftLeft,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ 32),
      Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega : y.toNat * 2 ^ 1 < 2 ^ 32)]
  rw [Nat.lt_div_iff_mul_lt hy0]; omega

end LeanNanoLlvm.Tests.Alive2
