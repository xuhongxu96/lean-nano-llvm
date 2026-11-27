import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM PR #242353: `[InstCombine] Fold icmp of add of mul nuw when no multiple is in range`
https://github.com/llvm/llvm-project/pull/242353
Alive2: https://alive2.llvm.org/ce/z/g3oxsD
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem pr_242353_i32 :
    [llvm-definition|
      define i1 @f(i32 %x) {
      entry:
        %m0 = mul nuw i32 %x, 13
        %a0 = add i32 %m0, -1
        %cmp = icmp ult i32 %a0, 7
        ret i1 %cmp
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i32 %x) {
      entry:
        ret i1 false
      }
    ] := by
  llvm_intro; llvm_symexec
  apply RegisterValue.isRefinedBy_bv_of_poisonOr
  cases arg0
  · simp [simp_llvm]
  · rename_i x; simp [simp_llvm]
    intro hnuw
    have hmul : x.toNat * 13 < 2 ^ 32 := by
      simpa [BitVec.umulOverflow] using hnuw
    rw [show (4294967295#32 : BitVec 32) = -(1#32) by decide, ← BitVec.sub_eq_add_neg]
    by_cases h0 : x = 0#32
    · rw [h0]; decide
    · have hx0 : 0 < x.toNat := by
        have : x.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
        omega
      have hge : 1#32 ≤ x * 13#32 := by
        simp only [BitVec.le_def, BitVec.toNat_mul, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega : 13 < 2 ^ 32), Nat.mod_eq_of_lt hmul,
            Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 32)]
        omega
      rw [BitVec.le_def, BitVec.toNat_sub_of_le hge, BitVec.toNat_mul]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : 13 < 2 ^ 32), Nat.mod_eq_of_lt hmul,
          Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 32), Nat.mod_eq_of_lt (by omega : 7 < 2 ^ 32)]
      omega

theorem pr_242353_inverse :
    [llvm-definition|
      define i1 @f(i8 %x) {
      entry:
        %m0 = mul nuw i8 %x, 13
        %a0 = add i8 %m0, -1
        %cmp = icmp ugt i8 %a0, 6
        ret i1 %cmp
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i8 %x) {
      entry:
        ret i1 true
      }
    ] := by
  llvm_intro; llvm_symexec
  apply RegisterValue.isRefinedBy_bv_of_poisonOr
  cases arg0
  · simp [simp_llvm]
  · rename_i x; simp [simp_llvm]
    revert x; decide

end LeanNanoLlvm.Tests.Alive2
