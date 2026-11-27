import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM Issue #244086: `[InstCombine] Missed fold: sdiv (mul X, X+1), 2 -> ashr (mul X, X+1), 1`
https://github.com/llvm/llvm-project/issues/244086

Since `x` and `x + 1` are consecutive integers, `x * (x + 1)` is always even, so signed
division by `2` equals arithmetic right shift by `1`.
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem issue_244086 :
    [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %a = add i32 %x, 1
        %m = mul i32 %a, %x
        %d = sdiv i32 %m, 2
        ret i32 %d
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %a = add i32 %x, 1
        %m = mul i32 %a, %x
        %d = ashr i32 %m, 1
        ret i32 %d
      }
    ] := by
  llvm_refine
  have heven : ((arg0 + 1#32) * arg0).toNat % 2 = 0 := by
    simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat]
    have : arg0.toNat % 2 = 0 ∨ arg0.toNat % 2 = 1 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, Nat.add_mod, h]
  generalize hm : (arg0 + 1#32) * arg0 = m at heven ⊢
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sdiv_of_ne_or_ne m 2#32 (Or.inr (by decide)), BitVec.toInt_sshiftRight]
  have h2 : (2 : Int) ∣ m.toInt := by
    rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
  rw [show (2#32).toInt = 2 by rfl, Int.tdiv_eq_ediv_of_dvd h2, Int.shiftRight_eq_div_pow]
  rfl

end LeanNanoLlvm.Tests.Alive2
