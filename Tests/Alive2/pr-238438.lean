import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

-- LLVM PR #238438: `[KnownBits] Improve multiplication bounds for negative operands`
-- https://github.com/llvm/llvm-project/pull/238438
-- Alive2: https://alive2.llvm.org/ce/z/ZqV8g3

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem pr_238438_mixed_sign_mul_i8 :
    [llvm-definition|
      define i8 @f(i8 %a, i8 %b) {
      entry:
        %x = or i8 %a, -16
        %t = and i8 %b, 7
        %y = or i8 %t, 1
        %m0 = mul i8 %x, %y
        %r = or i8 %m0, 127
        ret i8 %r
      }
    ] ⊒ [llvm-definition|
      define i8 @f(i8 %a, i8 %b) {
      entry:
        ret i8 -1
      }
    ] := by
  llvm_refine
  rename_i a b
  have hx : 240 ≤ (a ||| 240#8).toNat := by
    rw [BitVec.toNat_or]; exact Nat.right_le_or
  have hy_lo : 1 ≤ (b &&& 7#8 ||| 1#8).toNat := by
    rw [BitVec.toNat_or]; exact Nat.right_le_or
  have hy_hi : (b &&& 7#8 ||| 1#8).toNat ≤ 7 := by
    have h1 : (b &&& 7#8).toNat ≤ 7 := by rw [BitVec.toNat_and]; exact Nat.and_le_right
    have h2 : (b &&& 7#8 ||| 1#8).toNat < 8 := by
      rw [BitVec.toNat_or]
      exact Nat.or_lt_two_pow (n := 3) (by omega) (by decide)
    omega
  have hx_lt := (a ||| 240#8).isLt
  have hprod : 128 ≤ ((a ||| 240#8) * (b &&& 7#8 ||| 1#8)).toNat := by
    rw [BitVec.toNat_mul]
    let u := 256 - (a ||| 240#8).toNat
    let v := (b &&& 7#8 ||| 1#8).toNat
    have huv : 1 ≤ u * v ∧ u * v ≤ 112 :=
      ⟨Nat.mul_pos (by omega) (by omega), Nat.mul_le_mul (show u ≤ 16 by omega) hy_hi⟩
    have heq : (a ||| 240#8).toNat * v = (v - 1) * 256 + (256 - u * v) := by
      have h1 : (a ||| 240#8).toNat = 256 - u := by omega
      rw [h1, Nat.sub_mul]
      have h2 : 256 * v = (v - 1) * 256 + 256 := by
        cases hv : v with
        | zero => omega
        | succ k => rw [Nat.mul_succ, Nat.add_sub_cancel, Nat.mul_comm]
      omega
    rw [heq, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    omega
  generalize (a ||| 240#8) * (b &&& 7#8 ||| 1#8) = p at hprod ⊢
  have hmsb : p[7] = true := by
    rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
    have hlt := p.isLt
    simp; omega
  ext i hi
  by_cases h7 : i = 7
  · subst h7; simp [hmsb]
  · simp [show (127#8)[i]'hi = true by revert i hi h7; decide,
          show (255#8)[i]'hi = true by revert i hi; decide]

end LeanNanoLlvm.Tests.Alive2
