import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM PR #230791: `[InstCombine] fold (A | -2) + A -> (A - 1) & -2`
https://github.com/llvm/llvm-project/pull/230791
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

private theorem pr_230791_hi1 : ∀ j : Fin 31, (4294967294#32)[j.val + 1] = true := by decide
private theorem pr_230791_hi2 : ∀ j : Fin 31, (4294967295#32)[j.val + 1] = true := by decide
private theorem pr_230791_disj : ∀ j : Fin 32, ((4294967294#32)[j.val] && (1#32)[j.val]) = false := by decide
private theorem pr_230791_cov : ∀ j : Fin 32, ((4294967294#32)[j.val] || (1#32)[j.val]) = true := by decide

theorem pr_230791 :
    [llvm-definition|
      define i32 @f(i32 %a) {
      entry:
        %o = or i32 %a, -2
        %r = add i32 %o, %a
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %a) {
      entry:
        %s = sub i32 %a, 1
        %r = and i32 %s, -2
        ret i32 %r
      }
    ] := by
  llvm_refine
  have h1 : arg0 ||| 4294967294#32 = if arg0.toNat % 2 = 0 then 4294967294#32 else 4294967295#32 := by
    ext i hi
    cases i with
    | zero =>
      simp only [BitVec.getElem_eq_testBit_toNat, Nat.testBit_zero]
      split <;> simp_all
    | succ k =>
      have hk1 := pr_230791_hi1 ⟨k, by omega⟩
      have hk2 := pr_230791_hi2 ⟨k, by omega⟩
      split <;> simp [hk1, hk2]
  have h2 : (arg0 - 1#32) &&& 4294967294#32 = if arg0.toNat % 2 = 0 then arg0 - 2#32 else arg0 - 1#32 := by
    have hand : ∀ x : BitVec 32, (x &&& 4294967294#32) + (x &&& 1#32) = x := by
      intro x
      have hdisj : (x &&& 4294967294#32) &&& (x &&& 1#32) = 0#32 := by
        ext i hi
        have hz := pr_230791_disj ⟨i, hi⟩
        simp only [BitVec.getElem_and, BitVec.getElem_zero]; grind
      rw [BitVec.add_eq_or_of_and_eq_zero _ _ hdisj]
      ext i hi
      have ho := pr_230791_cov ⟨i, hi⟩
      simp only [BitVec.getElem_or, BitVec.getElem_and]; grind
    have hbit : ((arg0 - 1#32) &&& 1#32) = if arg0.toNat % 2 = 0 then 1#32 else 0#32 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, show (1#32).toNat = 2 ^ 1 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
      split <;> bv_omega
    have hs := hand (arg0 - 1#32)
    rw [hbit] at hs
    by_cases hp : arg0.toNat % 2 = 0 <;> simp only [hp, ↓reduceIte] at hs ⊢ <;> grind
  rw [h1, h2]
  split <;> (apply BitVec.eq_of_toNat_eq; bv_omega)

end LeanNanoLlvm.Tests.Alive2
