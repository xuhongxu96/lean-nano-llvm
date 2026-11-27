import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM PR #230796: `[InstCombine] fold ((X + C) & ~C) - X -> X & C where C is a power of 2`
https://github.com/llvm/llvm-project/pull/230796

Instantiated with `C = 8` (`~C = -9`) on `i32`.
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

private theorem pr_230796_disj : ∀ j : Fin 32, ((4294967287#32)[j.val] && (8#32)[j.val]) = false := by decide
private theorem pr_230796_cov : ∀ j : Fin 32, ((4294967287#32)[j.val] || (8#32)[j.val]) = true := by decide

theorem pr_230796 :
    [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %a = add i32 %x, 8
        %m = and i32 %a, -9
        %r = sub i32 %m, %x
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %r = and i32 %x, 8
        ret i32 %r
      }
    ] := by
  llvm_refine
  rename_i x
  have h1 : (x &&& 8#32) = if x[3] = true then 8#32 else 0#32 := by
    ext i hi
    simp only [BitVec.getElem_and]
    by_cases h3 : i = 3
    · subst h3; split <;> simp_all
    · have : (8#32)[i] = false := by revert i hi h3; decide
      split <;> simp [this]
  have h2 : ((x + 8#32) &&& 4294967287#32) = if x[3] = true then x + 8#32 else x := by
    have hsplit : ∀ y : BitVec 32, (y &&& 4294967287#32) + (y &&& 8#32) = y := by
      intro y
      have hdisj : (y &&& 4294967287#32) &&& (y &&& 8#32) = 0#32 := by
        ext i hi
        have hz := pr_230796_disj ⟨i, hi⟩
        simp only [BitVec.getElem_and, BitVec.getElem_zero]; grind
      rw [BitVec.add_eq_or_of_and_eq_zero _ _ hdisj]
      ext i hi
      have ho := pr_230796_cov ⟨i, hi⟩
      simp only [BitVec.getElem_or, BitVec.getElem_and]; grind
    have hbit : (x + 8#32)[3] = !x[3] := by
      simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
      have hx := x.isLt
      have h8 : (8 % 2 ^ 32 : Nat) = 8 := by omega
      have hdiv : ((x.toNat + 8) % 2 ^ 32) / 2 ^ 3 % 2 = (x.toNat / 2 ^ 3 + 1) % 2 := by omega
      rw [h8, hdiv]
      cases h : ((x.toNat / 2 ^ 3) % 2 == 0) <;> simp_all <;> omega
    have hadd8 : ((x + 8#32) &&& 8#32) = if x[3] = true then 0#32 else 8#32 := by
      ext i hi
      simp only [BitVec.getElem_and]
      by_cases h3 : i = 3
      · subst h3; rw [hbit]; split <;> simp_all
      · have : (8#32)[i] = false := by revert i hi h3; decide
        split <;> simp [this]
    have hs := hsplit (x + 8#32)
    rw [hadd8] at hs
    by_cases h3 : x[3] = true <;> simp only [h3, ↓reduceIte] at hs ⊢ <;> grind
  rw [h1, h2]; by_cases h3 : x[3] = true <;> simp only [h3, ↓reduceIte] <;> grind

end LeanNanoLlvm.Tests.Alive2
