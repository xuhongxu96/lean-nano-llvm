import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

-- LLVM PR #237549: `[InstCombine] Fold guarded comparisons of OR/XOR`
-- https://github.com/llvm/llvm-project/pull/237549
-- Alive2: https://alive2.llvm.org/ce/z/2tGc-W

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem pr_237549 :
    [llvm-definition|
      define i1 @f(i32 %a, i32 %b) {
      entry:
        %guard = icmp ult i32 %a, 19
        %bits = xor i32 %a, %b
        %test = icmp ule i32 %bits, 4863
        %result = and i1 %guard, %test
        ret i1 %result
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i32 %a, i32 %b) {
      entry:
        %guard = icmp ult i32 %a, 19
        %test = icmp ule i32 %b, 4863
        %result = and i1 %guard, %test
        ret i1 %result
      }
    ] := by
  llvm_refine
  rename_i a b
  rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> rintro ⟨ha, hle⟩ <;> refine ⟨ha, ?_⟩
  all_goals
    have ha32 : a.toNat < 32 := by
      have : a.toNat < 19 := by simpa [BitVec.lt_def] using ha
      omega
    have ha_hi : a >>> 5 = 0#32 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
      omega
    have hshr : (a ^^^ b) >>> 5 = b >>> 5 := by
      have hdist : (a ^^^ b) >>> 5 = (a >>> 5) ^^^ (b >>> 5) := by
        ext i hi; by_cases h : i + 5 < 32 <;> simp
      rw [hdist, ha_hi, BitVec.zero_xor]
    have hto := congrArg BitVec.toNat hshr
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hto
    simp only [BitVec.le_def, BitVec.toNat_ofNat] at hle ⊢
    omega

end LeanNanoLlvm.Tests.Alive2
