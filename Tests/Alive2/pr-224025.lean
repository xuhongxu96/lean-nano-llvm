import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM PR #224025: `[InstCombine] Fold -X / -Y to X / Y when it cannot overflow`
https://github.com/llvm/llvm-project/pull/224025

With `sub nsw 0, %x` and non-`-1` divisor (`-3`), `(-x) /s (-3) = x /s 3`.
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem pr_224025 :
    [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %nx = sub nsw i32 0, %x
        %r = sdiv i32 %nx, -3
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %r = sdiv i32 %x, 3
        ret i32 %r
      }
    ] := by
  llvm_refine
  have hx := BitVec.toInt_sub_of_not_ssubOverflow (x := 0#32) (y := arg0) ‹_›
  simp only [BitVec.zero_sub, BitVec.toInt_zero, Int.zero_sub] at hx
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sdiv_of_ne_or_ne (-arg0) 4294967293#32 (Or.inr (by decide)),
      BitVec.toInt_sdiv_of_ne_or_ne arg0 3#32 (Or.inr (by decide)), hx,
      show (4294967293#32).toInt = -3 by rfl, show (3#32).toInt = 3 by rfl,
      Int.neg_tdiv, Int.tdiv_neg, Int.neg_neg]

end LeanNanoLlvm.Tests.Alive2
