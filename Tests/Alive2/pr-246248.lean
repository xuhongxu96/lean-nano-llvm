import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import Tests.Rewrites.Common

/-!
# LLVM PR #246248: `[InstCombine] fold X & C ? (X - C) : (X | C) into X ^ C`
https://github.com/llvm/llvm-project/pull/246248
Alive2: https://alive2.llvm.org/ce/z/PL3XEf
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open LeanNanoLlvm.Tests.Rewrites
open scoped LeanNanoLlvm.AST.Syntax

theorem pr_246248 :
    [llvm-definition|
      define i32 @f(i32 %arg0) {
      entry:
        %v0 = and i32 %arg0, 64
        %v1 = icmp eq i32 %v0, 0
        %v2 = or disjoint i32 %arg0, 64
        %v3 = add nsw i32 %arg0, -64
        %v4 = select i1 %v1, i32 %v2, i32 %v3
        ret i32 %v4
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %arg0) {
      entry:
        %v4_opt = xor i32 %arg0, 64
        ret i32 %v4_opt
      }
    ] := by
  llvm_intro; llvm_symexec
  apply RegisterValue.isRefinedBy_bv_of_poisonOr
  cases arg0
  · simp [simp_llvm]
  · rename_i x; simp [simp_llvm]
    split
    · rename_i heq
      simp only [PoisonOr.IsRefinedBy]
      ext i hi
      have h0 := congrArg (fun v : BitVec 32 => v[i]'hi) heq
      simp at h0 ⊢; grind
    · rename_i hne
      split
      · simp [PoisonOr.IsRefinedBy]
      · simp only [PoisonOr.IsRefinedBy]
        have hbit : x &&& 64#32 = 64#32 := by
          ext i hi
          by_cases h6 : i = 6
          · subst h6
            cases hx6 : x[6]
            · exfalso; apply hne; ext j hj
              by_cases hj6 : j = 6
              · subst hj6; simp [hx6]
              · simp [show (64#32)[j]'hj = false by revert j hj hj6; decide]
            · simp [hx6]
          · simp [show (64#32)[i]'hi = false by revert i hi h6; decide]
        have hx : (x ^^^ 64#32) &&& 64#32 = 0#32 := by
          ext i hi
          have h6 := congrArg (fun v : BitVec 32 => v[i]'hi) hbit
          simp at h6 ⊢; grind
        have hadd : (x ^^^ 64#32) + 64#32 = x := by
          have hor : (x ^^^ 64#32) ||| 64#32 = x := by
            ext i hi
            have h6 := congrArg (fun v : BitVec 32 => v[i]'hi) hbit
            simp at h6 ⊢; grind
          rw [bv_or_eq_add_sub_and, hx, BitVec.sub_zero] at hor
          exact hor
        have hsub : (4294967232#32 : BitVec 32) = -(64#32) := by decide
        rw [hsub, ← BitVec.sub_eq_add_neg]
        have hres := congrArg (· - 64#32) hadd.symm
        simpa [BitVec.add_sub_cancel] using hres

end LeanNanoLlvm.Tests.Alive2
