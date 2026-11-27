import LeanNanoLlvm.Refinement.PoisonElim
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
  -- `llvm_bv` removes the poison and `select` case structure. Two `BitVec` goals remain, one per
  -- `select` arm; the `nsw` guard of the `add` arm appears as the hypothesis `h_1`.
  llvm_bv
  · -- h : arg0 &&& 64#32 = 0#32 ⊢ arg0 ||| 64#32 = arg0 ^^^ 64#32
    ext i hi
    have h0 := congrArg (fun v : BitVec 32 => v[i]'hi) h
    simp at h0 ⊢; grind
  · -- h : ¬arg0 &&& 64#32 = 0#32, h_1 : arg0.saddOverflow 4294967232#32 = false
    -- ⊢ arg0 + 4294967232#32 = arg0 ^^^ 64#32
    have hbit : arg0 &&& 64#32 = 64#32 := by
      ext i hi
      by_cases h6 : i = 6
      · subst h6
        cases hx6 : arg0[6]
        · exfalso; apply h; ext j hj
          by_cases hj6 : j = 6
          · subst hj6; simp [hx6]
          · simp [show (64#32)[j]'hj = false by revert j hj hj6; decide]
        · simp [hx6]
      · simp [show (64#32)[i]'hi = false by revert i hi h6; decide]
    have hx : (arg0 ^^^ 64#32) &&& 64#32 = 0#32 := by
      ext i hi
      have h6 := congrArg (fun v : BitVec 32 => v[i]'hi) hbit
      simp at h6 ⊢; grind
    have hadd : (arg0 ^^^ 64#32) + 64#32 = arg0 := by
      have hor : (arg0 ^^^ 64#32) ||| 64#32 = arg0 := by
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
