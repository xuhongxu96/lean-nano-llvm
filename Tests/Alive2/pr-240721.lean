import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM PR #240721: `[InstCombine] fold sext(x) - sext(x +nsw C) to -sext(C)`
https://github.com/llvm/llvm-project/pull/240721
Alive2: https://alive2.llvm.org/ce/z/8KSNP3
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem pr_240721 :
    [llvm-definition|
      define i64 @f(i32 %x, i32 %C) {
      entry:
        %ext = sext i32 %x to i64
        %plus = add nsw i32 %x, %C
        %extplus = sext i32 %plus to i64
        %s0 = sub nsw i64 %ext, %extplus
        ret i64 %s0
      }
    ] ⊒ [llvm-definition|
      define i64 @f(i32 %x, i32 %C) {
      entry:
        %ext = sext i32 %C to i64
        %negext = sub i64 0, %ext
        ret i64 %negext
      }
    ] := by
  llvm_refine
  rename_i x c
  intro h _
  have hx := x.le_toInt; have hx2 := x.toInt_lt
  have hc := c.le_toInt; have hc2 := c.toInt_lt
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.saddOverflow] at h
  simp [BitVec.toInt_sub, BitVec.toInt_signExtend, BitVec.toInt_add, BitVec.toInt_neg, Int.bmod_def]
  omega

end LeanNanoLlvm.Tests.Alive2
