import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM Issue #240711: `Missed optimization about difference between sext(x) and sext(x + C)`
https://github.com/llvm/llvm-project/issues/240711
Alive2: https://alive2.llvm.org/ce/z/DnQuNQ
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem issue_240711 :
    [llvm-definition|
      define i64 @f(i32 %x) {
      entry:
        %ext = sext i32 %x to i64
        %plus = add nsw i32 %x, 1
        %extplus = sext i32 %plus to i64
        %s0 = sub nsw i64 %ext, %extplus
        ret i64 %s0
      }
    ] ⊒ [llvm-definition|
      define i64 @f(i32 %x) {
      entry:
        ret i64 -1
      }
    ] := by
  llvm_refine
  rename_i x
  intro h _
  have hx := x.le_toInt; have hx2 := x.toInt_lt
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.saddOverflow] at h
  simp [BitVec.toInt_sub, BitVec.toInt_signExtend, BitVec.toInt_add, Int.bmod_def]
  omega

end LeanNanoLlvm.Tests.Alive2
