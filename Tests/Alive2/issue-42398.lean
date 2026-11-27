import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM Issue #42398: `[InstCombine] fold clamp of 2-value range`
https://github.com/llvm/llvm-project/issues/42398

`smax(smin(x, C1), C1 - 1) -> zext(x >s C1 - 1) + (C1 - 1)` (instantiated with `C1 = 10, C2 = 9`).
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem issue_42398 :
    [llvm-definition|
      define i32 @f(i32 %num) {
      entry:
        %cmp1 = icmp slt i32 %num, 10
        %s1 = select i1 %cmp1, i32 %num, i32 10
        %cmp2 = icmp sgt i32 %s1, 9
        %r = select i1 %cmp2, i32 %s1, i32 9
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %num) {
      entry:
        %cmp3 = icmp sgt i32 %num, 9
        %z = zext i1 %cmp3 to i32
        %r = add i32 %z, 9
        ret i32 %r
      }
    ] := by
  llvm_refine
  by_cases h9 : 9 < arg0.toInt <;> (repeat' split) <;> simp_all [BitVec.slt] <;>
    (apply BitVec.eq_of_toInt_eq; by_cases h9' : 9 < arg0.toInt <;> simp [h9'] <;> omega)

end LeanNanoLlvm.Tests.Alive2
