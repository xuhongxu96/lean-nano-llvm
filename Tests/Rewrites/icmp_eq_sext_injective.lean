import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem icmp_eq_sext_injective :
    [llvm-definition|
      define i1 @f(i8 %x, i8 %y) {
      entry:
        %ex = sext i8 %x to i32
        %ey = sext i8 %y to i32
        %r = icmp eq i32 %ex, %ey
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i8 %x, i8 %y) {
      entry:
        %r = icmp eq i8 %x, %y
        ret i1 %r
      }
    ] := by
  llvm_refine
  rw [Bool.eq_iff_iff]; simp; constructor <;> intro h
  · ext i hi; have hbit := congrArg (·[i]) h; simp [BitVec.getElem_signExtend, hi] at hbit; exact hbit
  · subst h; rfl

end LeanNanoLlvm.Tests.Rewrites
