import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem abs_nonneg_nsw (w : Nat) :
    [llvm-definition|
      define i1 @f(i$(w) %x) {
      entry:
        %neg = sub nsw i$(w) 0, %x
        %c = icmp slt i$(w) %x, 0
        %abs = select i1 %c, i$(w) %neg, i$(w) %x
        %r = icmp sge i$(w) %abs, 0
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i$(w) %x) {
      entry:
        ret i1 true
      }
    ] := by
  llvm_refine
  have hsub := BitVec.toInt_sub_of_not_ssubOverflow (x := 0#w) (y := arg0) (by simp_all)
  simp [BitVec.slt, BitVec.sle] at *; omega

end LeanNanoLlvm.Tests.Rewrites
