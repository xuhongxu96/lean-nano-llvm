import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem abs_neg_nsw (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x) {
      entry:
        %nx = sub nsw i$(w) 0, %x
        %nnx = sub nsw i$(w) 0, %nx
        %c = icmp slt i$(w) %nx, 0
        %r = select i1 %c, i$(w) %nnx, i$(w) %nx
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x) {
      entry:
        %nx = sub nsw i$(w) 0, %x
        %c = icmp slt i$(w) %x, 0
        %r = select i1 %c, i$(w) %nx, i$(w) %x
        ret i$(w) %r
      }
    ] := by
  llvm_refine
  · have hsub := BitVec.toInt_sub_of_not_ssubOverflow ‹_›
    simp only [BitVec.zero_sub, BitVec.toInt_zero, Int.zero_sub] at hsub
    apply BitVec.eq_of_toInt_eq
    simp [BitVec.slt, hsub] at *; subst_vars; simp [bitvec_ofBool_eq_zero] at *; omega
  · intro _ _; have hsub := BitVec.toInt_sub_of_not_ssubOverflow ‹_›
    simp only [BitVec.zero_sub, BitVec.toInt_zero, Int.zero_sub] at hsub
    apply BitVec.eq_of_toInt_eq
    simp [BitVec.slt, hsub] at *; subst_vars; simp [bitvec_ofBool_eq_zero] at *; omega

end LeanNanoLlvm.Tests.Rewrites
