import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem icmp_slt_sub_nsw_cancel (w : Nat) :
    [llvm-definition|
      define i1 @f(i$(w) %x, i$(w) %y, i$(w) %c) {
      entry:
        %a = sub nsw i$(w) %x, %c
        %b = sub nsw i$(w) %y, %c
        %r = icmp slt i$(w) %a, %b
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i$(w) %x, i$(w) %y, i$(w) %c) {
      entry:
        %r = icmp slt i$(w) %x, %y
        ret i1 %r
      }
    ] := by
  llvm_refine
  intro h1 h2; simp_all [BitVec.slt, BitVec.toInt_sub_of_not_ssubOverflow, -BitVec.toInt_sub]

end LeanNanoLlvm.Tests.Rewrites
