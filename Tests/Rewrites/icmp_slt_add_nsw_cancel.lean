import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem icmp_slt_add_nsw_cancel (w : Nat) :
    [llvm-definition|
      define i1 @f(i$(w) %x, i$(w) %y, i$(w) %c) {
      entry:
        %a = add nsw i$(w) %x, %c
        %b = add nsw i$(w) %y, %c
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
  simp_all [BitVec.slt, BitVec.toInt_add_of_not_saddOverflow, -BitVec.toInt_add]

end LeanNanoLlvm.Tests.Rewrites
