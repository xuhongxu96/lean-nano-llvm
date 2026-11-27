import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem icmp_ult_sub_nuw_cancel (w : Nat) :
    [llvm-definition|
      define i1 @f(i$(w) %x, i$(w) %y, i$(w) %c) {
      entry:
        %a = sub nuw i$(w) %x, %c
        %b = sub nuw i$(w) %y, %c
        %r = icmp ult i$(w) %a, %b
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i$(w) %x, i$(w) %y, i$(w) %c) {
      entry:
        %r = icmp ult i$(w) %x, %y
        ret i1 %r
      }
    ] := by
  llvm_refine
  simp_all [BitVec.lt_def, BitVec.usubOverflow, BitVec.toNat_sub_of_not_usubOverflow, -BitVec.toNat_sub]; omega

end LeanNanoLlvm.Tests.Rewrites
