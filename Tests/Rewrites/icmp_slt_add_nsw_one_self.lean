import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem icmp_slt_add_nsw_one_self :
    [llvm-definition|
      define i1 @f(i32 %x) {
      entry:
        %a = add nsw i32 %x, 1
        %r = icmp slt i32 %a, %x
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i32 %x) {
      entry:
        ret i1 false
      }
    ] := by
  llvm_refine
  simp_all [BitVec.slt, BitVec.toInt_add_of_not_saddOverflow, -BitVec.toInt_add]; omega

end LeanNanoLlvm.Tests.Rewrites
