import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem icmp_sgt_add_nsw_pos :
    [llvm-definition|
      define i1 @f(i32 %x) {
      entry:
        %a = add nsw i32 %x, 5
        %r = icmp sgt i32 %a, %x
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i32 %x) {
      entry:
        ret i1 true
      }
    ] := by
  llvm_refine
  intro h; simp_all [BitVec.slt, BitVec.toInt_add_of_not_saddOverflow, -BitVec.toInt_add]; omega

end LeanNanoLlvm.Tests.Rewrites
