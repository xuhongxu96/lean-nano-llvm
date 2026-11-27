import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem icmp_ult_sub_nuw_one_self :
    [llvm-definition|
      define i1 @f(i32 %x) {
      entry:
        %a = sub nuw i32 %x, 1
        %r = icmp ult i32 %a, %x
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i32 %x) {
      entry:
        ret i1 true
      }
    ] := by
  llvm_refine
  intro h; simp_all [BitVec.lt_def, BitVec.usubOverflow, BitVec.toNat_sub_of_not_usubOverflow, -BitVec.toNat_sub]; omega

end LeanNanoLlvm.Tests.Rewrites
