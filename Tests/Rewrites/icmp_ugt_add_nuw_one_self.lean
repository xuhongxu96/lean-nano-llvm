import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem icmp_ugt_add_nuw_one_self :
    [llvm-definition|
      define i1 @f(i32 %x) {
      entry:
        %a = add nuw i32 %x, 1
        %r = icmp ugt i32 %a, %x
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i32 %x) {
      entry:
        ret i1 true
      }
    ] := by
  llvm_refine
  simp_all [BitVec.lt_def, BitVec.toNat_add_of_not_uaddOverflow, -BitVec.toNat_add]

end LeanNanoLlvm.Tests.Rewrites
