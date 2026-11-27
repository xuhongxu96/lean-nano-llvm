import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem icmp_ult_add_nuw_const :
    [llvm-definition|
      define i1 @f(i32 %x) {
      entry:
        %a = add nuw i32 %x, 10
        %r = icmp ult i32 %a, 10
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i32 %x) {
      entry:
        ret i1 false
      }
    ] := by
  llvm_refine
  intro h; simp_all [BitVec.le_def, BitVec.toNat_add_of_not_uaddOverflow, -BitVec.toNat_add]

end LeanNanoLlvm.Tests.Rewrites
