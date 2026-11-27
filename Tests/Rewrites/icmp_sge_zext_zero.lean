import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem icmp_sge_zext_zero :
    [llvm-definition|
      define i1 @f(i8 %x) {
      entry:
        %a = zext i8 %x to i32
        %r = icmp sge i32 %a, 0
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i8 %x) {
      entry:
        ret i1 true
      }
    ] := by
  llvm_refine
  simp [BitVec.sle, BitVec.toInt_eq_toNat_cond, -BitVec.toInt_setWidth]; bv_omega

end LeanNanoLlvm.Tests.Rewrites
