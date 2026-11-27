import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem udiv_mul_nuw_cancel_3 :
    [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %a = mul nuw i32 %x, 3
        %r = udiv i32 %a, 3
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        ret i32 %x
      }
    ] := by
  llvm_refine
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul_of_not_umulOverflow ‹_›]

end LeanNanoLlvm.Tests.Rewrites
