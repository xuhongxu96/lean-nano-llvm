import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem sext_sub_nsw_inference :
    [llvm-definition|
      define i16 @f(i8 %x, i8 %y) {
      entry:
        %a = sext i8 %x to i16
        %b = sext i8 %y to i16
        %r = sub i16 %a, %b
        ret i16 %r
      }
    ] ⊒ [llvm-definition|
      define i16 @f(i8 %x, i8 %y) {
      entry:
        %a = sext i8 %x to i16
        %b = sext i8 %y to i16
        %r = sub nsw i16 %a, %b
        ret i16 %r
      }
    ] := by
  llvm_refine
  intro h; simp [BitVec.ssubOverflow, BitVec.toInt_signExtend_of_le] at h
  simp [BitVec.toInt_eq_toNat_cond] at h; bv_omega

end LeanNanoLlvm.Tests.Rewrites
