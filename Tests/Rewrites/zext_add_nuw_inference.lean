import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem zext_add_nuw_inference :
    [llvm-definition|
      define i16 @f(i8 %x, i8 %y) {
      entry:
        %a = zext i8 %x to i16
        %b = zext i8 %y to i16
        %r = add i16 %a, %b
        ret i16 %r
      }
    ] ⊒ [llvm-definition|
      define i16 @f(i8 %x, i8 %y) {
      entry:
        %a = zext i8 %x to i16
        %b = zext i8 %y to i16
        %r = add nuw i16 %a, %b
        ret i16 %r
      }
    ] := by
  llvm_refine
  intro h; simp [BitVec.uaddOverflow] at h; bv_omega

end LeanNanoLlvm.Tests.Rewrites
