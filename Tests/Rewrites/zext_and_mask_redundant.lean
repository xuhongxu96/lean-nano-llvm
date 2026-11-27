import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem zext_and_mask_redundant :
    [llvm-definition|
      define i32 @f(i8 %x) {
      entry:
        %e = zext i8 %x to i32
        %r = and i32 %e, 255
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i8 %x) {
      entry:
        %r = zext i8 %x to i32
        ret i32 %r
      }
    ] := by
  llvm_refine
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getLsbD_eq_getElem?_getD, getElem?_def]
  split <;> simp; intro h; clear h; revert i; decide

end LeanNanoLlvm.Tests.Rewrites
