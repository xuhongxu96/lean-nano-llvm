import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import Tests.Rewrites.Common

-- LLVM Issue #243056: `[SelectionDAG] Borrow of 0 - zext(i1 c) in expanded i16 compare`
-- https://github.com/llvm/llvm-project/issues/243056
-- Alive2: https://alive2.llvm.org/ce/z/-AbaDY

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open LeanNanoLlvm.Tests.Rewrites
open scoped LeanNanoLlvm.AST.Syntax

theorem issue_243056 :
    [llvm-definition|
      define i1 @f(i8 %x0, i8 %x1, i8 %y0, i8 %y1) {
      entry:
        %b = icmp ult i8 %x0, %y0
        %x1z = zext i8 %x1 to i16
        %x = shl nuw i16 %x1z, 8
        %y1z = zext i8 %y1 to i16
        %y1s = shl nuw i16 %y1z, 8
        %bz = zext i1 %b to i16
        %y = or disjoint i16 %y1s, %bz
        %r = icmp slt i16 %x, %y
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i8 %x0, i8 %x1, i8 %y0, i8 %y1) {
      entry:
        %x0z = zext i8 %x0 to i16
        %x1z = zext i8 %x1 to i16
        %x1s = shl nuw i16 %x1z, 8
        %x = or disjoint i16 %x1s, %x0z
        %y0z = zext i8 %y0 to i16
        %y1z = zext i8 %y1 to i16
        %y1s = shl nuw i16 %y1z, 8
        %y = or disjoint i16 %y1s, %y0z
        %r = icmp slt i16 %x, %y
        ret i1 %r
      }
    ] := by
  llvm_refine
  -- `h_2`, `h_3`, `h_4` say the `or disjoint` operands are disjoint, so each `or` is an `add`.
  rw [bv_or_eq_add_sub_and, h_2, BitVec.sub_zero, bv_or_eq_add_sub_and, h_3, BitVec.sub_zero,
    bv_or_eq_add_sub_and, h_4, BitVec.sub_zero]
  rw [Bool.eq_iff_iff]
  simp [BitVec.slt, BitVec.lt_def, BitVec.toInt_eq_toNat_cond, BitVec.toNat_add,
    BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  by_cases hcmp : arg0.toNat < arg2.toNat <;> simp [hcmp] <;> bv_omega

end LeanNanoLlvm.Tests.Alive2
