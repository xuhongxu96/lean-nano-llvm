import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

-- LLVM Issue #237772: `[CVP] X urem Y is not expanded when the largest X is exactly 2*Y`
-- https://github.com/llvm/llvm-project/issues/237772

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem issue_237772 :
    [llvm-definition|
      define i16 @f(i8 %a, i8 %b) {
      entry:
        %x = zext i8 %a to i16
        %y = zext i8 %b to i16
        %s = add nuw nsw i16 %x, %y
        %r = urem i16 %s, 255
        ret i16 %r
      }
    ] ⊒ [llvm-definition|
      define i16 @f(i8 %a, i8 %b) {
      entry:
        %x = zext i8 %a to i16
        %y = zext i8 %b to i16
        %s = add nuw nsw i16 %x, %y
        %lt = icmp ult i16 %s, 255
        %sub0 = add nsw i16 %s, -255
        %sel = select i1 %lt, i16 %s, i16 %sub0
        %top = icmp eq i16 %s, 510
        %r = select i1 %top, i16 0, i16 %sel
        ret i16 %r
      }
    ] := by
  llvm_refine
  all_goals
    have hlt : (BitVec.setWidth 16 arg0 + BitVec.setWidth 16 arg1).toNat ≤ 510 := by
      have ha := arg0.isLt; have hb := arg1.isLt
      simp [BitVec.toNat_add, BitVec.toNat_setWidth]; omega
    generalize BitVec.setWidth 16 arg0 + BitVec.setWidth 16 arg1 = s at hlt h h_1 ⊢
    have hne510 : s.toNat ≠ 510 := fun h' => h (BitVec.eq_of_toNat_eq h')
    have hge : 255 ≤ s.toNat := by simpa [BitVec.le_def] using h_1
  · simp [BitVec.saddOverflow, BitVec.toInt_eq_toNat_cond]; omega
  · rw [show (65281#16 : BitVec 16) = -(255#16) by decide, ← BitVec.sub_eq_add_neg]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_umod, BitVec.toNat_sub_of_le h_1]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : 255 < 2 ^ 16)]; omega

end LeanNanoLlvm.Tests.Alive2
