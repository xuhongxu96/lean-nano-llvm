import LeanNanoLlvm.Refinement
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
  llvm_intro; llvm_symexec
  all_goals
    apply RegisterValue.isRefinedBy_bv_of_poisonOr
    try (simp [simp_llvm]; done)
  rename_i a b _
  have hlt : (BitVec.setWidth 16 a + BitVec.setWidth 16 b).toNat ≤ 510 := by
    have ha := a.isLt; have hb := b.isLt
    simp [BitVec.toNat_add, BitVec.toNat_setWidth]; omega
  generalize BitVec.setWidth 16 a + BitVec.setWidth 16 b = s at hlt ⊢
  have hs2 : s.saddOverflow 65281#16 = false := by
    simp [BitVec.saddOverflow, BitVec.toInt_eq_toNat_cond]; omega
  simp only [hs2, Bool.false_eq_true, ↓reduceIte, BitVec.ofBool]
  cases h510 : (s == 510#16)
  · simp only [cond_false]
    have hne510 : s.toNat ≠ 510 := by
      intro h; have : s = 510#16 := BitVec.eq_of_toNat_eq h
      simp [this] at h510
    cases h255 : decide (s < 255#16)
    · simp only [cond_false, PoisonOr.IsRefinedBy]
      have hge_bv : 255#16 ≤ s := by
        simp [BitVec.le_def, BitVec.lt_def] at h255 ⊢; omega
      have hge : 255 ≤ s.toNat := by simpa [BitVec.le_def] using hge_bv
      rw [show (65281#16 : BitVec 16) = -(255#16) by decide, ← BitVec.sub_eq_add_neg]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_umod, BitVec.toNat_sub_of_le hge_bv]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : 255 < 2 ^ 16)]; omega
    · simp only [cond_true, PoisonOr.IsRefinedBy]
      have hlt255 : s.toNat < 255 := by simpa [BitVec.lt_def] using h255
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_umod, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : 255 < 2 ^ 16)]; omega
  · simp only [cond_true, PoisonOr.IsRefinedBy]
    have heq : s = 510#16 := eq_of_beq h510
    rw [heq]; rfl

end LeanNanoLlvm.Tests.Alive2
