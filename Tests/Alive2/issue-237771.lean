import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

-- LLVM Issue #237771: `[InstCombine] Missed fold: two range checks differing by one bit, when each arm returns a value`
-- https://github.com/llvm/llvm-project/issues/237771

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem issue_237771 :
    [llvm-definition|
      define i32 @f(i8 %c) {
      entry:
        %z = zext i8 %c to i32
        %a1 = add i8 %c, -97
        %c1 = icmp ult i8 %a1, 6
        br i1 %c1, label %lower, label %upper
      lower:
        %v1 = add nsw i32 %z, -87
        br label %join
      upper:
        %a2 = add i8 %c, -65
        %c2 = icmp ult i8 %a2, 6
        %v2 = add nsw i32 %z, -55
        %v3 = select i1 %c2, i32 %v2, i32 -1
        br label %join
      join:
        %r = phi i32 [%v1, %lower], [%v3, %upper]
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i8 %c) {
      entry:
        %t1 = zext i8 %c to i32
        %t2 = or i32 %t1, 32
        %t3 = add i32 %t2, -97
        %t4 = icmp ult i32 %t3, 6
        %t5 = add i32 %t2, -87
        %t6 = select i1 %t4, i32 %t5, i32 -1
        ret i32 %t6
      }
    ] := by
  llvm_intro; llvm_symexec
  all_goals
    rename_i c
    cases hc1 : decide (c + 159#8 < 6#8)
    · simp only [BitVec.ofBool, cond_false]; llvm_symexec
      apply RegisterValue.isRefinedBy_bv_of_poisonOr
      have hnsw : (BitVec.setWidth 32 c).saddOverflow 4294967241#32 = false := by
        have := c.isLt; simp [BitVec.saddOverflow, BitVec.toInt_eq_toNat_cond, BitVec.toNat_setWidth]; omega
      simp [simp_llvm, hnsw]
      clear hnsw; revert c hc1 h_ite_sym; decide
    · simp only [BitVec.ofBool, cond_true]; llvm_symexec
      apply RegisterValue.isRefinedBy_bv_of_poisonOr
      have hnsw : (BitVec.setWidth 32 c).saddOverflow 4294967209#32 = false := by
        have := c.isLt; simp [BitVec.saddOverflow, BitVec.toInt_eq_toNat_cond, BitVec.toNat_setWidth]; omega
      simp [simp_llvm, hnsw]
      clear hnsw; revert c hc1 h_ite_sym; decide

end LeanNanoLlvm.Tests.Alive2
