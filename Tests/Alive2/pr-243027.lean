import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM PR #243027: `[InstCombine] Fold and/or of mixed-sign icmps of the same operands`
https://github.com/llvm/llvm-project/pull/243027
Alive2: https://alive2.llvm.org/ce/z/3GAZDD
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem pr_243027_and_ult_sge :
    [llvm-definition|
      define i1 @f(i8 %x, i8 %y) {
      entry:
        %ult = icmp ult i8 %x, %y
        %sge = icmp sge i8 %x, %y
        %r = and i1 %ult, %sge
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i8 %x, i8 %y) {
      entry:
        %a = icmp sgt i8 %x, -1
        %b = icmp slt i8 %y, 0
        %r = and i1 %a, %b
        ret i1 %r
      }
    ] := by
  llvm_refine
  rw [Bool.eq_iff_iff]; simp [BitVec.sle, BitVec.slt, BitVec.toInt_eq_toNat_cond]; bv_omega

theorem pr_243027_and_ugt_sle :
    [llvm-definition|
      define i1 @f(i8 %x, i8 %y) {
      entry:
        %ugt = icmp ugt i8 %x, %y
        %sle = icmp sle i8 %x, %y
        %r = and i1 %ugt, %sle
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i8 %x, i8 %y) {
      entry:
        %a = icmp slt i8 %x, 0
        %b = icmp sgt i8 %y, -1
        %r = and i1 %a, %b
        ret i1 %r
      }
    ] := by
  llvm_refine
  rw [Bool.eq_iff_iff]; simp [BitVec.sle, BitVec.slt, BitVec.toInt_eq_toNat_cond]; bv_omega

end LeanNanoLlvm.Tests.Alive2
