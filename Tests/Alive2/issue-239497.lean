import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

-- LLVM Issue #239497: `[ConstraintElimination] Missing relational proofs across signed and unsigned comparisons`
-- https://github.com/llvm/llvm-project/issues/239497

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem issue_239497 :
    [llvm-definition|
      define i1 @f(i32 %x, i32 %y) {
      entry:
        %u0 = icmp ult i32 %x, %y
        %xpos = icmp slt i32 0, %x
        %xy = and i1 %u0, %xpos
        %ypos = icmp slt i32 0, %y
        %guard = and i1 %xy, %ypos
        br i1 %guard, label %if_then, label %if_else
      if_then:
        %s0 = icmp slt i32 %x, %y
        ret i1 %s0
      if_else:
        ret i1 true
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i32 %x, i32 %y) {
      entry:
        ret i1 true
      }
    ] := by
  llvm_intro; llvm_symexec
  rename_i x y
  cases hg : (decide (x < y) && (0#32).slt x && (0#32).slt y)
  · llvm_symexec; llvm_vc
  · llvm_symexec; llvm_vc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    have ⟨⟨hult, hx⟩, hy⟩ := hg
    simp [BitVec.slt, BitVec.lt_def, BitVec.toInt_eq_toNat_cond] at hult hx hy ⊢
    bv_omega

end LeanNanoLlvm.Tests.Alive2
