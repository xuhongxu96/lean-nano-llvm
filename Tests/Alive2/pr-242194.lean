import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

-- LLVM PR #242194: `[InstCombine] Treat shl X, 1 as X + X when cancelling icmp addends`
-- https://github.com/llvm/llvm-project/pull/242194
-- Alive2: https://alive2.llvm.org/ce/z/LEhB-B

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem pr_242194 :
    [llvm-definition|
      define i1 @f(i32 %pos, i32 %n) {
      entry:
        %sum = add i32 %pos, %n
        %twice = shl i32 %n, 1
        %r = icmp eq i32 %sum, %twice
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i32 %pos, i32 %n) {
      entry:
        %r = icmp eq i32 %pos, %n
        ret i1 %r
      }
    ] := by
  llvm_refine
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]
  rw [BitVec.shiftLeft_eq_mul_twoPow]; bv_omega

end LeanNanoLlvm.Tests.Alive2
