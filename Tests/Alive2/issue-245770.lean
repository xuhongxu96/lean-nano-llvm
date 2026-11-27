import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

-- LLVM Issue #245770: `[InstCombine] (x == c1 && y == c1) || (x == c2 && y == c2) => (x == c1 || x == c2) && (x == y)`
-- https://github.com/llvm/llvm-project/issues/245770
-- Alive2: https://alive2.llvm.org/ce/z/hcg_tW

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem issue_245770 (w : Nat) (c1 c2 : Int) :
    [llvm-definition|
      define i1 @f(i$(w) %x, i$(w) %y) {
      entry:
        %cmp = icmp eq i$(w) %x, <c1:int>
        %cmp1 = icmp eq i$(w) %y, <c1:int>
        %cond0 = and i1 %cmp, %cmp1
        br i1 %cond0, label %lor_end, label %lor_rhs
      lor_rhs:
        %cmp2 = icmp eq i$(w) %x, <c2:int>
        %cmp3 = icmp eq i$(w) %y, <c2:int>
        %v0 = and i1 %cmp2, %cmp3
        br label %lor_end
      lor_end:
        %r = phi i1 [true, %entry], [%v0, %lor_rhs]
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i$(w) %x, i$(w) %y) {
      entry:
        %cmp = icmp eq i$(w) %x, <c1:int>
        %cmp1 = icmp eq i$(w) %x, <c2:int>
        %cond0 = or i1 %cmp, %cmp1
        %cmp2 = icmp eq i$(w) %x, %y
        %r = and i1 %cond0, %cmp2
        ret i1 %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Alive2
