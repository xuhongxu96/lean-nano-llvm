import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM Issue #238695: `[InstCombine] Missed optimization: fold ((x & (3 << n)) >> n) to ((x >> n) & 3)`
https://github.com/llvm/llvm-project/issues/238695
Alive2: https://alive2.llvm.org/ce/z/9bj492
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem issue_238695 :
    [llvm-definition|
      define i32 @f(i32 %x, i32 %n) {
      entry:
        %m = shl i32 3, %n
        %a = and i32 %x, %m
        %r = lshr i32 %a, %n
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %x, i32 %n) {
      entry:
        %s = lshr i32 %x, %n
        %r = and i32 %s, 3
        ret i32 %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Alive2
