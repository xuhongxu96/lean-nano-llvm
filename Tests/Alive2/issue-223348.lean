import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM Issue #223348: `[InstCombine] Fold x > -x to x > 0 without nsw`
https://github.com/llvm/llvm-project/issues/223348

Valid even without `nsw`: at `0` and `INT_MIN`, `x == -x` so `x >s -x` is `false`,
matching `x >s 0`.
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem issue_223348 :
    [llvm-definition|
      define i1 @f(i32 %x) {
      entry:
        %neg = sub i32 0, %x
        %r = icmp sgt i32 %x, %neg
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i32 %x) {
      entry:
        %r = icmp sgt i32 %x, 0
        ret i1 %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Alive2
