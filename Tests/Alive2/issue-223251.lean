import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM Issue #223251: `[InstCombine] Fold range-with-hole test to direct inequality checks`
https://github.com/llvm/llvm-project/issues/223251

`((x - 8) >u 2) || ((x - 8) == 1) -> (x != 8) && (x != 10)` (on `i8`).
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem issue_223251 :
    [llvm-definition|
      define i1 @f(i8 %x) {
      entry:
        %v1 = add i8 %x, -8
        %v3 = icmp ugt i8 %v1, 2
        %v5 = icmp eq i8 %v1, 1
        %r = or i1 %v3, %v5
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i8 %x) {
      entry:
        %a = icmp ne i8 %x, 8
        %b = icmp ne i8 %x, 10
        %r = and i1 %a, %b
        ret i1 %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Alive2
