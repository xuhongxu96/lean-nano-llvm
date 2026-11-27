import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem nested_condBr_diamond_to_select (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i1 %c1, i1 %c2, i$(w) %a, i$(w) %b, i$(w) %d) {
      entry:
        br i1 %c1, label %inner, label %outer_f
      inner:
        br i1 %c2, label %t, label %f
      t:
        br label %merge
      f:
        br label %merge
      outer_f:
        br label %merge
      merge:
        %r = phi i$(w) [%a, %t], [%b, %f], [%d, %outer_f]
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i1 %c1, i1 %c2, i$(w) %a, i$(w) %b, i$(w) %d) {
      entry:
        %s1 = select i1 %c2, i$(w) %a, i$(w) %b
        %r = select i1 %c1, i$(w) %s1, i$(w) %d
        ret i$(w) %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
