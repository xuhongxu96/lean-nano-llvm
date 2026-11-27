import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem switch_i1_to_select (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i1 %c, i$(w) %a, i$(w) %b) {
      entry:
        switch i1 %c, label %f [i1 1, label %t]
      t:
        br label %merge
      f:
        br label %merge
      merge:
        %r = phi i$(w) [%a, %t], [%b, %f]
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i1 %c, i$(w) %a, i$(w) %b) {
      entry:
        %r = select i1 %c, i$(w) %a, i$(w) %b
        ret i$(w) %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
