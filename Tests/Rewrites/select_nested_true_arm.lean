import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem select_nested_true_arm (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i1 %c, i$(w) %a, i$(w) %b, i$(w) %d) {
      entry:
        %inner = select i1 %c, i$(w) %a, i$(w) %b
        %r = select i1 %c, i$(w) %inner, i$(w) %d
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i1 %c, i$(w) %a, i$(w) %b, i$(w) %d) {
      entry:
        %r = select i1 %c, i$(w) %a, i$(w) %d
        ret i$(w) %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
