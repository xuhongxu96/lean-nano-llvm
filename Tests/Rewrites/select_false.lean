import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem select_false (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %a, i$(w) %b) {
      entry:
        %r = select i1 false, i$(w) %a, i$(w) %b
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %a, i$(w) %b) {
      entry:
        ret i$(w) %b
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
