import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem add_over_select (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i1 %c, i$(w) %a, i$(w) %b, i$(w) %d) {
      entry:
        %s = select i1 %c, i$(w) %a, i$(w) %b
        %r = add i$(w) %s, %d
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i1 %c, i$(w) %a, i$(w) %b, i$(w) %d) {
      entry:
        %ad = add i$(w) %a, %d
        %bd = add i$(w) %b, %d
        %r = select i1 %c, i$(w) %ad, i$(w) %bd
        ret i$(w) %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
