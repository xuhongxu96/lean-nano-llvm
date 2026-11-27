import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem select_and_cond_to_nested (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i1 %c1, i1 %c2, i$(w) %a, i$(w) %b) {
      entry:
        %andc = and i1 %c1, %c2
        %r = select i1 %andc, i$(w) %a, i$(w) %b
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i1 %c1, i1 %c2, i$(w) %a, i$(w) %b) {
      entry:
        %s1 = select i1 %c2, i$(w) %a, i$(w) %b
        %r = select i1 %c1, i$(w) %s1, i$(w) %b
        ret i$(w) %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
