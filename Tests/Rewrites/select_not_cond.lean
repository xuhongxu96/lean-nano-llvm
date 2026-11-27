import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem select_not_cond (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i1 %c, i$(w) %a, i$(w) %b) {
      entry:
        %nc = xor i1 %c, true
        %r = select i1 %nc, i$(w) %a, i$(w) %b
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i1 %c, i$(w) %a, i$(w) %b) {
      entry:
        %r = select i1 %c, i$(w) %b, i$(w) %a
        ret i$(w) %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
