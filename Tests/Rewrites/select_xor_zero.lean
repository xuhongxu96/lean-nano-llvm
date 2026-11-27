import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem select_xor_zero (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i1 %c, i$(w) %x, i$(w) %y) {
      entry:
        %s = select i1 %c, i$(w) %y, i$(w) 0
        %r = xor i$(w) %x, %s
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i1 %c, i$(w) %x, i$(w) %y) {
      entry:
        %a = xor i$(w) %x, %y
        %r = select i1 %c, i$(w) %a, i$(w) %x
        ret i$(w) %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
