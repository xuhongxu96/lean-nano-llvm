import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem xor_distrib_and (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y, i$(w) %z) {
      entry:
        %t = xor i$(w) %x, %y
        %r = and i$(w) %t, %z
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y, i$(w) %z) {
      entry:
        %a = and i$(w) %x, %z
        %b = and i$(w) %y, %z
        %r = xor i$(w) %a, %b
        ret i$(w) %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
