import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem mul_sub_cancel (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y, i$(w) %z) {
      entry:
        %s = add i$(w) %x, %y
        %p = mul i$(w) %s, %z
        %q = mul i$(w) %y, %z
        %r = sub i$(w) %p, %q
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y, i$(w) %z) {
      entry:
        %r = mul i$(w) %x, %z
        ret i$(w) %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
