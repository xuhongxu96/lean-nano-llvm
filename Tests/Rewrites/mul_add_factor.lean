import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem mul_add_factor (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y, i$(w) %z) {
      entry:
        %a = mul i$(w) %x, %y
        %b = mul i$(w) %x, %z
        %r = add i$(w) %a, %b
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y, i$(w) %z) {
      entry:
        %s = add i$(w) %y, %z
        %r = mul i$(w) %x, %s
        ret i$(w) %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
