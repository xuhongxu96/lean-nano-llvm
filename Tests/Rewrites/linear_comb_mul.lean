import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem linear_comb_mul (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x) {
      entry:
        %a = mul i$(w) %x, 3
        %b = mul i$(w) %x, 5
        %r = add i$(w) %a, %b
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x) {
      entry:
        %r = mul i$(w) %x, 8
        ret i$(w) %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
