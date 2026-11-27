import Tests.Rewrites.Common

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem complement_absorb_or (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %nx = xor i$(w) %x, -1
        %a = and i$(w) %nx, %y
        %r = or i$(w) %x, %a
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %r = or i$(w) %x, %y
        ret i$(w) %r
      }
    ] := by
  llvm_refine
  simp only [xor_neg_one]; ext _ _; simp; grind

end LeanNanoLlvm.Tests.Rewrites
