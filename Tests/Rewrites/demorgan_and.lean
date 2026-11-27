import Tests.Rewrites.Common

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem demorgan_and (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %a = and i$(w) %x, %y
        %r = xor i$(w) %a, -1
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %nx = xor i$(w) %x, -1
        %ny = xor i$(w) %y, -1
        %r = or i$(w) %nx, %ny
        ret i$(w) %r
      }
    ] := by
  llvm_refine
  simp only [xor_neg_one]; ext _ _; simp

end LeanNanoLlvm.Tests.Rewrites
