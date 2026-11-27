import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import Tests.Rewrites.Common

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem demorgan_or (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %o = or i$(w) %x, %y
        %r = xor i$(w) %o, -1
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %nx = xor i$(w) %x, -1
        %ny = xor i$(w) %y, -1
        %r = and i$(w) %nx, %ny
        ret i$(w) %r
      }
    ] := by
  llvm_refine
  simp only [xor_neg_one]; ext _ _; simp

end LeanNanoLlvm.Tests.Rewrites
