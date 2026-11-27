import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import Tests.Rewrites.Common

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem complement_partition (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %a = and i$(w) %x, %y
        %ny = xor i$(w) %y, -1
        %b = and i$(w) %x, %ny
        %r = or i$(w) %a, %b
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        ret i$(w) %x
      }
    ] := by
  llvm_refine
  simp only [xor_neg_one]; ext _ _; simp; grind

end LeanNanoLlvm.Tests.Rewrites
