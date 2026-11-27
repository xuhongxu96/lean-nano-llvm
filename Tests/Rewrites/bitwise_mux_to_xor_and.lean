import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import Tests.Rewrites.Common

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem bitwise_mux_to_xor_and (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y, i$(w) %m) {
      entry:
        %a = and i$(w) %x, %m
        %nm = xor i$(w) %m, -1
        %b = and i$(w) %y, %nm
        %r = or i$(w) %a, %b
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y, i$(w) %m) {
      entry:
        %d = xor i$(w) %x, %y
        %dm = and i$(w) %d, %m
        %r = xor i$(w) %dm, %y
        ret i$(w) %r
      }
    ] := by
  llvm_refine
  simp only [xor_neg_one]; ext _ _; simp; grind

end LeanNanoLlvm.Tests.Rewrites
