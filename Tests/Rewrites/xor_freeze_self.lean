import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem xor_freeze_self (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x) {
      entry:
        %fx = freeze i$(w) %x
        %r = xor i$(w) %fx, %fx
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x) {
      entry:
        ret i$(w) 0
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
