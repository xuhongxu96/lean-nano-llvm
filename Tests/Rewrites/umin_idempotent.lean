import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem umin_idempotent (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x) {
      entry:
        %c = icmp ult i$(w) %x, %x
        %r = select i1 %c, i$(w) %x, i$(w) %x
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x) {
      entry:
        ret i$(w) %x
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
