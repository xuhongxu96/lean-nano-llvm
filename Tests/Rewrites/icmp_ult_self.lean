import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem icmp_ult_self (w : Nat) :
    [llvm-definition|
      define i1 @f(i$(w) %x) {
      entry:
        %r = icmp ult i$(w) %x, %x
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i$(w) %x) {
      entry:
        ret i1 false
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
