import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem icmp_eq_self (w : Nat) :
    [llvm-definition|
      define i1 @f(i$(w) %x) {
      entry:
        %r = icmp eq i$(w) %x, %x
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i$(w) %x) {
      entry:
        ret i1 true
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
