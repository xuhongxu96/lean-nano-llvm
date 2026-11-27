import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem condBr_same_phi_elim (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i1 %c, i$(w) %x) {
      entry:
        br i1 %c, label %t, label %f
      t:
        br label %merge
      f:
        br label %merge
      merge:
        %r = phi i$(w) [%x, %t], [%x, %f]
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i1 %c, i$(w) %x) {
      entry:
        ret i$(w) %x
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
