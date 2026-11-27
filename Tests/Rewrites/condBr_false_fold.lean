import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem condBr_false_fold (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %a, i$(w) %b) {
      entry:
        br i1 false, label %t, label %f
      t:
        ret i$(w) %a
      f:
        ret i$(w) %b
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %a, i$(w) %b) {
      entry:
        ret i$(w) %b
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
