import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import Tests.Rewrites.Common

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem and_allones (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x) {
      entry:
        %r = and i$(w) %x, -1
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x) {
      entry:
        ret i$(w) %x
      }
    ] := by
  llvm_refine
  simp [neg_one_eq_allOnes]

end LeanNanoLlvm.Tests.Rewrites
