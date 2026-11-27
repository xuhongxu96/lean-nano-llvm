import Tests.Rewrites.Common

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem or_freeze_neg_one (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x) {
      entry:
        %fx = freeze i$(w) %x
        %r = or i$(w) %fx, -1
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x) {
      entry:
        ret i$(w) -1
      }
    ] := by
  llvm_refine
  simp [neg_one_eq_allOnes]

end LeanNanoLlvm.Tests.Rewrites
