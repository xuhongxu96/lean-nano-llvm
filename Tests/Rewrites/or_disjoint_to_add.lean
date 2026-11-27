import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem or_disjoint_to_add (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %r = or disjoint i$(w) %x, %y
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %r = add i$(w) %x, %y
        ret i$(w) %r
      }
    ] := by
  llvm_refine
  exact (BitVec.add_eq_or_of_and_eq_zero _ _ h).symm

end LeanNanoLlvm.Tests.Rewrites
