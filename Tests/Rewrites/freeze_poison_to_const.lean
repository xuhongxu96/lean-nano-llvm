import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem freeze_poison_to_const (w : Nat) :
    [llvm-definition|
      define i$(w) @f() {
      entry:
        %r = freeze i$(w) poison
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f() {
      entry:
        ret i$(w) 0
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
