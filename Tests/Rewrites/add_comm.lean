import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem add_comm (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %r = add i$(w) %x, %y
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %r = add i$(w) %y, %x
        ret i$(w) %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
