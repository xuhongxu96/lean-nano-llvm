import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem neg_sub_swap (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %d = sub i$(w) %x, %y
        %r = sub i$(w) 0, %d
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %r = sub i$(w) %y, %x
        ret i$(w) %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
