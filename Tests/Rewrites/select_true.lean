import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem select_true (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %a, i$(w) %b) {
      entry:
        %r = select i1 true, i$(w) %a, i$(w) %b
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %a, i$(w) %b) {
      entry:
        ret i$(w) %a
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
