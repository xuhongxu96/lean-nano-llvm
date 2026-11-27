import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem select_same_arms_to_freeze (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i1 %c, i$(w) %x) {
      entry:
        %r = select i1 %c, i$(w) %x, i$(w) %x
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i1 %c, i$(w) %x) {
      entry:
        %fc = freeze i1 %c
        %r = select i1 %fc, i$(w) %x, i$(w) %x
        ret i$(w) %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
