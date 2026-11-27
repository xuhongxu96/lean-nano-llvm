import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem ashr_shl_nsw_cancel (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %c) {
      entry:
        %a = shl nsw i$(w) %x, %c
        %r = ashr i$(w) %a, %c
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %c) {
      entry:
        ret i$(w) %x
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
