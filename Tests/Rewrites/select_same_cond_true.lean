import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem select_same_cond_true (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i1 %c, i$(w) %a, i$(w) %b, i$(w) %d) {
      entry:
        %s1 = select i1 %c, i$(w) %a, i$(w) %b
        %r = select i1 %c, i$(w) %s1, i$(w) %d
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i1 %c, i$(w) %a, i$(w) %b, i$(w) %d) {
      entry:
        %r = select i1 %c, i$(w) %a, i$(w) %d
        ret i$(w) %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
