import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem zext_nneg_to_sext (w1 w2 : Nat) :
    [llvm-definition|
      define i$(w2) @f(i$(w1) %x) {
      entry:
        %r = zext nneg i$(w1) %x to i$(w2)
        ret i$(w2) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w2) @f(i$(w1) %x) {
      entry:
        %r = sext i$(w1) %x to i$(w2)
        ret i$(w2) %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
