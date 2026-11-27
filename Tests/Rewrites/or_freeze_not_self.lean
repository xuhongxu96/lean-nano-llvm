import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import Tests.Rewrites.Common

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem or_freeze_not_self (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x) {
      entry:
        %fx = freeze i$(w) %x
        %nfx = xor i$(w) %fx, -1
        %r = or i$(w) %fx, %nfx
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x) {
      entry:
        ret i$(w) -1
      }
    ] := by
  llvm_refine
  simp only [neg_one_eq_allOnes]; ext _ _; simp

end LeanNanoLlvm.Tests.Rewrites
