import Tests.Rewrites.Common

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem and_freeze_not_self (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x) {
      entry:
        %fx = freeze i$(w) %x
        %nfx = xor i$(w) %fx, -1
        %r = and i$(w) %fx, %nfx
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x) {
      entry:
        ret i$(w) 0
      }
    ] := by
  llvm_refine
  simp only [xor_neg_one]; ext _ _; simp

end LeanNanoLlvm.Tests.Rewrites
