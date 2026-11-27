import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import Tests.Rewrites.Common

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem sub_not_x_eq_add_x_1 (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %nx = xor i$(w) %x, -1
        %r = sub i$(w) %y, %nx
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %a = add i$(w) %y, %x
        %r = add i$(w) %a, 1
        ret i$(w) %r
      }
    ] := by
  llvm_refine
  simp only [xor_neg_one, not_eq_neg_sub_one, BitVec.sub_eq_add_neg]; grind

end LeanNanoLlvm.Tests.Rewrites
