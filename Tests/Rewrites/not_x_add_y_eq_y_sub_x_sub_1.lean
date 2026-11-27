import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import Tests.Rewrites.Common

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem not_x_add_y_eq_y_sub_x_sub_1 (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %nx = xor i$(w) %x, -1
        %r = add i$(w) %nx, %y
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %a = sub i$(w) %y, %x
        %r = sub i$(w) %a, 1
        ret i$(w) %r
      }
    ] := by
  llvm_refine
  simp only [xor_neg_one, not_eq_neg_sub_one, BitVec.sub_eq_add_neg]; grind

end LeanNanoLlvm.Tests.Rewrites
