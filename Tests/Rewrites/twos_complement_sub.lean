import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import Tests.Rewrites.Common

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem twos_complement_sub (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %ny = xor i$(w) %y, -1
        %t = add i$(w) %x, %ny
        %r = add i$(w) %t, 1
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %r = sub i$(w) %x, %y
        ret i$(w) %r
      }
    ] := by
  llvm_refine
  simp only [xor_neg_one, not_eq_neg_sub_one, BitVec.sub_eq_add_neg]; grind

end LeanNanoLlvm.Tests.Rewrites
