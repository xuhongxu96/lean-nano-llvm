import Tests.Rewrites.Common

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem neg_not_to_add_one (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x) {
      entry:
        %nx = xor i$(w) %x, -1
        %r = sub i$(w) 0, %nx
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x) {
      entry:
        %r = add i$(w) %x, 1
        ret i$(w) %r
      }
    ] := by
  llvm_refine
  simp only [xor_neg_one, not_eq_neg_sub_one, BitVec.sub_eq_add_neg]; grind

end LeanNanoLlvm.Tests.Rewrites
