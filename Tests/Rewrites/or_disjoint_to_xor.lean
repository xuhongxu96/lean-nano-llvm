import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import Tests.Rewrites.Common

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem or_disjoint_to_xor (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %r = or disjoint i$(w) %x, %y
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %r = xor i$(w) %x, %y
        ret i$(w) %r
      }
    ] := by
  llvm_refine
  simp only [bv_or_eq_add_sub_and, bv_xor_eq_add_sub_two_and, h, ← BitVec.ofNat_eq_ofNat]; grind

end LeanNanoLlvm.Tests.Rewrites
