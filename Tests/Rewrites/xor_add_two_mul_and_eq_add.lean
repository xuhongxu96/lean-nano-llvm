import Tests.Rewrites.Common

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem xor_add_two_mul_and_eq_add (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %a = xor i$(w) %x, %y
        %b = and i$(w) %x, %y
        %c = mul i$(w) %b, 2
        %r = add i$(w) %a, %c
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %r = add i$(w) %x, %y
        ret i$(w) %r
      }
    ] := by
  llvm_refine
  simp only [bv_xor_eq_add_sub_two_and, ← BitVec.ofNat_eq_ofNat]; grind

end LeanNanoLlvm.Tests.Rewrites
