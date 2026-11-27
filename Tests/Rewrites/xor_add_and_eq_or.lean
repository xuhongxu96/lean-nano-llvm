import Tests.Rewrites.Common

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem xor_add_and_eq_or (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %a = xor i$(w) %x, %y
        %b = and i$(w) %x, %y
        %r = add i$(w) %a, %b
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %r = or i$(w) %x, %y
        ret i$(w) %r
      }
    ] := by
  llvm_refine
  simp only [bv_or_eq_add_sub_and, bv_xor_eq_add_sub_two_and]; grind

end LeanNanoLlvm.Tests.Rewrites
