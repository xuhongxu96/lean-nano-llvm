import Tests.Rewrites.Common

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem or_sub_and_eq_xor (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %a = or i$(w) %x, %y
        %b = and i$(w) %x, %y
        %r = sub i$(w) %a, %b
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
  simp only [bv_or_eq_add_sub_and, bv_xor_eq_add_sub_two_and]; grind

end LeanNanoLlvm.Tests.Rewrites
