import Tests.Rewrites.Common

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem xor_from_or_and_not (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %o = or i$(w) %x, %y
        %a = and i$(w) %x, %y
        %na = xor i$(w) %a, -1
        %r = and i$(w) %o, %na
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
  simp only [xor_neg_one]; ext _ _; simp; grind

end LeanNanoLlvm.Tests.Rewrites
