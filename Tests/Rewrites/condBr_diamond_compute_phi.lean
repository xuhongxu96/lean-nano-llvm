import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem condBr_diamond_compute_phi (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i1 %c, i$(w) %x) {
      entry:
        br i1 %c, label %t, label %f
      t:
        %a = add i$(w) %x, 1
        br label %merge
      f:
        %b = sub i$(w) %x, 1
        br label %merge
      merge:
        %r = phi i$(w) [%a, %t], [%b, %f]
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i1 %c, i$(w) %x) {
      entry:
        %a = add i$(w) %x, 1
        %b = sub i$(w) %x, 1
        %r = select i1 %c, i$(w) %a, i$(w) %b
        ret i$(w) %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
