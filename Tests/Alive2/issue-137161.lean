import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM Issue #137161: `[InstCombine] Fold (X == 0 ? Y : 0) | X to X == 0 ? Y : X`
https://github.com/llvm/llvm-project/issues/137161
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem issue_137161 (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %c = icmp eq i$(w) %x, 0
        %s = select i1 %c, i$(w) %y, i$(w) 0
        %r = or i$(w) %s, %x
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %c = icmp eq i$(w) %x, 0
        %r = select i1 %c, i$(w) %y, i$(w) %x
        ret i$(w) %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Alive2
