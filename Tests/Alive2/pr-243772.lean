import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM PR #243772: `[InstCombine] Fold (X & (Y << Z)) >>u Z --> (X >>u Z) & Y`
https://github.com/llvm/llvm-project/pull/243772

Valid when `Y << Z` is `nuw` (no unsigned bits shifted out).
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem pr_243772 (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y, i$(w) %z) {
      entry:
        %s = shl nuw i$(w) %y, %z
        %a = and i$(w) %x, %s
        %r = lshr i$(w) %a, %z
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y, i$(w) %z) {
      entry:
        %s = lshr i$(w) %x, %z
        %r = and i$(w) %s, %y
        ret i$(w) %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Alive2
