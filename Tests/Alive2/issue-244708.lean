import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM Issue #244708: `[InstCombine] Missed fold: or (select C, (X & 112), 112), (X & -113) -> or X, (select C, 0, 112)`
https://github.com/llvm/llvm-project/issues/244708
Alive2: https://alive2.llvm.org/ce/z/5ixcjc
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem issue_244708 :
    [llvm-definition|
      define i8 @f(i1 %c, i8 %x) {
      entry:
        %m = and i8 %x, 112
        %s = select i1 %c, i8 %m, i8 112
        %lo = and i8 %x, -113
        %r = or disjoint i8 %s, %lo
        ret i8 %r
      }
    ] ⊒ [llvm-definition|
      define i8 @f(i1 %c, i8 %x) {
      entry:
        %s = select i1 %c, i8 0, i8 112
        %r = or i8 %x, %s
        ret i8 %r
      }
    ] := by
  llvm_refine <;> (
    intro _; ext i hi
    have hcomp : (112#8)[i]'hi = !((143#8)[i]'hi) := by revert i hi; decide
    simp [hcomp]; grind)

end LeanNanoLlvm.Tests.Alive2
