import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM PR #246147: `[InstCombine] Fold mulh with different source widths`
https://github.com/llvm/llvm-project/pull/246147
Alive2: https://alive2.llvm.org/ce/z/WXp95R
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem pr_246147 :
    [llvm-definition|
      define i16 @f(i8 %a, i4 %b) {
      entry:
        %ea = zext i8 %a to i16
        %eb = zext i4 %b to i16
        %m0 = mul i16 %ea, %eb
        %shr = lshr i16 %m0, 8
        ret i16 %shr
      }
    ] ⊒ [llvm-definition|
      define i16 @f(i8 %a, i4 %b) {
      entry:
        %b8 = zext i4 %b to i8
        %wa = zext i8 %a to i16
        %wb = zext i8 %b8 to i16
        %p = mul i16 %wa, %wb
        %hi = lshr i16 %p, 8
        %m = trunc i16 %hi to i8
        %r = zext i8 %m to i16
        ret i16 %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Alive2
