import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem trunc_xor_sext :
    [llvm-definition|
      define i8 @f(i8 %x, i8 %y) {
      entry:
        %ex = sext i8 %x to i32
        %ey = sext i8 %y to i32
        %s = xor i32 %ex, %ey
        %r = trunc i32 %s to i8
        ret i8 %r
      }
    ] ⊒ [llvm-definition|
      define i8 @f(i8 %x, i8 %y) {
      entry:
        %r = xor i8 %x, %y
        ret i8 %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
