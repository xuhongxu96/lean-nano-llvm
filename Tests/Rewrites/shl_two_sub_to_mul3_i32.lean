import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem shl_two_sub_to_mul3_i32 :
    [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %s = shl i32 %x, 2
        %r = sub i32 %s, %x
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %r = mul i32 %x, 3
        ret i32 %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
