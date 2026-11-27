import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem sext_trunc_nsw_cancel :
    [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %a = trunc nsw i32 %x to i8
        %r = sext i8 %a to i32
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        ret i32 %x
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
