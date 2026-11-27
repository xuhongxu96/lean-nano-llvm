import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem trunc_nuw_nsw_drop :
    [llvm-definition|
      define i8 @f(i32 %x) {
      entry:
        %r = trunc nuw nsw i32 %x to i8
        ret i8 %r
      }
    ] ⊒ [llvm-definition|
      define i8 @f(i32 %x) {
      entry:
        %r = trunc i32 %x to i8
        ret i8 %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
