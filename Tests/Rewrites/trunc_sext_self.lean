import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem trunc_sext_self :
    [llvm-definition|
      define i8 @f(i8 %x) {
      entry:
        %e = sext i8 %x to i32
        %r = trunc i32 %e to i8
        ret i8 %r
      }
    ] ⊒ [llvm-definition|
      define i8 @f(i8 %x) {
      entry:
        ret i8 %x
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
