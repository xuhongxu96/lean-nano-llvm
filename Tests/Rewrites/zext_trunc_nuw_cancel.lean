import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem zext_trunc_nuw_cancel :
    [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %a = trunc nuw i32 %x to i8
        %r = zext i8 %a to i32
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        ret i32 %x
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
