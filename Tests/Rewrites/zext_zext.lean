import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem zext_zext :
    [llvm-definition|
      define i32 @f(i8 %x) {
      entry:
        %e1 = zext i8 %x to i16
        %r = zext i16 %e1 to i32
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i8 %x) {
      entry:
        %r = zext i8 %x to i32
        ret i32 %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
