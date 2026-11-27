import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem icmp_ult_zext_cancel :
    [llvm-definition|
      define i1 @f(i8 %x, i8 %y) {
      entry:
        %a = zext i8 %x to i32
        %b = zext i8 %y to i32
        %r = icmp ult i32 %a, %b
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i8 %x, i8 %y) {
      entry:
        %r = icmp ult i8 %x, %y
        ret i1 %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
