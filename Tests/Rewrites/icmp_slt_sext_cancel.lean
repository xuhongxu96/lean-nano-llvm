import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem icmp_slt_sext_cancel :
    [llvm-definition|
      define i1 @f(i8 %x, i8 %y) {
      entry:
        %a = sext i8 %x to i32
        %b = sext i8 %y to i32
        %r = icmp slt i32 %a, %b
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i8 %x, i8 %y) {
      entry:
        %r = icmp slt i8 %x, %y
        ret i1 %r
      }
    ] := by
  llvm_refine
  simp [BitVec.slt, BitVec.toInt_signExtend_of_le]

end LeanNanoLlvm.Tests.Rewrites
