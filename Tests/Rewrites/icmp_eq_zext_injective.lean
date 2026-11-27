import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem icmp_eq_zext_injective :
    [llvm-definition|
      define i1 @f(i8 %x, i8 %y) {
      entry:
        %ex = zext i8 %x to i32
        %ey = zext i8 %y to i32
        %r = icmp eq i32 %ex, %ey
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i8 %x, i8 %y) {
      entry:
        %r = icmp eq i8 %x, %y
        ret i1 %r
      }
    ] := by
  llvm_refine
  rw [Bool.eq_iff_iff]; simp; constructor <;> intro h
  · apply BitVec.eq_of_toNat_eq; have := congrArg BitVec.toNat h; simp at this; bv_omega
  · subst h; rfl

end LeanNanoLlvm.Tests.Rewrites
