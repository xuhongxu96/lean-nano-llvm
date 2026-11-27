import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM PR #221189: `[InstCombine] Fold icmp (zext X), (and (trunc Y), Mask) -> icmp X, trunc Y`
https://github.com/llvm/llvm-project/pull/221189
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem pr_221189 :
    [llvm-definition|
      define i1 @f(i8 %x, i64 %y) {
      entry:
        %zx = zext i8 %x to i32
        %ty = trunc i64 %y to i32
        %m = and i32 %ty, 255
        %r = icmp ult i32 %zx, %m
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i8 %x, i64 %y) {
      entry:
        %ty = trunc i64 %y to i8
        %r = icmp ult i8 %x, %ty
        ret i1 %r
      }
    ] := by
  llvm_refine
  rename_i x y
  simp only [BitVec.lt_def, BitVec.toNat_setWidth, BitVec.toNat_and]
  have h1 : (y.toNat % 2 ^ 32) &&& (255#32).toNat = (y.toNat % 2 ^ 32) % 2 ^ 8 :=
    Nat.and_two_pow_sub_one_eq_mod _ 8
  rw [h1]; bv_omega

end LeanNanoLlvm.Tests.Alive2
