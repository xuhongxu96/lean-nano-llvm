import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM PR #231358: `[InstCombine] Fold sub nuw (and X, LowMask), (zext Y) to zext (sub nuw (trunc X), Y)`
https://github.com/llvm/llvm-project/pull/231358
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem pr_231358 :
    [llvm-definition|
      define i32 @f(i32 %x, i16 %y) {
      entry:
        %m = and i32 %x, 65535
        %zy = zext i16 %y to i32
        %r = sub nuw i32 %m, %zy
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %x, i16 %y) {
      entry:
        %tx = trunc i32 %x to i16
        %s = sub nuw i16 %tx, %y
        %r = zext i16 %s to i32
        ret i32 %r
      }
    ] := by
  llvm_refine
  rename_i x y
  have hm : (x &&& 65535#32).toNat = x.toNat % 2 ^ 16 := by
    rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 16
  constructor
  · intro h1 h2
    simp [BitVec.usubOverflow, hm] at h1 h2; bv_omega
  · intro h1 h2
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.usubOverflow, hm] at h1 h2
    simp [-BitVec.toNat_sub]
    bv_omega

end LeanNanoLlvm.Tests.Alive2
