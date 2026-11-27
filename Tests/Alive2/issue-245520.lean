import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM Issue #245520: `[InstCombine] Missed optimization: (1 << X) ^ -(1 << X) -> -2 << X`
https://github.com/llvm/llvm-project/issues/245520
Alive2: https://alive2.llvm.org/ce/z/Z8kXMP
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem issue_245520 :
    [llvm-definition|
      define i64 @f(i64 %x) {
      entry:
        %p = shl nuw i64 1, %x
        %n = sub i64 0, %p
        %r = xor i64 %p, %n
        ret i64 %r
      }
    ] ⊒ [llvm-definition|
      define i64 @f(i64 %x) {
      entry:
        %r = shl i64 -2, %x
        ret i64 %r
      }
    ] := by
  llvm_refine
  rename_i x
  refine ⟨fun h1 h2 _ _ _ => by bv_omega, fun hlt _ _ _ => ?_⟩
  have hneg : -(1#64 <<< x.toNat) = (-1#64) <<< x.toNat := by
    rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.shiftLeft_eq_mul_twoPow, BitVec.one_mul,
      BitVec.neg_mul, BitVec.one_mul]
  rw [hneg, ← BitVec.shiftLeft_xor_distrib]; rfl

end LeanNanoLlvm.Tests.Alive2
