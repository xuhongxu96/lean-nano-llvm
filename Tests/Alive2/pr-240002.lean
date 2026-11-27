import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM PR #240002: `[DivRemPairs] Recognize another "expanded rem" pattern`
https://github.com/llvm/llvm-project/pull/240002
Alive2: https://alive2.llvm.org/ce/z/drmNUV
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem pr_240002_unsigned_ne (w : Nat) :
    [llvm-definition|
      define i1 @f(i$(w) %n, i$(w) %c) {
      entry:
        %div = udiv i$(w) %n, %c
        %m0 = mul i$(w) %div, %c
        %cmp = icmp ne i$(w) %n, %m0
        ret i1 %cmp
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i$(w) %n, i$(w) %c) {
      entry:
        %div = udiv i$(w) %n, %c
        %rem = urem i$(w) %n, %c
        %cmp = icmp ne i$(w) %rem, 0
        ret i1 %cmp
      }
    ] := by
  llvm_refine
  rw [Bool.eq_iff_iff]; simp only [bne_iff_ne]
  have hrel : arg0 / arg1 * arg1 + arg0 % arg1 = arg0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_udiv, BitVec.toNat_umod]
    have hlt := arg0.isLt
    have hle : arg0.toNat / arg1.toNat * arg1.toNat ≤ arg0.toNat := Nat.div_mul_le_self _ _
    rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hlt), Nat.mul_comm, Nat.div_add_mod,
        Nat.mod_eq_of_lt hlt]
  constructor <;> intro h hc
  · apply h; rw [hc, BitVec.add_zero] at hrel; exact hrel.symm
  · apply h; rw [← hc] at hrel
    have h0 := congrArg (· - arg0) hrel
    rw [BitVec.add_comm arg0] at h0
    simpa [BitVec.add_sub_cancel] using h0

end LeanNanoLlvm.Tests.Alive2
