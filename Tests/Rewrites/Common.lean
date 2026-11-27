/-!
# Shared Pure-`BitVec` Helpers for Alive2 Proofs

Small pure-`BitVec` lemmas reused across individual rewrite proofs in `Tests/Alive2/`.
Kept out of `LeanNanoLlvm/Refinement/Tactic.lean` so the core tactics remain purely
LLVM-semantic.
-/

namespace LeanNanoLlvm.Tests.Rewrites

theorem neg_one_eq_allOnes (w : Nat) : -(1#w) = BitVec.allOnes w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.toNat_allOnes]
  cases w with
  | zero => simp
  | succ n =>
    have hpos : 1 < 2 ^ (n + 1) := by
      have := Nat.two_pow_pos n; rw [Nat.pow_succ]; omega
    simp [Nat.mod_eq_of_lt hpos, Nat.mod_eq_of_lt (show 2 ^ (n + 1) - 1 < 2 ^ (n + 1) by omega)]

theorem xor_neg_one {w : Nat} (x : BitVec w) : x ^^^ -(1#w) = ~~~x := by
  rw [neg_one_eq_allOnes]; ext i hi; simp

theorem not_eq_neg_sub_one {w : Nat} (x : BitVec w) : ~~~x = -x - 1#w := by
  have := BitVec.neg_eq_not_add x; grind

theorem nat_add_eq_xor_add_two_and (a b : Nat) : a + b = (a ^^^ b) + 2 * (a &&& b) := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    by_cases ha : a = 0
    · subst ha; simp
    · have hdiv : a / 2 < a := Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by omega)
      have hrec := ih (a / 2) hdiv (b / 2)
      have hxor : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
        apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_div_two]
      have hand : (a &&& b) / 2 = (a / 2) &&& (b / 2) := by
        apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_div_two]
      have hxm := Nat.testBit_xor a b 0
      have ham := Nat.testBit_and a b 0
      simp only [Nat.testBit_zero] at hxm ham
      grind

theorem bv_xor_eq_add_sub_two_and {w : Nat} (x y : BitVec w) :
    x ^^^ y = x + y - 2 * (x &&& y) := by
  have h : x + y = (x ^^^ y) + 2 * (x &&& y) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_xor, BitVec.toNat_and]
    rw [nat_add_eq_xor_add_two_and x.toNat y.toNat]
    simp [Nat.add_mod, Nat.mul_mod]
  grind

theorem bv_or_eq_add_sub_and {w : Nat} (x y : BitVec w) :
    x ||| y = x + y - (x &&& y) := by
  have h1 : x ||| y = (x ^^^ y) + (x &&& y) := by
    rw [BitVec.add_eq_or_of_and_eq_zero _ _ (by ext i hi; simp; grind)]
    ext i hi; simp; grind
  rw [h1, bv_xor_eq_add_sub_two_and]; grind

end LeanNanoLlvm.Tests.Rewrites
