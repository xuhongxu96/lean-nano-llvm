import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM Issue #51744: `[InstCombine] fold multiply and equality compare with constant`
https://github.com/llvm/llvm-project/issues/51744

`(mul i32 %x, 1355350016) == 65536 -> (trunc i32 %x to i16) == 51577`
since `0x50c90000 = 0x50c9 * 2^16` and `0x50c9 * 0xc979 ≡ 1 (mod 2^16)`.
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem issue_51744 :
    [llvm-definition|
      define i1 @f(i32 %x) {
      entry:
        %m = mul i32 %x, 1355350016
        %r = icmp eq i32 %m, 65536
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i32 %x) {
      entry:
        %t = trunc i32 %x to i16
        %r = icmp eq i16 %t, 51577
        ret i1 %r
      }
    ] := by
  llvm_refine
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]
  have hsh : ∀ a : BitVec 32, a * 65536#32 = a <<< 16 := by
    intro a; rw [BitVec.shiftLeft_eq_mul_twoPow, show BitVec.twoPow 32 16 = 65536#32 by decide]
  have hc1 : (1355350016#32 : BitVec 32) * 51577#32 = 65536#32 := by decide
  have hc2 : (1355350016#32 : BitVec 32) = 65536#32 * 20681#32 := by decide
  have hc3 : ((51577#32 : BitVec 32) <<< 16) * 20681#32 = 65536#32 := by decide
  have hbits : BitVec.setWidth 16 (51577#32) = 51577#16 := by decide
  have hiff : ∀ a b : BitVec 32,
      a <<< 16 = b <<< 16 ↔ BitVec.setWidth 16 a = BitVec.setWidth 16 b := by
    intro a b; constructor
    · intro h; ext i hi
      have hi32 : i + 16 < 32 := by omega
      have hget := congrArg (fun v : BitVec 32 => v[i + 16]'hi32) h
      simpa [hi, show ¬(i + 16 < 16) by omega, show i + 16 - 16 = i by omega] using hget
    · intro h; ext i hi
      by_cases h16 : i < 16
      · simp [h16]
      · have hi16 : i - 16 < 16 := by omega
        have hget := congrArg (fun v : BitVec 16 => v[i - 16]'hi16) h
        simpa [h16, hi16] using hget
  constructor
  · intro h
    have hmul : (arg0 * 1355350016#32) * 51577#32 = 65536#32 * 51577#32 := congrArg (· * 51577#32) h
    rw [BitVec.mul_assoc, hc1, BitVec.mul_comm 65536#32 51577#32, hsh, hsh] at hmul
    rw [← hbits]; exact (hiff arg0 51577#32).mp hmul
  · intro h
    rw [← hbits] at h
    rw [hc2, ← BitVec.mul_assoc, hsh, (hiff arg0 51577#32).mpr h, hc3]

end LeanNanoLlvm.Tests.Alive2
