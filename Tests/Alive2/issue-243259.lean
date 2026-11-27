import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM Issue #243259: `[InstCombine] Missed optimization: ((x & 1) + 9) >> 1 -> (x & 1) + 4`
https://github.com/llvm/llvm-project/issues/243259
Alive2: https://alive2.llvm.org/ce/z/_CB6nx
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem issue_243259 :
    [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %a = and i32 %x, 1
        %b = add nuw nsw i32 %a, 9
        %c = lshr i32 %b, 1
        ret i32 %c
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %a = and i32 %x, 1
        %c = add nuw nsw i32 %a, 4
        ret i32 %c
      }
    ] := by
  llvm_refine
  rename_i x
  have hlt : (x &&& 1#32).toNat < 2 := by
    rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt (Nat.and_le_right) (by decide)
  have h01 : x &&& 1#32 = 0#32 ∨ x &&& 1#32 = 1#32 := by
    rcases (show (x &&& 1#32).toNat = 0 ∨ (x &&& 1#32).toNat = 1 by omega) with h | h
    · left; exact BitVec.eq_of_toNat_eq h
    · right; exact BitVec.eq_of_toNat_eq h
  rcases h01 with h | h <;> rw [h] <;> simp [BitVec.saddOverflow, BitVec.uaddOverflow]

end LeanNanoLlvm.Tests.Alive2
