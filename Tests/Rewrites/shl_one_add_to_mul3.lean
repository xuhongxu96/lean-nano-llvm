import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem shl_one_add_to_mul3 (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x) {
      entry:
        %s = shl i$(w) %x, 1
        %r = add i$(w) %s, %x
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x) {
      entry:
        %r = mul i$(w) %x, 3
        ret i$(w) %r
      }
    ] := by
  llvm_refine
  intro h; cases w with
  | zero => omega
  | succ n =>
    have h1 : 1 < 2 ^ (n + 1) := Nat.one_lt_two_pow (by omega)
    rw [Nat.mod_eq_of_lt h1]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; grind

end LeanNanoLlvm.Tests.Rewrites
