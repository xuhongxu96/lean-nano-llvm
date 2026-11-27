import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM PR #214933: `[InstCombine] Fold comparisons of urem with dividend`
https://github.com/llvm/llvm-project/pull/214933

- `(X urem Y) == X` → `X ult Y`
- `(X urem Y) != X` → `X uge Y`
(Division by zero is immediate UB in source.)
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem pr_214933_eq (w : Nat) :
    [llvm-definition|
      define i1 @f(i$(w) %x, i$(w) %y) {
      entry:
        %rem = urem i$(w) %x, %y
        %r = icmp eq i$(w) %rem, %x
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i$(w) %x, i$(w) %y) {
      entry:
        %r = icmp ult i$(w) %x, %y
        ret i1 %r
      }
    ] := by
  llvm_refine
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, decide_eq_true_eq, BitVec.toNat_eq, BitVec.toNat_umod, BitVec.lt_def]
  constructor
  · intro h
    have hy0 : arg1.toNat ≠ 0 := by
      intro hz; apply ‹¬ arg1 = 0#w›; apply BitVec.eq_of_toNat_eq; simpa using hz
    have hlt := Nat.mod_lt arg0.toNat (Nat.pos_of_ne_zero hy0)
    omega
  · intro h; exact Nat.mod_eq_of_lt h

theorem pr_214933_ne (w : Nat) :
    [llvm-definition|
      define i1 @f(i$(w) %x, i$(w) %y) {
      entry:
        %rem = urem i$(w) %x, %y
        %r = icmp ne i$(w) %rem, %x
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i$(w) %x, i$(w) %y) {
      entry:
        %r = icmp uge i$(w) %x, %y
        ret i1 %r
      }
    ] := by
  llvm_refine
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq, BitVec.toNat_eq, BitVec.toNat_umod, BitVec.le_def]
  constructor
  · intro h
    exact Classical.byContradiction fun hge => h (Nat.mod_eq_of_lt (by omega))
  · intro h heq
    have hy0 : arg1.toNat ≠ 0 := by
      intro hz; apply ‹¬ arg1 = 0#w›; apply BitVec.eq_of_toNat_eq; simpa using hz
    have hlt := Nat.mod_lt arg0.toNat (Nat.pos_of_ne_zero hy0)
    omega

end LeanNanoLlvm.Tests.Alive2
