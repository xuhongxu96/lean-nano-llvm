import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM Issue #244101: `[InstCombine] Missed optimization: (2 << X) | -(2 << X) -> -2 << X`
https://github.com/llvm/llvm-project/issues/244101
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem issue_244101 :
    [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %p = shl i32 2, %x
        %n = sub i32 0, %p
        %r = or i32 %p, %n
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %r = shl i32 -2, %x
        ret i32 %r
      }
    ] := by
  llvm_refine
  rename_i x
  constructor
  · intro h1 h2; bv_omega
  · intro hlt
    have h32 : x.toNat < 32 := by simp [BitVec.lt_def] at hlt; exact hlt
    have : ∀ k : Fin 32, (2#32 <<< k.val) ||| -(2#32 <<< k.val) = 4294967294#32 <<< k.val := by decide
    exact this ⟨x.toNat, h32⟩

end LeanNanoLlvm.Tests.Alive2
