import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM PR #238951: `[ValueTracking] Infer nonzero for supersets of nonzero bit masks`
https://github.com/llvm/llvm-project/pull/238951
Alive2: https://alive2.llvm.org/ce/z/HKnKDk
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem pr_238951 :
    [llvm-definition|
      define i1 @f(i8 %x) {
      entry:
        %narrow = and i8 %x, 3
        %cond = icmp ne i8 %narrow, 0
        br i1 %cond, label %taken, label %exit
      taken:
        %wide = and i8 %x, 7
        %cmp = icmp ne i8 %wide, 0
        ret i1 %cmp
      exit:
        ret i1 false
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i8 %x) {
      entry:
        %narrow = and i8 %x, 3
        %cond_not = icmp eq i8 %narrow, 0
        br i1 %cond_not, label %exit, label %taken
      taken:
        ret i1 true
      exit:
        ret i1 false
      }
    ] := by
  llvm_refine
  -- `h_br` is the branch condition; the `taken` side must return `true`.
  intro h0; apply h_br
  have : (arg0 &&& 7#8) &&& 3#8 = 0#8 := by rw [h0]; rfl
  simpa [BitVec.and_assoc, show (7#8 : BitVec 8) &&& 3#8 = 3#8 by decide] using this

end LeanNanoLlvm.Tests.Alive2
