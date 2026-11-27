import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem icmp_eq_xor_zero (w : Nat) :
    [llvm-definition|
      define i1 @f(i$(w) %x, i$(w) %y) {
      entry:
        %d = xor i$(w) %x, %y
        %r = icmp eq i$(w) %d, 0
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i$(w) %x, i$(w) %y) {
      entry:
        %r = icmp eq i$(w) %x, %y
        ret i1 %r
      }
    ] := by
  llvm_refine
  rw [Bool.eq_iff_iff]; simp [BitVec.xor_eq_zero_iff]

end LeanNanoLlvm.Tests.Rewrites
