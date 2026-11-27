import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem not_icmp_slt_to_sge (w : Nat) :
    [llvm-definition|
      define i1 @f(i$(w) %x, i$(w) %y) {
      entry:
        %c = icmp slt i$(w) %x, %y
        %r = xor i1 %c, true
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i$(w) %x, i$(w) %y) {
      entry:
        %r = icmp sge i$(w) %x, %y
        ret i1 %r
      }
    ] := by
  llvm_refine
  rename_i a b
  by_cases h : a.toInt < b.toInt
  · simp [BitVec.slt, BitVec.sle, h, show ¬(b.toInt ≤ a.toInt) by omega]
  · simp [BitVec.slt, BitVec.sle, h, show b.toInt ≤ a.toInt by omega]

end LeanNanoLlvm.Tests.Rewrites
