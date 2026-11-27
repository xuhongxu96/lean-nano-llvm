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
  by_cases h : arg0.toInt < arg1.toInt
  · simp [BitVec.slt, BitVec.sle, h, show ¬(arg1.toInt ≤ arg0.toInt) by omega]
  · simp [BitVec.slt, BitVec.sle, h, show arg1.toInt ≤ arg0.toInt by omega]

end LeanNanoLlvm.Tests.Rewrites
