import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem smax_comm (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %c = icmp sgt i$(w) %x, %y
        %r = select i1 %c, i$(w) %x, i$(w) %y
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y) {
      entry:
        %c = icmp sgt i$(w) %y, %x
        %r = select i1 %c, i$(w) %y, i$(w) %x
        ret i$(w) %r
      }
    ] := by
  llvm_refine
  all_goals (repeat' split) <;> (try rfl) <;>
    (apply BitVec.eq_of_toInt_eq; simp [BitVec.slt] at *; omega)

end LeanNanoLlvm.Tests.Rewrites
