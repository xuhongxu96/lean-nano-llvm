import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem icmp_eq_add_const (w : Nat) :
    [llvm-definition|
      define i1 @f(i$(w) %x) {
      entry:
        %a = add i$(w) %x, 5
        %r = icmp eq i$(w) %a, 12
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i$(w) %x) {
      entry:
        %r = icmp eq i$(w) %x, 7
        ret i1 %r
      }
    ] := by
  llvm_refine
  rw [Bool.eq_iff_iff]; simp [← BitVec.ofNat_eq_ofNat]; grind

end LeanNanoLlvm.Tests.Rewrites
