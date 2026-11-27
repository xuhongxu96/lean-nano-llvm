import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem icmp_ule_add_nuw_cancel (w : Nat) :
    [llvm-definition|
      define i1 @f(i$(w) %x, i$(w) %y, i$(w) %c) {
      entry:
        %a = add nuw i$(w) %x, %c
        %b = add nuw i$(w) %y, %c
        %r = icmp ule i$(w) %a, %b
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i$(w) %x, i$(w) %y, i$(w) %c) {
      entry:
        %r = icmp ule i$(w) %x, %y
        ret i1 %r
      }
    ] := by
  llvm_refine
  intro h1 h2; simp_all [BitVec.le_def, BitVec.toNat_add_of_not_uaddOverflow, -BitVec.toNat_add]

end LeanNanoLlvm.Tests.Rewrites
