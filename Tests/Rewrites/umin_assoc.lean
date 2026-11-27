import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem umin_assoc (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y, i$(w) %z) {
      entry:
        %c1 = icmp ult i$(w) %x, %y
        %m1 = select i1 %c1, i$(w) %x, i$(w) %y
        %c2 = icmp ult i$(w) %m1, %z
        %r = select i1 %c2, i$(w) %m1, i$(w) %z
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %x, i$(w) %y, i$(w) %z) {
      entry:
        %c1 = icmp ult i$(w) %y, %z
        %m1 = select i1 %c1, i$(w) %y, i$(w) %z
        %c2 = icmp ult i$(w) %x, %m1
        %r = select i1 %c2, i$(w) %x, i$(w) %m1
        ret i$(w) %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Rewrites
