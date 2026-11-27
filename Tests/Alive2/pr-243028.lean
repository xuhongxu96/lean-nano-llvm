import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM PR #243028: `[InstCombine] Fold an icmp into a chain of and/or when it folds with a leaf`
https://github.com/llvm/llvm-project/pull/243028
Alive2: https://alive2.llvm.org/ce/z/euszVD
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem pr_243028_or_chain (w : Nat) :
    [llvm-definition|
      define i1 @f(i$(w) %x, i$(w) %y, i1 %a, i1 %b) {
      entry:
        %lt = icmp ult i$(w) %x, %y
        %o1 = or i1 %lt, %a
        %o2 = or i1 %o1, %b
        %gt = icmp ugt i$(w) %x, %y
        %r = or i1 %gt, %o2
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i$(w) %x, i$(w) %y, i1 %a, i1 %b) {
      entry:
        %ne = icmp ne i$(w) %x, %y
        %o1 = or i1 %ne, %a
        %r = or i1 %o1, %b
        ret i1 %r
      }
    ] := by llvm_refine

theorem pr_243028_and_chain (w : Nat) :
    [llvm-definition|
      define i1 @f(i$(w) %x, i$(w) %y, i1 %a, i1 %b) {
      entry:
        %ge = icmp uge i$(w) %x, %y
        %a1 = and i1 %ge, %a
        %a2 = and i1 %a1, %b
        %le = icmp ule i$(w) %x, %y
        %r = and i1 %le, %a2
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i$(w) %x, i$(w) %y, i1 %a, i1 %b) {
      entry:
        %eq = icmp eq i$(w) %x, %y
        %a1 = and i1 %eq, %a
        %r = and i1 %a1, %b
        ret i1 %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Alive2
