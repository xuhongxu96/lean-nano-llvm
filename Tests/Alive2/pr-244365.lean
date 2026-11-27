import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM PR #244365: `[NaryReassociate] Reassociate distributive mul when operands exist`
https://github.com/llvm/llvm-project/pull/244365
Alive2: https://alive2.llvm.org/ce/z/fJjGuD
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem pr_244365 (w : Nat) :
    [llvm-definition|
      define i$(w) @f(i$(w) %a, i$(w) %b, i$(w) %c) {
      entry:
        %s = add i$(w) %a, %b
        %r = mul i$(w) %s, %c
        ret i$(w) %r
      }
    ] ⊒ [llvm-definition|
      define i$(w) @f(i$(w) %a, i$(w) %b, i$(w) %c) {
      entry:
        %ac = mul i$(w) %a, %c
        %bc = mul i$(w) %b, %c
        %r = add i$(w) %ac, %bc
        ret i$(w) %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Alive2
