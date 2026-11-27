import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM Issue #163093: `fold max(0, a-b) + (b-x) == 0 into select(a<0 ? b : a) == x`
https://github.com/llvm/llvm-project/issues/163093
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem issue_163093 (w : Nat) :
    [llvm-definition|
      define i1 @f(i$(w) %arg0, i$(w) %v1, i$(w) %v3) {
      entry:
        %v4 = sub i$(w) %v1, %v3
        %v5 = icmp slt i$(w) %v1, 0
        %v6 = select i1 %v5, i$(w) 0, i$(w) %v4
        %v7 = sub i$(w) %v3, %arg0
        %v8 = add i$(w) %v7, %v6
        %v9 = icmp eq i$(w) %v8, 0
        ret i1 %v9
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i$(w) %arg0, i$(w) %v1, i$(w) %v3) {
      entry:
        %v4 = icmp slt i$(w) %v1, 0
        %v5 = select i1 %v4, i$(w) %v3, i$(w) %v1
        %v6 = sub i$(w) %v5, %arg0
        %v7 = icmp eq i$(w) %v6, 0
        ret i1 %v7
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Alive2
