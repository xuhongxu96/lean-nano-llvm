import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

-- LLVM Issue #237771: `[InstCombine] Missed fold: two range checks differing by one bit, when each arm returns a value`
-- https://github.com/llvm/llvm-project/issues/237771

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem issue_237771 :
    [llvm-definition|
      define i32 @f(i8 %c) {
      entry:
        %z = zext i8 %c to i32
        %a1 = add i8 %c, -97
        %c1 = icmp ult i8 %a1, 6
        br i1 %c1, label %lower, label %upper
      lower:
        %v1 = add nsw i32 %z, -87
        br label %join
      upper:
        %a2 = add i8 %c, -65
        %c2 = icmp ult i8 %a2, 6
        %v2 = add nsw i32 %z, -55
        %v3 = select i1 %c2, i32 %v2, i32 -1
        br label %join
      join:
        %r = phi i32 [%v1, %lower], [%v3, %upper]
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i8 %c) {
      entry:
        %t1 = zext i8 %c to i32
        %t2 = or i32 %t1, 32
        %t3 = add i32 %t2, -97
        %t4 = icmp ult i32 %t3, 6
        %t5 = add i32 %t2, -87
        %t6 = select i1 %t4, i32 %t5, i32 -1
        ret i32 %t6
      }
    ] := by
  llvm_refine
  -- Every leaf is about the 8-bit argument alone; the `nsw` guards are not needed. Check all 256 values.
  · revert arg0; decide
  · clear h_1; revert arg0; decide
  · clear h; revert arg0; decide

end LeanNanoLlvm.Tests.Alive2
