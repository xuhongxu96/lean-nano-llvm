import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM PR #241985: `[AMDGPU][GlobalISel] Fold conditional increments and decrements into carry ops`
https://github.com/llvm/llvm-project/pull/241985
Alive2: https://alive2.llvm.org/ce/z/TZnU6U
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

theorem pr_241985_inc :
    [llvm-definition|
      define i32 @f(i1 %c, i32 %x) {
      entry:
        %n = add i32 %x, 1
        %r = select i1 %c, i32 %n, i32 %x
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i1 %c, i32 %x) {
      entry:
        %z = zext i1 %c to i32
        %r = add i32 %x, %z
        ret i32 %r
      }
    ] := by llvm_refine

theorem pr_241985_inc_swapped :
    [llvm-definition|
      define i32 @f(i1 %c, i32 %x) {
      entry:
        %n = add i32 %x, 1
        %r = select i1 %c, i32 %x, i32 %n
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i1 %c, i32 %x) {
      entry:
        %z = zext i1 %c to i32
        %a = sub i32 %x, -1
        %r = sub i32 %a, %z
        ret i32 %r
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Alive2
