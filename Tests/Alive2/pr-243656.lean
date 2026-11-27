import LeanNanoLlvm.Refinement.Disprove
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM PR #243656 — `[SCEV] Prove X + C u< X from X u>= -C in isImpliedCond`

- Source: <https://github.com/llvm/llvm-project/pull/243656>
- Alive2: <https://alive2.llvm.org/ce/z/_Yu7jT>

Disproves the unguarded negative test (`@src_noguard_must_fail` → `@tgt_noguard_must_fail`):
without the `x != 0` precondition, `(x - 1) u< x` is NOT refined by `true` (counterexample `x = 0`).
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

/-- PR #243656 negative test: without `x != 0`, `(x - 1) u< x` is not refined by `true`. -/
theorem pr_243656_noguard_must_fail :
    ¬ ([llvm-definition|
      define i8 @src_noguard_must_fail(i8 %x) {
      entry:
        %a = add i8 %x, -1
        %r = icmp ult i8 %a, %x
        %z = zext i1 %r to i8
        ret i8 %z
      }
    ] ⊒ [llvm-definition|
      define i8 @tgt_noguard_must_fail(i8 %x) {
      entry:
        ret i8 1
      }
    ]) := by llvm_disprove

/-- Exact `i1` version from Alive2 (`https://alive2.llvm.org/ce/z/_Yu7jT`). -/
theorem pr_243656_noguard_must_fail_i1 :
    ¬ ([llvm-definition|
      define i1 @src_noguard_must_fail(i8 %x) {
      entry:
        %a = add i8 %x, -1
        %r = icmp ult i8 %a, %x
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @tgt_noguard_must_fail(i8 %x) {
      entry:
        ret i1 1
      }
    ]) := by llvm_disprove

end LeanNanoLlvm.Tests.Alive2
