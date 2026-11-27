import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

/-!
# LLVM PR #238215 — `[GVN] Drop poison-generating flags from scalar PRE operand leaders`

- Source: <https://github.com/llvm/llvm-project/pull/238215>
- Alive2 (before fix, unsound): <https://alive2.llvm.org/ce/z/fVqw7n>
- Alive2 (after fix, sound): <https://alive2.llvm.org/ce/z/b4ztPz>

GVN scalar PRE reused `%cb = icmp samesign ult i32 %x, %y` from predecessor `pB` when
hoisting `zext i1 %cjoin to i32`, introducing `poison` when `%c = 0` and `%x, %y` have
opposite signs (`%x = 0, %y = -1`). Dropping `samesign` from `%cb` fixes the miscompile.
-/

namespace LeanNanoLlvm.Tests.Alive2

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

/-- PR #238215 (before fix): GVN scalar PRE keeping `samesign` on `%cb` is UNSOUND. -/
theorem pr_238215_gvn_pre_samesign_miscompile :
    ¬ ([llvm-definition|
      define i32 @src(i1 %c, i32 %x, i32 %y) {
      entry:
        br i1 %c, label %pA, label %pB
      pA:
        %ca = icmp ult i32 %x, %y
        %ra = zext i1 %ca to i32
        br label %join
      pB:
        %cb = icmp samesign ult i32 %x, %y
        br label %join
      join:
        %cjoin = icmp ult i32 %x, %y
        %r = zext i1 %cjoin to i32
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @tgt(i1 %c, i32 %x, i32 %y) {
      entry:
        br i1 %c, label %pA, label %pB
      pA:
        %ca = icmp ult i32 %x, %y
        %ra = zext i1 %ca to i32
        br label %join
      pB:
        %cb = icmp samesign ult i32 %x, %y
        %pre = zext i1 %cb to i32
        br label %join
      join:
        %rprephi = phi i32 [ %pre, %pB ], [ %ra, %pA ]
        %cjoin = icmp ult i32 %x, %y
        ret i32 %rprephi
      }
    ]) := by llvm_disprove

/-- PR #238215 (after fix): dropping `samesign` from `%cb` makes GVN scalar PRE SOUND. -/
theorem pr_238215_gvn_pre_samesign_fixed :
    [llvm-definition|
      define i32 @src(i1 %c, i32 %x, i32 %y) {
      entry:
        br i1 %c, label %pA, label %pB
      pA:
        %ca = icmp ult i32 %x, %y
        %ra = zext i1 %ca to i32
        br label %join
      pB:
        %cb = icmp samesign ult i32 %x, %y
        br label %join
      join:
        %cjoin = icmp ult i32 %x, %y
        %r = zext i1 %cjoin to i32
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @tgt(i1 %c, i32 %x, i32 %y) {
      entry:
        br i1 %c, label %pA, label %pB
      pA:
        %ca = icmp ult i32 %x, %y
        %ra = zext i1 %ca to i32
        br label %join
      pB:
        %cb = icmp ult i32 %x, %y
        %pre = zext i1 %cb to i32
        br label %join
      join:
        %rprephi = phi i32 [ %pre, %pB ], [ %ra, %pA ]
        %cjoin = icmp ult i32 %x, %y
        ret i32 %rprephi
      }
    ] := by llvm_refine

end LeanNanoLlvm.Tests.Alive2
