import LeanNanoLlvm.Refinement.Disprove
import LeanNanoLlvm.AST.Syntax

/-!
# Kernel-Pure Disproofs of Unsound LLVM IR Rewrites

Tests for `llvm_disprove`: automatic timeout-bounded witness search (across `i1`–`i128`),
explicit witness mode `llvm_disprove [...]`, custom timeout `llvm_disprove (timeout := N)`,
value mismatches, poison introduction (`nsw`, `nuw`, `disjoint`, `select -> or/and`), and
UB introduction (`udiv`, `condBr` on poison).
-/

namespace LeanNanoLlvm.Tests.Rewrites

open LeanNanoLlvm Semantics Refinement
open scoped LeanNanoLlvm.AST.Syntax

/-- Wrong arithmetic result (`x + 1` vs `x + 2`, `i32`). -/
theorem disprove_wrong_add_i32 :
    ¬ ([llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %r = add i32 %x, 1
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %r = add i32 %x, 2
        ret i32 %r
      }
    ]) := by llvm_disprove

/-- Adding `nsw` when signed overflow is possible (`i32`). -/
theorem disprove_add_intro_nsw_i32 :
    ¬ ([llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %r = add i32 %x, 1
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %r = add nsw i32 %x, 1
        ret i32 %r
      }
    ]) := by llvm_disprove

/-- Adding `nuw` when unsigned overflow is possible (`i32`). -/
theorem disprove_add_intro_nuw_i32 :
    ¬ ([llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %r = add i32 %x, 1
        ret i32 %r
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i32 %x) {
      entry:
        %r = add nuw i32 %x, 1
        ret i32 %r
      }
    ]) := by llvm_disprove

/-- Classic Alive2 poison bug: `select %a, true, %b` cannot be folded to `or %a, %b`
    because `%a = true, %b = poison` produces `true` in src but `poison` in tgt. -/
theorem disprove_select_to_or_poison :
    ¬ ([llvm-definition|
      define i1 @f(i1 %a, i1 %b) {
      entry:
        %r = select i1 %a, i1 1, i1 %b
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i1 %a, i1 %b) {
      entry:
        %r = or i1 %a, %b
        ret i1 %r
      }
    ]) := by llvm_disprove

/-- Classic Alive2 poison bug: `select %a, %b, false` cannot be folded to `and %a, %b`
    because `%a = false, %b = poison` produces `false` in src but `poison` in tgt. -/
theorem disprove_select_to_and_poison :
    ¬ ([llvm-definition|
      define i1 @f(i1 %a, i1 %b) {
      entry:
        %r = select i1 %a, i1 %b, i1 0
        ret i1 %r
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i1 %a, i1 %b) {
      entry:
        %r = and i1 %a, %b
        ret i1 %r
      }
    ]) := by llvm_disprove

/-- Adding `disjoint` to `or` when bits may overlap (`i8`). -/
theorem disprove_or_intro_disjoint_i8 :
    ¬ ([llvm-definition|
      define i8 @f(i8 %x) {
      entry:
        %r = or i8 %x, 1
        ret i8 %r
      }
    ] ⊒ [llvm-definition|
      define i8 @f(i8 %x) {
      entry:
        %r = or disjoint i8 %x, 1
        ret i8 %r
      }
    ]) := by llvm_disprove

/-- Target introduces division-by-zero / poison-divisor UB (`udiv`). -/
theorem disprove_intro_udiv_ub :
    ¬ ([llvm-definition|
      define i8 @f(i8 %x, i8 %y) {
      entry:
        ret i8 %x
      }
    ] ⊒ [llvm-definition|
      define i8 @f(i8 %x, i8 %y) {
      entry:
        %d = udiv i8 %x, %y
        ret i8 %x
      }
    ]) := by llvm_disprove

/-- Target introduces UB by branching on a potentially-poison condition. -/
theorem disprove_intro_condbr_poison_ub :
    ¬ ([llvm-definition|
      define i32 @f(i1 %c) {
      entry:
        ret i32 42
      }
    ] ⊒ [llvm-definition|
      define i32 @f(i1 %c) {
      entry:
        br i1 %c, label %t, label %e
      t:
        ret i32 42
      e:
        ret i32 42
      }
    ]) := by llvm_disprove

/-- Wide `i64` constant extracted automatically from the IR AST (`424242`). -/
theorem disprove_i64_ast_constant :
    ¬ ([llvm-definition|
      define i1 @f(i64 %x) {
      entry:
        %c = icmp eq i64 %x, 424242
        ret i1 %c
      }
    ] ⊒ [llvm-definition|
      define i1 @f(i64 %x) {
      entry:
        ret i1 0
      }
    ]) := by llvm_disprove

/-- Wide `i128` overflow disproof with explicit timeout budget (no bitwidth cap). -/
theorem disprove_i128_intro_nuw :
    ¬ ([llvm-definition|
      define i128 @f(i128 %x) {
      entry:
        %r = add i128 %x, 1
        ret i128 %r
      }
    ] ⊒ [llvm-definition|
      define i128 @f(i128 %x) {
      entry:
        %r = add nuw i128 %x, 1
        ret i128 %r
      }
    ]) := by llvm_disprove (timeout := 5000)

/-- Explicit witness mode: `llvm_disprove [...]` bypasses search and certifies directly. -/
theorem disprove_explicit_witness :
    ¬ ([llvm-definition|
      define i8 @f(i8 %x) {
      entry:
        %r = or i8 %x, 1
        ret i8 %r
      }
    ] ⊒ [llvm-definition|
      define i8 @f(i8 %x) {
      entry:
        %r = or disjoint i8 %x, 1
        ret i8 %r
      }
    ]) := by
  llvm_disprove [RegisterValue.bv 8 (PoisonOr.value 1#8)]

end LeanNanoLlvm.Tests.Rewrites
