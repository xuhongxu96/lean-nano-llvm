import LeanNanoLlvm.AST
import LeanNanoLlvm.Tactic
import LeanNanoLlvm.Semantics
import Tests.Semantics.Helpers

/-! Semantics tests: immediate UB versus poison. -/

open LeanNanoLlvm
open AST.Syntax
open Semantics

section

open scoped LeanNanoLlvm.AST.Syntax

/-! ### Immediate UB vs Poison -/

theorem udiv_by_zero_is_immediate_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i8 @f() {
      entry:
        %r = udiv i8 10, 0
        ret i8 %r
      }
    ] []) = true := by
  decide +kernel

theorem sdiv_int_min_by_neg1_is_immediate_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i8 @f() {
      entry:
        %r = sdiv i8 -128, -1
        ret i8 %r
      }
    ] []) = true := by
  decide +kernel

theorem srem_poison_rhs_is_immediate_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i8 @f() {
      entry:
        %r = srem i8 5, poison
        ret i8 %r
      }
    ] []) = true := by
  decide +kernel

theorem udiv_exact_inexact_is_poison :
    runDefinitionRet [llvm-definition|
      define i8 @f() {
      entry:
        %r = udiv exact i8 5, 2
        ret i8 %r
      }
    ] [] = .ok (.bv 8 .poison) := by
  decide +kernel

theorem or_disjoint_overlap_is_poison :
    runDefinitionRet [llvm-definition|
      define i8 @f() {
      entry:
        %r = or disjoint i8 3, 2
        ret i8 %r
      }
    ] [] = .ok (.bv 8 .poison) := by
  decide +kernel

theorem br_poison_is_immediate_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        br i1 poison, label %a, label %b
      a:
        ret i32 1
      b:
        ret i32 2
      }
    ] []) = true := by
  decide +kernel

theorem unreachable_is_immediate_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        unreachable
      }
    ] []) = true := by
  decide +kernel

theorem assume_false_is_immediate_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        call void @llvm.assume(i1 false)
        ret i32 0
      }
    ] []) = true := by
  decide +kernel

end
