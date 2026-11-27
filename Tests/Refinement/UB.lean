import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import LeanNanoLlvm.AST.Unexpander
import Tests.Refinement.Helpers

/-! Refinement tests: immediate UB refines to any behavior. -/

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

/-! ### Immediate UB Refinement (UB Refines to Any Behavior) -/

open scoped LeanNanoLlvm.AST.Syntax in
def ret42Def : AST.Definition := [llvm-definition|
  define i8 @f(i8 %x) {
  entry:
    ret i8 42
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
def udivZeroDef : AST.Definition := [llvm-definition|
  define i8 @f(i8 %x) {
  entry:
    %r = udiv i8 %x, 0
    ret i8 %r
  }
]

theorem ret_42_refines_udiv_by_zero : udivZeroDef ⊒ ret42Def := by
  llvm_refine

end LeanNanoLlvm.Refinement
