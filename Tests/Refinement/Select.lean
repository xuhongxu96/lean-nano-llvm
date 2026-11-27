import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import LeanNanoLlvm.AST.Unexpander
import Tests.Refinement.Helpers

/-! Refinement tests: `select` non-poison-propagation refinement. -/

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

/-! ### Select Non-Poison-Propagation Refinement -/

open scoped LeanNanoLlvm.AST.Syntax in
def retADef : AST.Definition := [llvm-definition|
  define i32 @f(i32 %a, i32 %b) {
  entry:
    ret i32 %a
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
def selectTrueDef : AST.Definition := [llvm-definition|
  define i32 @f(i32 %a, i32 %b) {
  entry:
    %r = select i1 true, i32 %a, i32 %b
    ret i32 %r
  }
]

theorem ret_a_refines_select_true : selectTrueDef ⊒ retADef := by
  llvm_refine

end LeanNanoLlvm.Refinement
