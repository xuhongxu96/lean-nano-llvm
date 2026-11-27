import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import LeanNanoLlvm.AST.Unexpander
import Tests.Refinement.Helpers

/-! Refinement tests: basic arithmetic, reflexivity and width-generic refinement. -/

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

/-! ### Basic Arithmetic, Reflexivity & Width-Generic Refinement (`i$(w)`) -/

open scoped LeanNanoLlvm.AST.Syntax in
def addDef : AST.Definition := [llvm-definition|
  define i8 @f(i8 %a, i8 %b) {
  entry:
    %x = add i8 %a, %b
    ret i8 %x
  }
]

theorem addDef_is_refined_by_itself : addDef ⊒ addDef :=
  Definition.IsRefinedBy.refl addDef

open scoped LeanNanoLlvm.AST.Syntax in
def retXDef (w : Nat) : AST.Definition := [llvm-definition|
  define i$(w) @f(i$(w) %x) {
  entry:
    ret i$(w) %x
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
def retAddX0Def (w : Nat) : AST.Definition := [llvm-definition|
  define i$(w) @f(i$(w) %x) {
  entry:
    %x = add i$(w) %x, 0
    ret i$(w) %x
  }
]

theorem ret_add_x_0_is_refined_by_ret_x_generic (w : Nat) :
    retAddX0Def w ⊒ retXDef w := by
  llvm_refine

theorem ret_add_x_0_is_refined_by_ret_x :
    retAddX0Def 8 ⊒ retXDef 8 :=
  ret_add_x_0_is_refined_by_ret_x_generic 8

end LeanNanoLlvm.Refinement
