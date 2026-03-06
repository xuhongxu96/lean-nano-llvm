import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics
open AST.Syntax

open scoped LeanNanoLlvm.AST.Syntax in
def addDef : @AST.Definition 512 := [llvm-definition|
  define i8 @f(i8 %a, i8 %b) {
  entry:
    %x = add i8 %a, %b
    ret i8 %x
  }
]

theorem addDef_refines_itself : addDef ⊑ addDef := by
  intro args st retval h
  exact h

open scoped LeanNanoLlvm.AST.Syntax in
def retAddX0Def : @AST.Definition 512 := [llvm-definition|
  define i8 @f(i8 %x) {
  entry:
    %x = add i8 %x, 0
    ret i8 %x
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
def retXDef : @AST.Definition 512 := [llvm-definition|
  define i8 @f(i8 %x) {
  entry:
    ret i8 %x
  }
]

private theorem intw_add_zero (x : Semantics.IntW 8) :
    (do let y ← x; pure (y + (0 : BitVec 8))) = x := by
  cases x with
  | ofOption o =>
    cases o <;> simp


theorem ret_add_x_0_refines_ret_x : retAddX0Def ⊑ retXDef := by
  intro args undefs retval h
  sorry


end LeanNanoLlvm.Refinement
