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
  intro args st retval _ _ _ _ h
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
    (do let y ← x; PoisonOr.value (y + (0 : BitVec 8))) = x := by
  cases x with
  | ofOption o =>
    cases o <;> simp

private theorem intw_add_zero_generic {w : Nat} (x : Semantics.IntW w) :
    (do let y ← x; PoisonOr.value (y + (0 : BitVec w))) = x := by
  cases x with
  | ofOption o =>
    cases o <;> simp


theorem ret_add_x_0_refines_ret_x : retAddX0Def ⊑ retXDef := by
  intro args undefs retval hwfAdd hwfRet hsig hargs h
  cases args with
  | nil =>
      simp [Semantics.Definition.ArgValuesWellFormed, retAddX0Def] at hargs
  | cons arg rest =>
      cases rest with
      | nil =>
          cases arg <;> simp [Semantics.Definition.ArgValuesWellFormed,
            Semantics.RegisterValue.WellFormedFor, retAddX0Def] at hargs
          rename_i w v
          subst hargs
          simp [retAddX0Def, simp_llvm, simp_wellform, simp_llvm_option] at *
      | cons arg' rest' =>
          simp [Semantics.Definition.ArgValuesWellFormed, retAddX0Def] at hargs

open scoped LeanNanoLlvm.AST.Syntax in
def retAddX0Poly : @AST.Definition 1 := [llvm-1-definition|
  define i$0 @f(i$0 %x) {
  entry:
    %x = add i$0 %x, 0
    ret i$0 %x
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
def retXPoly : @AST.Definition 1 := [llvm-1-definition|
  define i$0 @f(i$0 %x) {
  entry:
    ret i$0 %x
  }
]

abbrev singletonWidths (w : Nat) : List.Vector Nat 1 := ⟨[w], by simp⟩

theorem ret_add_x_0_refines_ret_x_generic (w : Nat) :
    retAddX0Poly.instantiateWidths (singletonWidths w) ⊑ retXPoly.instantiateWidths (singletonWidths w) := by
  intro args undefs retval hwfAdd hwfRet hsig hargs h
  cases args with
  | nil =>
      simp [Semantics.Definition.ArgValuesWellFormed, retAddX0Poly, singletonWidths] at hargs
  | cons arg rest =>
      cases rest with
      | nil =>
          cases arg <;> simp [Semantics.Definition.ArgValuesWellFormed,
            Semantics.RegisterValue.WellFormedFor, retAddX0Poly, singletonWidths] at hargs
          rename_i w' v
          subst hargs
          simp [singletonWidths, retAddX0Poly, retXPoly, simp_llvm, simp_wellform, simp_llvm_option] at h ⊢
          change Except.ok (RegisterValue.bv w v) = Except.ok retval at h
          change Except.ok (RegisterValue.bv w (do let x ← v; PoisonOr.value (x + (0 : BitVec w)))) =
            Except.ok retval
          rw [intw_add_zero_generic v]
          exact h
      | cons arg' rest' =>
          simp [Semantics.Definition.ArgValuesWellFormed, retAddX0Poly, singletonWidths] at hargs


end LeanNanoLlvm.Refinement
