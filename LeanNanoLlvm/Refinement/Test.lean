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


private theorem intw_add_zero (x : IntW 8) :
    (do let y ← x; PoisonOr.value (y + (0 : BitVec 8))) = x := by
  cases x with
  | ofOption o =>
    cases o <;> simp

private theorem intw_add_zero_generic {w : Nat} (x : IntW w) :
    (do let y ← x; PoisonOr.value (y + (0 : BitVec w))) = x := by
  cases x with
  | ofOption o =>
    cases o <;> simp

open scoped LeanNanoLlvm.AST.Syntax in
theorem ret_add_x_0_refines_ret_x :
  [llvm-definition|
    define i8 @f(i8 %x) {
    entry:
      %x = add i8 %x, 0
      ret i8 %x
    }
  ] ⊑ [llvm-definition|
    define i8 @f(i8 %x) {
    entry:
      ret i8 %x
    }
  ] := by
  intro args undefs retval hwfAdd hwfRet hsig hargs h
  cases args with
  | nil =>
      simp [Definition.ArgValuesWellFormed] at hargs
  | cons arg rest =>
      cases rest with
      | nil =>
          cases arg <;> simp [Definition.ArgValuesWellFormed,
            RegisterValue.WellFormedFor] at hargs
          rename_i w v
          subst hargs
          simp [simp_llvm, simp_wellform, simp_llvm_option] at *
      | cons arg' rest' =>
          simp [Definition.ArgValuesWellFormed] at hargs

abbrev singletonWidths (w : Nat) : List.Vector Nat 1 := ⟨[w], by simp⟩

open scoped LeanNanoLlvm.AST.Syntax in
theorem ret_add_x_0_refines_ret_x_generic (w : Nat) :
  [llvm-1-definition|
    define i$0 @f(i$0 %x) {
    entry:
      %x = add i$0 %x, 0
      ret i$0 %x
    }
  ].instantiateWidths (singletonWidths w)
  ⊑
  [llvm-1-definition|
    define i$0 @f(i$0 %x) {
    entry:
      ret i$0 %x
    }
  ].instantiateWidths (singletonWidths w) := by
  intro args undefs retval hwfAdd hwfRet hsig hargs h
  cases args with
  | nil =>
      simp [Definition.ArgValuesWellFormed, singletonWidths] at hargs
  | cons arg rest =>
      cases rest with
      | nil =>
          cases arg <;> simp [Definition.ArgValuesWellFormed,
            RegisterValue.WellFormedFor, singletonWidths] at hargs
          rename_i w' v
          subst hargs
          simp [singletonWidths, simp_llvm, simp_wellform, simp_llvm_option] at *
      | cons arg' rest' =>
          simp [Definition.ArgValuesWellFormed, singletonWidths] at hargs


end LeanNanoLlvm.Refinement
