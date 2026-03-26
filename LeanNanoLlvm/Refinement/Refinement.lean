/-
Adapted in part from Lean-MLIR.
See LICENSE and NOTICE in this repository for licensing and attribution details.

https://github.com/opencompl/lean-mlir
-/

import LeanNanoLlvm.Tactic
import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.Semantics.Eval
import LeanNanoLlvm.Semantics.Wellformed
import LeanNanoLlvm.Util.Undef
import Mathlib.Order.Defs.Unbundled

/--
The notation typeclass for heterogenous refinement relations.
This enables the notation `a ⊑ b`, where `a : α` and `b : β`.

NOTE: This typeclass is not intended for dialect implementors. Please implement
`DialectRefinement` instead, from which appropriate `HRefinement` instances will
be inferred.
-/
class HRefinement (α β : Type) where
  /--
  We say that `a` refines `b`, written as `a ⊑ b`, when
  every observable behaviour of `a` is allowed by `b`.

  Note that this notation is driven by a typeclass, thus the exact meaning
  is type-dependent.
  -/
  Refines : α → β → Prop

@[inherit_doc] infix:50 " ⊑ "  => HRefinement.Refines

/--
The homogenous version of `HRefinement`.
This enables the notation `a ⊑ b`, where `a, b : α`.

NOTE: This typeclass is not intended for dialect implementors. Please implement
`DialectRefinement` instead.
-/
class Refinement (α : Type) where
  Refines : α → α → Prop

instance instHRefinementOfRefinement [Refinement α] : HRefinement α α where
  Refines := Refinement.Refines

@[simp_eval]
def Refinement.ofHRefinement (inst : HRefinement α α) : Refinement α where
  Refines x y := x ⊑ y

section OfEq

/-- Equality induces a trivial (homogenous) refinement relation on any type `α`. -/
def Refinement.ofEq : Refinement α where
  Refines := Eq

instance (priority := low) :
    Std.Refl (HRefinement.Refines (self := @instHRefinementOfRefinement α .ofEq)) where
  refl _ := rfl
instance (priority := low) :
    IsTrans α (HRefinement.Refines (self := @instHRefinementOfRefinement α .ofEq)) where
  trans _ _ _ := Eq.trans
instance (priority := low) [DecidableEq α] :
    Decidable (HRefinement.Refines (self := @instHRefinementOfRefinement α .ofEq) x y) :=
  decidable_of_iff (x = y) (by rfl)

end OfEq

/-! ### Id Refinement -/
namespace Id
variable {α β} [inst : HRefinement α β]

instance instRefinement : HRefinement (Id α) (Id β) := inst

@[simp_eval (high)] -- high priority so that this is tried before the `reduceRefines` simproc
theorem pure_Refines_pure (x : α) (y : β) :
  (pure x : Id _) ⊑ (pure y : Id _) ↔ x ⊑ y := by rfl

end Id

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

variable {φ : Nat}

/--
Semantic refinement on LLVM definitions.

`y ⊑ x` has two components.

1. Definedness: if the source `x` can successfully return some value for every
   `undef` supply, then the target `y` must also be able to successfully
   return some value for every `undef` supply.
2. Value refinement: every concrete return value produced by the target `y`
   must already be producible by the source `x`, possibly under a different
   `undef` supply.
-/
def Definition.SignatureCompatible (x y : @AST.Definition φ) : Prop :=
  x.prototype.type = y.prototype.type

@[simp_eval]
theorem definition_signatureCompatible_iff (x y : @AST.Definition φ) :
    Definition.SignatureCompatible x y ↔ x.prototype.type = y.prototype.type := by
  rfl

/--
Return-value refinement for the current executable semantics.

A source poison integer return allows any target integer return of the same
width. Non-poison bitvector returns and `void` must match exactly.
-/
@[simp]
def RegisterValue.Refines : RegisterValue → RegisterValue → Prop
  | .bv w_x _, .bv w_y .poison => w_y = w_x
  | .bv w_x (.value v_x), .bv w_y (.value v_y) => ∃ h : w_y = w_x, h ▸ v_y = v_x
  | .void, .void => True
  | _, _ => False

@[simp_eval]
theorem registerValue_Refines_iff (y x : RegisterValue) :
    RegisterValue.Refines y x ↔
      match y, x with
      | .bv w_x _, .bv w_y .poison=> w_y = w_x
      | .bv w_x (.value v_x), .bv w_y (.value v_y) => ∃ h : w_y = w_x, h ▸ v_y = v_x
      | .void, .void => True
      | _, _ => False := by
  cases x <;> cases y <;> rfl

def Definition.ReturnValuesRefined (x : @AST.Definition φ) (args : List RegisterValue)
    (_u : UndefChain) (ret : RegisterValue) : Prop :=
  ∃ u',
    runNanoLlvmStateM (evalNanoLlvmDefinition x args) default ⟨u', 0⟩ = .ok ret ∨
      ∃ ret_x,
        runNanoLlvmStateM (evalNanoLlvmDefinition x args) default ⟨u', 0⟩ = .ok ret_x ∧
          RegisterValue.Refines ret ret_x

@[simp_eval]
theorem definition_returnValuesRefined_iff (x : @AST.Definition φ) (args : List RegisterValue)
    (u : UndefChain) (ret : RegisterValue) :
    Definition.ReturnValuesRefined x args u ret ↔
      ∃ u',
        runNanoLlvmStateM (evalNanoLlvmDefinition x args) default ⟨u', 0⟩ = .ok ret ∨
          ∃ ret_x,
            runNanoLlvmStateM (evalNanoLlvmDefinition x args) default ⟨u', 0⟩ = .ok ret_x ∧
              RegisterValue.Refines ret ret_x := by
  rfl

def Definition.Refines (y x : @AST.Definition φ) : Prop :=
  ∀ (args : List RegisterValue),
    AST.Definition.WellFormed x →
    AST.Definition.WellFormed y →
    Definition.SignatureCompatible x y →
    Semantics.Definition.ArgValuesWellFormed x args →
    (((∀ (u : UndefChain), ∃ (ret_x : RegisterValue),
        runNanoLlvmStateM (evalNanoLlvmDefinition x args) default ⟨u, 0⟩ = .ok ret_x) →
      (∀ (u' : UndefChain), ∃ (ret_y : RegisterValue),
        runNanoLlvmStateM (evalNanoLlvmDefinition y args) default ⟨u', 0⟩ = .ok ret_y)) ∧
      (∀ (u : UndefChain) (ret : RegisterValue),
        runNanoLlvmStateM (evalNanoLlvmDefinition y args) default ⟨u, 0⟩ = .ok ret →
        Definition.ReturnValuesRefined x args u ret))

instance : Refinement (@AST.Definition φ) where
  Refines := Definition.Refines

@[simp_eval]
theorem definition_Refines_iff (y x : @AST.Definition φ) :
    y ⊑ x ↔
      (∀ (args : List RegisterValue),
        x.WellFormed →
        y.WellFormed →
        Definition.SignatureCompatible x y →
        Semantics.Definition.ArgValuesWellFormed x args →
        (((∀ (u : UndefChain), ∃ (ret_x : RegisterValue),
            runNanoLlvmStateM (evalNanoLlvmDefinition x args) default ⟨u, 0⟩ = .ok ret_x) →
          (∀ (u' : UndefChain), ∃ (ret_y : RegisterValue),
            runNanoLlvmStateM (evalNanoLlvmDefinition y args) default ⟨u', 0⟩ = .ok ret_y)) ∧
          (∀ (u : UndefChain) (ret : RegisterValue),
            runNanoLlvmStateM (evalNanoLlvmDefinition y args) default ⟨u, 0⟩ = .ok ret →
            Definition.ReturnValuesRefined x args u ret))) := by
  rfl

end LeanNanoLlvm.Refinement
