/-
Adapted in part from Lean-MLIR.
See LICENSE and NOTICE in this repository for licensing and attribution details.

https://github.com/opencompl/lean-mlir
-/

import LeanNanoLlvm.Tactic
import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.Semantics.Denote
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
  We say that `a` is refined by `b`, written as `a ⊑ b`, when
  every observable behaviour of `b` is allowed by `a`.

  Note that this notation is driven by a typeclass, thus the exact meaning
  is type-dependent.
  -/
  IsRefinedBy : α → β → Prop

@[inherit_doc] infix:50 " ⊑ "  => HRefinement.IsRefinedBy

/--
The homogenous version of `HRefinement`.
This enables the notation `a ⊑ b`, where `a, b : α`.

NOTE: This typeclass is not intended for dialect implementors. Please implement
`DialectRefinement` instead.
-/
class Refinement (α : Type) where
  IsRefinedBy : α → α → Prop

instance instHRefinementOfRefinement [Refinement α] : HRefinement α α where
  IsRefinedBy := Refinement.IsRefinedBy

@[simp_denote]
def Refinement.ofHRefinement (inst : HRefinement α α) : Refinement α where
  IsRefinedBy x y := x ⊑ y

section OfEq

/-- Equality induces a trivial (homogenous) refinement relation on any type `α`. -/
def Refinement.ofEq : Refinement α where
  IsRefinedBy := Eq

instance (priority := low) :
    Std.Refl (HRefinement.IsRefinedBy (self := @instHRefinementOfRefinement α .ofEq)) where
  refl _ := rfl
instance (priority := low) :
    IsTrans α (HRefinement.IsRefinedBy (self := @instHRefinementOfRefinement α .ofEq)) where
  trans _ _ _ := Eq.trans
instance (priority := low) [DecidableEq α] :
    Decidable (HRefinement.IsRefinedBy (self := @instHRefinementOfRefinement α .ofEq) x y) :=
  decidable_of_iff (x = y) (by rfl)

end OfEq

/-! ### Id Refinement -/
namespace Id
variable {α β} [inst : HRefinement α β]

instance instRefinement : HRefinement (Id α) (Id β) := inst

@[simp_denote (high)] -- high priority so that this is tried before the `reduceIsRefinedBy` simproc
theorem pure_isRefinedBy_pure (x : α) (y : β) :
  (pure x : Id _) ⊑ (pure y : Id _) ↔ x ⊑ y := by rfl

end Id

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

variable {φ : Nat}

/--
Semantic refinement on LLVM definitions.

`x ⊑ y` has two components.

1. Definedness: if the source `x` can successfully return some value for every
   `undef` supply, then the target `y` must also be able to successfully
   return some value for every `undef` supply.
2. Value refinement: every concrete return value produced by the target `y`
   must already be producible by the source `x`, possibly under a different
   `undef` supply.
-/
def Definition.SignatureCompatible (x y : @AST.Definition φ) : Prop :=
  x.prototype.type = y.prototype.type

@[simp_denote]
theorem definition_signatureCompatible_iff (x y : @AST.Definition φ) :
    Definition.SignatureCompatible x y ↔ x.prototype.type = y.prototype.type := by
  rfl

/--
Return-value refinement for the current executable semantics.

A source poison integer return allows any target integer return of the same
width. Non-poison bitvector returns and `void` must match exactly.
-/
@[simp]
def RegisterValue.IsRefinedBy : RegisterValue → RegisterValue → Prop
  | .bv w_x .poison, .bv w_y _ => w_x = w_y
  | .bv w_x (.value v_x), .bv w_y (.value v_y) => ∃ h : w_x = w_y, h ▸ v_x = v_y
  | .void, .void => True
  | _, _ => False

@[simp_denote]
theorem registerValue_isRefinedBy_iff (x y : RegisterValue) :
    RegisterValue.IsRefinedBy x y ↔
      match x, y with
      | .bv w_x .poison, .bv w_y _ => w_x = w_y
      | .bv w_x (.value v_x), .bv w_y (.value v_y) => ∃ h : w_x = w_y, h ▸ v_x = v_y
      | .void, .void => True
      | _, _ => False := by
  cases x <;> cases y <;> rfl

def Definition.ReturnValuesRefined (x : @AST.Definition φ) (args : List RegisterValue)
    (_u : UndefChain) (ret : RegisterValue) : Prop :=
  ∃ u',
    runNanoLlvmStateM (denoteNanoLlvmDefinition x args) default ⟨u', 0⟩ = .ok ret ∨
      ∃ ret_x,
        runNanoLlvmStateM (denoteNanoLlvmDefinition x args) default ⟨u', 0⟩ = .ok ret_x ∧
          RegisterValue.IsRefinedBy ret_x ret

@[simp_denote]
theorem definition_returnValuesRefined_iff (x : @AST.Definition φ) (args : List RegisterValue)
    (u : UndefChain) (ret : RegisterValue) :
    Definition.ReturnValuesRefined x args u ret ↔
      ∃ u',
        runNanoLlvmStateM (denoteNanoLlvmDefinition x args) default ⟨u', 0⟩ = .ok ret ∨
          ∃ ret_x,
            runNanoLlvmStateM (denoteNanoLlvmDefinition x args) default ⟨u', 0⟩ = .ok ret_x ∧
              RegisterValue.IsRefinedBy ret_x ret := by
  rfl

def Definition.IsRefinedBy (x y : @AST.Definition φ) : Prop :=
  ∀ (args : List RegisterValue),
    AST.Definition.WellFormed x →
    AST.Definition.WellFormed y →
    Definition.SignatureCompatible x y →
    Semantics.Definition.ArgValuesWellFormed x args →
    (((∀ (u : UndefChain), ∃ (ret_x : RegisterValue),
        runNanoLlvmStateM (denoteNanoLlvmDefinition x args) default ⟨u, 0⟩ = .ok ret_x) →
      (∀ (u' : UndefChain), ∃ (ret_y : RegisterValue),
        runNanoLlvmStateM (denoteNanoLlvmDefinition y args) default ⟨u', 0⟩ = .ok ret_y)) ∧
      (∀ (u : UndefChain) (ret : RegisterValue),
        runNanoLlvmStateM (denoteNanoLlvmDefinition y args) default ⟨u, 0⟩ = .ok ret →
        Definition.ReturnValuesRefined x args u ret))

instance : Refinement (@AST.Definition φ) where
  IsRefinedBy := Definition.IsRefinedBy

@[simp_denote]
theorem definition_isRefinedBy_iff (x y : @AST.Definition φ) :
    x ⊑ y ↔
      (∀ (args : List RegisterValue),
        AST.Definition.WellFormed x →
        AST.Definition.WellFormed y →
        Definition.SignatureCompatible x y →
        Semantics.Definition.ArgValuesWellFormed x args →
        (((∀ (u : UndefChain), ∃ (ret_x : RegisterValue),
            runNanoLlvmStateM (denoteNanoLlvmDefinition x args) default ⟨u, 0⟩ = .ok ret_x) →
          (∀ (u' : UndefChain), ∃ (ret_y : RegisterValue),
            runNanoLlvmStateM (denoteNanoLlvmDefinition y args) default ⟨u', 0⟩ = .ok ret_y)) ∧
          (∀ (u : UndefChain) (ret : RegisterValue),
            runNanoLlvmStateM (denoteNanoLlvmDefinition y args) default ⟨u, 0⟩ = .ok ret →
            Definition.ReturnValuesRefined x args u ret))) := by
  rfl

end LeanNanoLlvm.Refinement
