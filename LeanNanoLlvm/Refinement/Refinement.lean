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

class HRefinement (α β : Type) where
  /-- Heterogeneous refinement relation (`y ⊑ x` means target `y` refines source `x`). -/
  Refines : α → β → Prop

@[inherit_doc] infix:50 " ⊑ " => HRefinement.Refines

class Refinement (α : Type) where
  Refines : α → α → Prop

instance instHRefinementOfRefinement [Refinement α] : HRefinement α α where
  Refines := Refinement.Refines

@[simp_eval]
def Refinement.ofHRefinement (inst : HRefinement α α) : Refinement α where
  Refines x y := x ⊑ y

section OfEq

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

@[simp_eval (high)]
theorem pure_Refines_pure (x : α) (y : β) :
  (pure x : Id _) ⊑ (pure y : Id _) ↔ x ⊑ y := by rfl

end Id

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

variable {φ : Nat}

def Definition.SignatureCompatible (x y : @AST.Definition φ) : Prop :=
  x.prototype.type = y.prototype.type

@[simp_eval]
theorem definition_signatureCompatible_iff (x y : @AST.Definition φ) :
    Definition.SignatureCompatible x y ↔ x.prototype.type = y.prototype.type := by
  rfl

/-
Poison-aware structural return-value refinement across all LLVM IR value types.
A source `poison` scalar (int, float, ptr) allows any target scalar of the same type;
non-poison scalars must match; aggregates and vectors refine element-wise.
-/
mutual
@[simp]
def RegisterValue.Refines : RegisterValue → RegisterValue → Prop
  | .bv wy _, .bv wx .poison => wx = wy
  | .bv wy (.value vy), .bv wx (.value vx) => ∃ h : wx = wy, h ▸ vx = vy
  | .float fty _, .float ftx .poison => ftx = fty
  | .float fty (.value fy), .float ftx (.value fx) => ∃ h : ftx = fty, h ▸ fx = fy
  | .ptr asy _, .ptr asx .poison => asx = asy
  | .ptr asy (.value py), .ptr asx (.value px) => asx = asy ∧ px = py
  | .vector ty esy, .vector tx esx => tx = ty ∧ RegisterValue.RefinesList esy esx
  | .array ty esy, .array tx esx => tx = ty ∧ RegisterValue.RefinesList esy esx
  | .struct py tsy fsy, .struct px tsx fsx =>
      px = py ∧ tsx = tsy ∧ RegisterValue.RefinesList fsy fsx
  | .void, .void => True
  | _, _ => False

@[simp]
def RegisterValue.RefinesList : List RegisterValue → List RegisterValue → Prop
  | [], [] => True
  | y :: ys, x :: xs => RegisterValue.Refines y x ∧ RegisterValue.RefinesList ys xs
  | _, _ => False
end

mutual
theorem RegisterValue.Refines.refl : ∀ (v : RegisterValue), RegisterValue.Refines v v
  | .bv _ .poison => rfl
  | .bv _ (.value _) => ⟨rfl, rfl⟩
  | .float _ .poison => rfl
  | .float _ (.value _) => ⟨rfl, rfl⟩
  | .ptr _ .poison => rfl
  | .ptr _ (.value _) => ⟨rfl, rfl⟩
  | .vector _ elems => ⟨rfl, RegisterValue.RefinesList.refl elems⟩
  | .array _ elems => ⟨rfl, RegisterValue.RefinesList.refl elems⟩
  | .struct _ _ fields => ⟨rfl, rfl, RegisterValue.RefinesList.refl fields⟩
  | .void => trivial

theorem RegisterValue.RefinesList.refl : ∀ (vs : List RegisterValue), RegisterValue.RefinesList vs vs
  | [] => trivial
  | v :: vs => ⟨RegisterValue.Refines.refl v, RegisterValue.RefinesList.refl vs⟩
end

/-- Initial machine state for a given `(cfg, dl)` pair. -/
@[simp]
def initStateFor (cfg : SemanticsConfig) (dl : AST.DataLayout := .default64LE) : NanoLlvmState :=
  { config := cfg, dataLayout := dl, stepsRemaining := cfg.maxSteps }

/--
Config- and UB-aware semantic refinement on LLVM definitions (`y` refines `x`).

For all well-formed arguments `args`, assuming both definitions are well-formed under `cfg`
and have compatible signatures:
- If source `x` triggers Immediate UB under some oracle, target `y` is unrestricted (UB refines to anything).
- Otherwise:
  1. Definedness: if `x` succeeds for every total oracle `o`, then `y` must succeed for every oracle `o'`.
  2. Value refinement: every return value `ret_y` produced by `y` under some oracle `o` must refine
     a return value `ret_x` produced by `x` under some oracle `o'`.
-/
def Definition.RefinesWith (cfg : SemanticsConfig) (dl : AST.DataLayout := .default64LE)
    (y x : @AST.Definition φ) : Prop :=
  ∀ (args : List RegisterValue),
    AST.Definition.WellFormedWith cfg x →
    AST.Definition.WellFormedWith cfg y →
    Definition.SignatureCompatible x y →
    Semantics.Definition.ArgValuesWellFormed x args →
    (∃ (o : NondetOracle) (msg : String),
        runNanoLlvmM (evalNanoLlvmDefinition x args) (initStateFor cfg dl) ⟨o, 0⟩ = .error (.immediateUB msg)) ∨
    (((∀ (o : NondetOracle), ∃ (ret_x : RegisterValue),
        runNanoLlvmM (evalNanoLlvmDefinition x args) (initStateFor cfg dl) ⟨o, 0⟩ = .ok ret_x) →
      (∀ (o' : NondetOracle), ∃ (ret_y : RegisterValue),
        runNanoLlvmM (evalNanoLlvmDefinition y args) (initStateFor cfg dl) ⟨o', 0⟩ = .ok ret_y)) ∧
      (∀ (o : NondetOracle) (ret_y : RegisterValue),
        runNanoLlvmM (evalNanoLlvmDefinition y args) (initStateFor cfg dl) ⟨o, 0⟩ = .ok ret_y →
        ∃ (o' : NondetOracle) (ret_x : RegisterValue),
          runNanoLlvmM (evalNanoLlvmDefinition x args) (initStateFor cfg dl) ⟨o', 0⟩ = .ok ret_x ∧
          RegisterValue.Refines ret_y ret_x))

/-- Config-explicit refinement notation: `y ⊑[cfg] x`. -/
notation:50 y " ⊑[" cfg "] " x => Definition.RefinesWith cfg AST.DataLayout.default64LE y x

/-- Default refinement uses `SemanticsConfig.modern` (`undef` disabled). -/
def Definition.Refines (y x : @AST.Definition φ) : Prop :=
  Definition.RefinesWith .modern .default64LE y x

instance : Refinement (@AST.Definition φ) where
  Refines := Definition.Refines

/-- Reflexivity holds for every LLVM definition under any configuration and DataLayout. -/
theorem Definition.RefinesWith.refl (cfg : SemanticsConfig) (dl : AST.DataLayout := .default64LE)
    (d : @AST.Definition φ) : Definition.RefinesWith cfg dl d d := by
  intro args _ _ _ _
  right
  constructor
  · exact id
  · intro o ret h
    exact ⟨o, ret, h, RegisterValue.Refines.refl ret⟩

theorem Definition.Refines.refl (d : @AST.Definition φ) : d ⊑ d :=
  Definition.RefinesWith.refl .modern .default64LE d

end LeanNanoLlvm.Refinement
