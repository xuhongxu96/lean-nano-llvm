/-
Adapted in part from Lean-MLIR.
See LICENSE and NOTICE in this repository for licensing and attribution details.

https://github.com/opencompl/lean-mlir
-/
import Mathlib.Data.Vector.Basic

inductive ConcreteOrMVar (α : Type u) (φ : Nat)
  | concrete (a : α)
  | mvar (i : Fin φ)
deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

instance : ToString (ConcreteOrMVar Nat φ) where
  toString x :=
    match x with
    | .concrete a => s!"i{a}"
    | .mvar i => s!"${i}"

instance : Coe α (ConcreteOrMVar α φ) := ⟨.concrete⟩

instance : OfNat (ConcreteOrMVar Nat φ) n := ⟨.concrete n⟩

namespace ConcreteOrMVar

def toConcrete : ConcreteOrMVar α 0 → α
  | .concrete a => a

@[simp]
theorem toConcrete_concrete : toConcrete (.concrete a) = a := rfl

/--
  Provide a value for the metavariable with the maximal index `φ` out of `φ+1` total metavariables.
  All other metavariables indices' are left as-is, but cast to `Fin φ` -/
def instantiateOne (a : α) : ConcreteOrMVar α (φ + 1) → ConcreteOrMVar α φ
  | .concrete w => .concrete w
  | .mvar i => i.lastCases (.concrete a) (fun j => .mvar j)

def instantiate (as : List.Vector α φ) : ConcreteOrMVar α φ → α
  | .concrete w => w
  | .mvar i => as.get i

def metaInstantiate [Lean.ToExpr α] (as : Vector Lean.Expr φ) : ConcreteOrMVar α φ → Lean.Expr
  | .concrete w => Lean.toExpr w
  | .mvar i => as[i]

@[simp]
def ofNat_eq_concrete (x : Nat) :
  (OfNat.ofNat x) = (ConcreteOrMVar.concrete x : ConcreteOrMVar Nat φ) := rfl

@[simp]
def instantiate_ofNat_eq (as : List.Vector Nat φ) (x : Nat) :
  ConcreteOrMVar.instantiate as (OfNat.ofNat x) = x := rfl

@[simp]
theorem instantiate_mvar_zero :
  (mvar (φ := 1) 0).instantiate ⟨[w], h1⟩ = w := rfl

end ConcreteOrMVar
