/-
Released under Apache 2.0 license as described in the LICENSE of Lean-MLIR.

https://github.com/opencompl/lean-mlir
-/

import LeanNanoLlvm.Tactic
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
