/-
Adapted in part from Lean-MLIR.
See LICENSE and NOTICE in this repository for licensing and attribution details.

https://github.com/opencompl/lean-mlir
-/

import LeanNanoLlvm.Tactic
import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.Semantics.Step
import LeanNanoLlvm.Semantics.Wellformed

class HRefinement (α β : Type) where
  /-- Heterogeneous refinement relation (`x ⊒ y` means source `x` is refined by target `y`). -/
  IsRefinedBy : α → β → Prop

@[inherit_doc] infix:50 " ⊒ " => HRefinement.IsRefinedBy

class Refinement (α : Type) where
  IsRefinedBy : α → α → Prop

instance instHRefinementOfRefinement [Refinement α] : HRefinement α α where
  IsRefinedBy := Refinement.IsRefinedBy

@[simp_eval]
def Refinement.ofHRefinement (inst : HRefinement α α) : Refinement α where
  IsRefinedBy x y := x ⊒ y

section OfEq

def Refinement.ofEq : Refinement α where
  IsRefinedBy := Eq

instance (priority := low) :
    Std.Refl (HRefinement.IsRefinedBy (self := @instHRefinementOfRefinement α .ofEq)) where
  refl _ := rfl

instance (priority := low) :
    Trans (HRefinement.IsRefinedBy (self := @instHRefinementOfRefinement α .ofEq))
          (HRefinement.IsRefinedBy (self := @instHRefinementOfRefinement α .ofEq))
          (HRefinement.IsRefinedBy (self := @instHRefinementOfRefinement α .ofEq)) where
  trans := Eq.trans

instance (priority := low) [DecidableEq α] :
    Decidable (HRefinement.IsRefinedBy (self := @instHRefinementOfRefinement α .ofEq) x y) :=
  decidable_of_iff (x = y) (by rfl)

end OfEq

/-! ### Id Refinement -/
namespace Id
variable {α β} [inst : HRefinement α β]

instance instRefinement : HRefinement (Id α) (Id β) := inst

@[simp_eval (high)]
theorem pure_isRefinedBy_pure (x : α) (y : β) :
    (pure x : Id _) ⊒ (pure y : Id _) ↔ x ⊒ y := by rfl

end Id

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

/-- Two function definitions have identical LLVM function types. -/
def Definition.SignatureCompatible (x y : AST.Definition) : Prop :=
  x.prototype.type = y.prototype.type

@[simp_eval]
theorem definition_signatureCompatible_iff (x y : AST.Definition) :
    Definition.SignatureCompatible x y ↔ x.prototype.type = y.prototype.type := by
  rfl

theorem argValuesWellFormed_of_signatureCompatible {x y : AST.Definition}
    {args : List RegisterValue}
    (hsig : Definition.SignatureCompatible x y)
    (hargs : Semantics.Definition.ArgValuesWellFormed x args) :
    Semantics.Definition.ArgValuesWellFormed y args := by
  unfold Semantics.Definition.ArgValuesWellFormed at hargs ⊢
  rw [← hsig]
  exact hargs

/-! ### Small-Step Behavioral Helpers for Refinement Proofs -/

@[simp]
theorem terminates_halted_iff (v ret : RegisterValue) (m mem : MemoryState)
    (tr : List TraceEvent) :
    Terminates (.halted v m) tr ret mem ↔ tr = [] ∧ ret = v ∧ mem = m := by
  constructor
  · intro h
    cases h with
    | refl => exact ⟨rfl, rfl, rfl⟩
    | step hs _ => cases hs
  · rintro ⟨rfl, rfl, rfl⟩
    exact StarStep.refl _

theorem terminates_of_det_step {st : MachineState} {ev0 : Option TraceEvent} {c1 : Config}
    (hdet : ∀ ev c', Step (.running st) ev c' ↔ ev = ev0 ∧ c' = c1)
    {tr : List TraceEvent} {ret : RegisterValue} {mem : MemoryState} :
    Terminates (.running st) tr ret mem ↔
      ∃ tr', tr = ev0.toList ++ tr' ∧ Terminates c1 tr' ret mem :=
  StarStep.of_det_step hdet

theorem terminates_of_det_step_none {st : MachineState} {c1 : Config}
    (hdet : ∀ ev c', Step (.running st) ev c' ↔ ev = none ∧ c' = c1)
    {tr : List TraceEvent} {ret : RegisterValue} {mem : MemoryState} :
    Terminates (.running st) tr ret mem ↔ Terminates c1 tr ret mem := by
  rw [terminates_of_det_step hdet]
  simp

/-! ### Full Behavioral Definition Refinement -/

/--
Full behavioral small-step semantic refinement on LLVM definitions (source `x` is refined by target `y`).

Source `x` is refined by target `y` under `(cfg, dl)` iff:
- `x` and `y` have compatible function signatures (`Definition.SignatureCompatible x y`), and
- For every well-formed initial caller memory `initMem` and well-formed argument list `args`:
  - Either source `x` can abort (`CanAbort`, i.e., reach Immediate UB or a resource error such
    as OOM / stack overflow — allowing target optimizations like dead-`alloca` or tail-call
    elimination that avoid source allocations), OR:
  - Target `y` cannot abort (`¬ CanAbort cY`),
  - Every terminating execution of `y` (`Terminates cY trY retY memY`) is matched by a
    terminating execution of `x` (`Terminates cX trX retX memX`) and a memory injection `inj`
    that is the identity on all pre-existing caller objects (`inj.IdOn initMem.allocIds`) such that:
    1. Observable traces refine (`Trace.IsRefinedBy inj trX trY`),
    2. Return values refine (`RegisterValue.IsRefinedBy inj retX retY`),
    3. Caller-visible final memory refines (`MemoryState.IsRefinedBy inj initMem.allocIds memX memY`), and
  - If target `y` diverges (`Diverges cY`), then source `x` also diverges (`Diverges cX`).
-/
def Definition.IsRefinedByWith (cfg : SemanticsConfig) (dl : AST.DataLayout := .default64LE)
    (x y : AST.Definition) : Prop :=
  Definition.SignatureCompatible x y ∧
  ∀ (initMem : MemoryState) (args : List RegisterValue),
    MemoryState.WellFormed initMem →
    Semantics.Definition.ArgValuesWellFormed x args →
    let cX := initCallConfig cfg dl initMem ∅ ∅ x args
    let cY := initCallConfig cfg dl initMem ∅ ∅ y args
    CanAbort cX ∨
    (¬ CanAbort cY ∧
      (∀ trY retY memY,
        Terminates cY trY retY memY →
        ∃ trX retX memX inj,
          inj.IdOn initMem.allocIds ∧
          Terminates cX trX retX memX ∧
          Trace.IsRefinedBy inj trX trY ∧
          RegisterValue.IsRefinedBy inj retX retY ∧
          MemoryState.IsRefinedBy inj initMem.allocIds memX memY) ∧
      (Diverges cY → Diverges cX))

/-- Config-explicit refinement notation: `x ⊒[cfg] y` (source `x` is refined by target `y`). -/
notation:50 x " ⊒[" cfg "] " y => Definition.IsRefinedByWith cfg AST.DataLayout.default64LE x y

/-- Default refinement uses `SemanticsConfig.modern` (`undef` disabled). -/
def Definition.IsRefinedBy (x y : AST.Definition) : Prop :=
  Definition.IsRefinedByWith .modern .default64LE x y

instance : Refinement AST.Definition where
  IsRefinedBy := Definition.IsRefinedBy

/-- Reflexivity holds for every LLVM definition under any configuration and DataLayout. -/
theorem Definition.IsRefinedByWith.refl (cfg : SemanticsConfig)
    (dl : AST.DataLayout := .default64LE) (d : AST.Definition) :
    Definition.IsRefinedByWith cfg dl d d := by
  refine ⟨rfl, ?_⟩
  intro initMem args _ _
  by_cases habort : CanAbort (initCallConfig cfg dl initMem ∅ ∅ d args)
  · exact Or.inl habort
  · refine Or.inr ⟨habort, ?_, id⟩
    intro tr ret mem hterm
    exact ⟨tr, ret, mem, .id,
      MemoryInjection.id_idOn initMem.allocIds,
      hterm,
      Trace.IsRefinedBy.refl tr,
      RegisterValue.IsRefinedBy.refl ret,
      MemoryState.IsRefinedBy.refl initMem.allocIds mem⟩

theorem Definition.IsRefinedBy.refl (d : AST.Definition) : d ⊒ d :=
  Definition.IsRefinedByWith.refl .modern .default64LE d

/-- Transitivity holds unconditionally via `MemoryInjection.comp`, enabling multi-pass
    refinement chaining and Lean `calc` blocks (`x ⊒ y ⊒ z`). -/
theorem Definition.IsRefinedByWith.trans {cfg : SemanticsConfig} {dl : AST.DataLayout}
    {x y z : AST.Definition}
    (hxy : Definition.IsRefinedByWith cfg dl x y)
    (hyz : Definition.IsRefinedByWith cfg dl y z) :
    Definition.IsRefinedByWith cfg dl x z := by
  obtain ⟨hsigXY, hbehXY⟩ := hxy
  obtain ⟨hsigYZ, hbehYZ⟩ := hyz
  refine ⟨hsigXY.trans hsigYZ, ?_⟩
  intro initMem args hwfMem hargsX
  have hargsY := argValuesWellFormed_of_signatureCompatible hsigXY hargsX
  rcases hbehXY initMem args hwfMem hargsX with habortX | ⟨hnoAbortY, htermXY, hdivXY⟩
  · exact Or.inl habortX
  · rcases hbehYZ initMem args hwfMem hargsY with habortY | ⟨hnoAbortZ, htermYZ, hdivYZ⟩
    · exact absurd habortY hnoAbortY
    · refine Or.inr ⟨hnoAbortZ, ?_, fun hdivZ => hdivXY (hdivYZ hdivZ)⟩
      intro trZ retZ memZ htermZ
      obtain ⟨trY, retY, memY, inj2, hid2, htermY, htr2, hret2, hmem2⟩ :=
        htermYZ trZ retZ memZ htermZ
      obtain ⟨trX, retX, memX, inj1, hid1, htermX, htr1, hret1, hmem1⟩ :=
        htermXY trY retY memY htermY
      exact ⟨trX, retX, memX, MemoryInjection.comp inj1 inj2,
        MemoryInjection.comp_idOn hid1 hid2,
        htermX,
        Trace.IsRefinedBy.trans htr1 htr2,
        RegisterValue.IsRefinedBy.trans hret1 hret2,
        MemoryState.IsRefinedBy.trans hmem1 hmem2⟩

theorem Definition.IsRefinedBy.trans {x y z : AST.Definition}
    (hxy : x ⊒ y) (hyz : y ⊒ z) : x ⊒ z :=
  Definition.IsRefinedByWith.trans hxy hyz

instance (cfg : SemanticsConfig) (dl : AST.DataLayout) :
    Trans (Definition.IsRefinedByWith cfg dl)
          (Definition.IsRefinedByWith cfg dl)
          (Definition.IsRefinedByWith cfg dl) where
  trans := Definition.IsRefinedByWith.trans

instance : Trans Definition.IsRefinedBy Definition.IsRefinedBy Definition.IsRefinedBy where
  trans := Definition.IsRefinedBy.trans

instance :
    Trans (HRefinement.IsRefinedBy (α := AST.Definition) (β := AST.Definition))
          (HRefinement.IsRefinedBy (α := AST.Definition) (β := AST.Definition))
          (HRefinement.IsRefinedBy (α := AST.Definition) (β := AST.Definition)) where
  trans := Definition.IsRefinedBy.trans

end LeanNanoLlvm.Refinement
