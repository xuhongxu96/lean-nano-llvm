/-
Adapted in part from Lean-MLIR.
See LICENSE and NOTICE in this repository for licensing and attribution details.

https://github.com/opencompl/lean-mlir
-/

import LeanNanoLlvm.Tactic
import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.Semantics.StepLemmas
import LeanNanoLlvm.Semantics.Wellformed

class HRefinement (α β : Type) where
  /-- Heterogeneous refinement relation (`x ⊒ y` means source `x` is refined by target `y`). -/
  IsRefinedBy : α → β → Prop

@[inherit_doc] infix:50 " ⊒ " => HRefinement.IsRefinedBy

class Refinement (α : Type) where
  IsRefinedBy : α → α → Prop

instance instHRefinementOfRefinement [Refinement α] : HRefinement α α where
  IsRefinedBy := Refinement.IsRefinedBy

@[simp_llvm]
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

@[simp_llvm]
theorem pure_isRefinedBy_pure (x : α) (y : β) :
    (pure x : Id _) ⊒ (pure y : Id _) ↔ x ⊒ y := by rfl

end Id

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

/-- Two function definitions have identical LLVM function types. -/
def Definition.SignatureCompatible (x y : AST.Definition) : Prop :=
  x.prototype.type = y.prototype.type

@[simp_wellform]
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

@[simp, simp_step]
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

/-- A running state that deterministically steps silently to `.halted v m` cannot abort or diverge,
    and uniquely terminates with `(tr = [], ret = v, mem = m)`. -/
theorem det_step_to_halted {st : MachineState} {v : RegisterValue} {m : MemoryState}
    (hdet : ∀ ev c', Step (.running st) ev c' ↔ ev = none ∧ c' = .halted v m) :
    ¬ CanAbort (.running st) ∧
    ¬ Diverges (.running st) ∧
    (∀ tr r mem, Terminates (.running st) tr r mem → tr = [] ∧ r = v ∧ mem = m) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [CanAbort.of_det_step hdet]; exact not_canAbort_halted
  · rw [Diverges.of_det_step hdet]; exact not_diverges_halted
  · intro tr r mem ht
    rw [terminates_of_det_step_none hdet, terminates_halted_iff] at ht
    exact ht

/-- Chain a deterministic silent step onto a deterministic-termination summary. -/
theorem det_step_chain {st : MachineState} {c1 : Config}
    (hdet : ∀ ev c', Step (.running st) ev c' ↔ ev = none ∧ c' = c1)
    {v : RegisterValue} {m : MemoryState}
    (h1 : ¬ CanAbort c1 ∧ ¬ Diverges c1 ∧
      ∀ tr r mem, Terminates c1 tr r mem → tr = [] ∧ r = v ∧ mem = m) :
    ¬ CanAbort (.running st) ∧
    ¬ Diverges (.running st) ∧
    (∀ tr r mem, Terminates (.running st) tr r mem → tr = [] ∧ r = v ∧ mem = m) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [CanAbort.of_det_step hdet]; exact h1.1
  · rw [Diverges.of_det_step hdet]; exact h1.2.1
  · intro tr r mem ht
    rw [terminates_of_det_step_none hdet] at ht
    exact h1.2.2 tr r mem ht

/-! ### Configuration-Level Behavioral Refinement -/

/--
Configuration-level small-step behavioral refinement (`cX` is refined by `cY` relative to
caller-owned allocations `callerIds`).
-/
def Config.IsRefinedBy (callerIds : List AllocId) (cX cY : Config) : Prop :=
  CanAbort cX ∨
  (¬ CanAbort cY ∧
    (∀ trY retY memY,
      Terminates cY trY retY memY →
      ∃ trX retX memX inj,
        inj.IdOn callerIds ∧
        Terminates cX trX retX memX ∧
        Trace.IsRefinedBy inj trX trY ∧
        RegisterValue.IsRefinedBy inj retX retY ∧
        MemoryState.IsRefinedBy inj callerIds memX memY) ∧
    (Diverges cY → Diverges cX))

theorem Config.IsRefinedBy.refl (callerIds : List AllocId) (c : Config) :
    Config.IsRefinedBy callerIds c c := by
  by_cases habort : CanAbort c
  · exact Or.inl habort
  · refine Or.inr ⟨habort, ?_, id⟩
    intro tr ret mem hterm
    exact ⟨tr, ret, mem, .id,
      MemoryInjection.id_idOn callerIds,
      hterm,
      Trace.IsRefinedBy.refl tr,
      RegisterValue.IsRefinedBy.refl ret,
      MemoryState.IsRefinedBy.refl callerIds mem⟩

theorem Config.IsRefinedBy.trans {callerIds : List AllocId} {cX cY cZ : Config}
    (hxy : Config.IsRefinedBy callerIds cX cY)
    (hyz : Config.IsRefinedBy callerIds cY cZ) :
    Config.IsRefinedBy callerIds cX cZ := by
  rcases hxy with habortX | ⟨hnoAbortY, htermXY, hdivXY⟩
  · exact Or.inl habortX
  · rcases hyz with habortY | ⟨hnoAbortZ, htermYZ, hdivYZ⟩
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

instance (callerIds : List AllocId) :
    Trans (Config.IsRefinedBy callerIds)
          (Config.IsRefinedBy callerIds)
          (Config.IsRefinedBy callerIds) where
  trans := Config.IsRefinedBy.trans

theorem Config.IsRefinedBy.of_canAbort {callerIds : List AllocId} {cX cY : Config}
    (h : CanAbort cX) : Config.IsRefinedBy callerIds cX cY :=
  Or.inl h

/-- Prove `Config.IsRefinedBy` when target `cY` deterministically halts at `(retY, memY)`
    and source `cX` can silently reach `(retX, memX)` with refined return value and memory. -/
theorem Config.IsRefinedBy.of_det_halted {callerIds : List AllocId} {cX cY : Config}
    {retX retY : RegisterValue} {memX memY : MemoryState}
    (hY : ¬ CanAbort cY ∧ ¬ Diverges cY ∧
      ∀ tr r m, Terminates cY tr r m → tr = [] ∧ r = retY ∧ m = memY)
    (hX_term : Terminates cX [] retX memX)
    (hret : RegisterValue.IsRefinedBy .id retX retY)
    (hmem : MemoryState.IsRefinedBy .id callerIds memX memY) :
    Config.IsRefinedBy callerIds cX cY := by
  refine Or.inr ⟨hY.1, ?_, fun hd => False.elim (hY.2.1 hd)⟩
  intro trY rY mY ht
  obtain ⟨rfl, rfl, rfl⟩ := hY.2.2 trY rY mY ht
  exact ⟨[], retX, memX, .id, MemoryInjection.id_idOn _, hX_term, trivial, hret, hmem⟩

/-- Stutter a single silent source step `cX → cX'` (preserving `Config.IsRefinedBy`). -/
theorem Config.IsRefinedBy.of_step_left {callerIds : List AllocId} {cX cX' cY : Config}
    (hsX : Step cX none cX')
    (h : Config.IsRefinedBy callerIds cX' cY) :
    Config.IsRefinedBy callerIds cX cY := by
  rcases h with habort | ⟨hnoY, hterm, hdiv⟩
  · exact Or.inl (CanAbort.of_starStep (StarStep.single hsX) habort)
  · refine Or.inr ⟨hnoY, ?_, fun hd => Diverges.of_step hsX (hdiv hd)⟩
    intro trY retY memY htY
    obtain ⟨trX, retX, memX, inj, hid, htermX, htr, hret, hmem⟩ := hterm trY retY memY htY
    exact ⟨trX, retX, memX, inj, hid, StarStep.step (ev := none) hsX htermX, htr, hret, hmem⟩

private theorem diverges_of_starStep {c1 tr c2} (hstar : StarStep c1 tr c2) (hd : Diverges c2) :
    Diverges c1 := by
  induction hstar with
  | refl _ => exact hd
  | step hs _ ih => exact Diverges.of_step hs (ih hd)

/-- Stutter any silent `StarStep` prefix on the source side. -/
theorem Config.IsRefinedBy.of_starStep_left {callerIds : List AllocId} {cX cX' cY : Config}
    (hsX : StarStep cX [] cX')
    (h : Config.IsRefinedBy callerIds cX' cY) :
    Config.IsRefinedBy callerIds cX cY := by
  rcases h with habort | ⟨hnoY, hterm, hdiv⟩
  · exact Or.inl (CanAbort.of_starStep hsX habort)
  · refine Or.inr ⟨hnoY, ?_, fun hd => diverges_of_starStep hsX (hdiv hd)⟩
    intro trY retY memY htY
    obtain ⟨trX, retX, memX, inj, hid, htermX, htr, hret, hmem⟩ := hterm trY retY memY htY
    exact ⟨trX, retX, memX, inj, hid, by simpa using StarStep.trans hsX htermX, htr, hret, hmem⟩

/-- Peel a deterministic silent step on the target side. -/
theorem Config.IsRefinedBy.of_det_step_right {callerIds : List AllocId}
    {stY : MachineState} {cX cY' : Config}
    (hdetY : ∀ ev c', Step (.running stY) ev c' ↔ ev = none ∧ c' = cY')
    (h : Config.IsRefinedBy callerIds cX cY') :
    Config.IsRefinedBy callerIds cX (.running stY) := by
  rcases h with habort | ⟨hnoY, hterm, hdiv⟩
  · exact Or.inl habort
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · rw [CanAbort.of_det_step hdetY]; exact hnoY
    · intro trY retY memY htY
      rw [terminates_of_det_step_none hdetY] at htY
      exact hterm trY retY memY htY
    · intro hdY
      rw [Diverges.of_det_step hdetY] at hdY
      exact hdiv hdY

/-- Lock-step deterministic silent transition on both source and target. -/
theorem Config.IsRefinedBy.of_det_step_both {callerIds : List AllocId}
    {stX stY : MachineState} {cX' cY' : Config}
    (hsX : Step (.running stX) none cX')
    (hdetY : ∀ ev c', Step (.running stY) ev c' ↔ ev = none ∧ c' = cY')
    (h : Config.IsRefinedBy callerIds cX' cY') :
    Config.IsRefinedBy callerIds (.running stX) (.running stY) :=
  Config.IsRefinedBy.of_step_left hsX (Config.IsRefinedBy.of_det_step_right hdetY h)

/-- An immediately-UB source configuration is refined by any target configuration. -/
theorem Config.IsRefinedBy.of_ub_left {callerIds : List AllocId} {msg : String} {cY : Config} :
    Config.IsRefinedBy callerIds (.ub msg) cY :=
  Or.inl (Or.inl ⟨[], msg, StarStep.refl _⟩)

/-- Refinement between two halted configurations reduces directly to return value and memory refinement. -/
theorem Config.IsRefinedBy.of_halted {callerIds : List AllocId}
    {retX retY : RegisterValue} {memX memY : MemoryState}
    (hret : RegisterValue.IsRefinedBy .id retX retY)
    (hmem : MemoryState.IsRefinedBy .id callerIds memX memY) :
    Config.IsRefinedBy callerIds (.halted retX memX) (.halted retY memY) :=
  Config.IsRefinedBy.of_det_halted
    ⟨not_canAbort_halted, not_diverges_halted, fun _ _ _ ht => (terminates_halted_iff _ _ _ _ _).mp ht⟩
    (StarStep.refl _) hret hmem

/-- Refinement between two halted configurations with identical memory reduces to return value refinement. -/
theorem Config.IsRefinedBy.of_halted_same_mem {callerIds : List AllocId}
    {retX retY : RegisterValue} {mem : MemoryState}
    (hret : RegisterValue.IsRefinedBy .id retX retY) :
    Config.IsRefinedBy callerIds (.halted retX mem) (.halted retY mem) :=
  Config.IsRefinedBy.of_halted hret (MemoryState.IsRefinedBy.refl callerIds mem)

/-- Peel a possibly nondeterministic silent target step: if every step from `.running stY`
    is silent (`ev = none`) and leads to some `cY'` refined by `cX`, then `.running stY`
    refines `cX`. -/
theorem Config.IsRefinedBy.of_step_right_forall {callerIds : List AllocId}
    {stY : MachineState} {cX : Config}
    (hinv : ∀ ev cY', Step (.running stY) ev cY' → ev = none ∧ Config.IsRefinedBy callerIds cX cY') :
    Config.IsRefinedBy callerIds cX (.running stY) := by
  by_cases habX : CanAbort cX
  · exact Or.inl habX
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · rintro (⟨tr, msg, hstar⟩ | ⟨tr, err, hstar⟩)
      · cases hstar with
        | step hs hrest =>
          have ⟨_, href⟩ := hinv _ _ hs
          rcases href with hab | ⟨hnoY, _, _⟩
          · exact habX hab
          · exact hnoY (Or.inl ⟨_, msg, hrest⟩)
      · cases hstar with
        | step hs hrest =>
          have ⟨_, href⟩ := hinv _ _ hs
          rcases href with hab | ⟨hnoY, _, _⟩
          · exact habX hab
          · exact hnoY (Or.inr ⟨_, err, hrest⟩)
    · intro trY retY memY htY
      cases htY with
      | step hs hrest =>
        have ⟨heq, href⟩ := hinv _ _ hs
        subst heq
        rcases href with hab | ⟨_, hterm, _⟩
        · exact absurd hab habX
        · simpa using hterm _ _ _ hrest
    · intro hdivY
      obtain ⟨ev, cY', hs, hdiv'⟩ := Diverges.step_inv hdivY
      have ⟨_, href⟩ := hinv ev cY' hs
      rcases href with hab | ⟨_, _, hdiv⟩
      · exact absurd hab habX
      · exact hdiv hdiv'

/-! ### General Backward Simulation Theorem (for CFG, Loops, Traces & Memory) -/

/--
General CompCert-style backward simulation theorem for `Config.IsRefinedBy`.

Given a simulation invariant `R : MemoryInjection → Config → Config → Prop` and a well-founded
target-stuttering measure `measure : Config → Nat`:
- `hHalted`: related halted target configs match source termination (or source can abort),
- `hAbort`: related aborting target configs imply source can abort,
- `hStep`: every target step `cY →[evY] cY'` either implies source can abort, or is matched by
  either ≥1 source steps (`PlusStep`) or 0 source steps with strictly decreasing `measure cY'`,
  extending `inj` monotonically (`inj.Extends inj'`) and preserving refined trace events.

Then `inj.IdOn callerIds → R inj cX cY → Config.IsRefinedBy callerIds cX cY`.
-/
theorem Config.IsRefinedBy.of_simulation
    {callerIds : List AllocId}
    (R : MemoryInjection → Config → Config → Prop)
    (measure : Config → Nat := fun _ => 0)
    (hHalted : ∀ inj cX retY memY,
      R inj cX (.halted retY memY) →
      CanAbort cX ∨
      ∃ trX retX memX inj',
        inj.Extends inj' ∧
        Terminates cX trX retX memX ∧
        Trace.IsRefinedBy inj' trX [] ∧
        RegisterValue.IsRefinedBy inj' retX retY ∧
        MemoryState.IsRefinedBy inj' callerIds memX memY)
    (hAbort : ∀ inj cX cY,
      R inj cX cY →
      ((∃ msg, cY = .ub msg) ∨ (∃ err, cY = .resourceError err)) →
      CanAbort cX)
    (hStep : ∀ inj cX cY evY cY',
      R inj cX cY →
      Step cY evY cY' →
      CanAbort cX ∨
      ∃ trX cX' inj',
        inj.Extends inj' ∧
        (PlusStep cX trX cX' ∨ (cX' = cX ∧ trX = [] ∧ measure cY' < measure cY)) ∧
        Trace.IsRefinedBy inj' trX evY.toList ∧
        R inj' cX' cY')
    {inj0 : MemoryInjection} {cX0 cY0 : Config}
    (hid0 : inj0.IdOn callerIds) (hR0 : R inj0 cX0 cY0) :
    Config.IsRefinedBy callerIds cX0 cY0 := by
  by_cases habortX0 : CanAbort cX0
  · exact Or.inl habortX0
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · -- 1. `¬ CanAbort cY0`
      have hStarAbort : ∀ cY tr cYend, StarStep cY tr cYend →
          ((∃ msg, cYend = .ub msg) ∨ (∃ err, cYend = .resourceError err)) →
          ∀ inj cX, R inj cX cY → CanAbort cX := by
        intro cY tr cYend hstar hend
        induction hstar with
        | refl c =>
          intro inj cX hR
          exact hAbort inj cX c hR hend
        | step hs _ ih =>
          intro inj cX hR
          rcases hStep inj cX _ _ _ hR hs with hAb | ⟨trX, cX', inj', _, hmv, _, hR'⟩
          · exact hAb
          · have hAb' : CanAbort cX' := ih hend inj' cX' hR'
            rcases hmv with hplus | ⟨rfl, _, _⟩
            · exact CanAbort.of_starStep (StarStep.of_plusStep hplus) hAb'
            · exact hAb'
      rintro (⟨tr, msg, hs⟩ | ⟨tr, err, hs⟩)
      · exact habortX0 (hStarAbort _ _ _ hs (Or.inl ⟨msg, rfl⟩) inj0 cX0 hR0)
      · exact habortX0 (hStarAbort _ _ _ hs (Or.inr ⟨err, rfl⟩) inj0 cX0 hR0)
    · -- 2. Terminating target executions match terminating source executions
      have hStarTerm : ∀ cY trY cYend, StarStep cY trY cYend →
          ∀ retY memY, cYend = .halted retY memY →
          ∀ inj cX, ¬ CanAbort cX → R inj cX cY →
          ∃ trX retX memX inj',
            inj.Extends inj' ∧
            Terminates cX trX retX memX ∧
            Trace.IsRefinedBy inj' trX trY ∧
            RegisterValue.IsRefinedBy inj' retX retY ∧
            MemoryState.IsRefinedBy inj' callerIds memX memY := by
        intro cY trY cYend hstar
        induction hstar with
        | refl c =>
          intro retY memY heq inj cX hnoX hR
          subst heq
          rcases hHalted inj cX retY memY hR with hAb | hRes
          · exact absurd hAb hnoX
          · exact hRes
        | step hs _ ih =>
          intro retY memY heq inj cX hnoX hR
          rcases hStep inj cX _ _ _ hR hs with hAb | ⟨trX1, cX1, inj1, hext1, hmv, htr1, hR1⟩
          · exact absurd hAb hnoX
          · have hstarX1 : StarStep cX trX1 cX1 := by
              rcases hmv with hplus | ⟨rfl, rfl, _⟩
              · exact StarStep.of_plusStep hplus
              · exact StarStep.refl _
            have hnoX1 : ¬ CanAbort cX1 := fun h => hnoX (CanAbort.of_starStep hstarX1 h)
            obtain ⟨trX2, retX, memX, inj2, hext2, htermX2, htr2, hret2, hmem2⟩ :=
              ih retY memY heq inj1 cX1 hnoX1 hR1
            exact ⟨trX1 ++ trX2, retX, memX, inj2,
              hext1.trans hext2,
              StarStep.trans hstarX1 htermX2,
              Trace.IsRefinedBy.append (Trace.IsRefinedBy.mono hext2 htr1) htr2,
              hret2,
              hmem2⟩
      intro trY retY memY htY
      obtain ⟨trX, retX, memX, inj', hext, htermX, htr, hret, hmem⟩ :=
        hStarTerm _ _ _ htY retY memY rfl inj0 cX0 habortX0 hR0
      exact ⟨trX, retX, memX, inj', hext.idOn hid0, htermX, htr, hret, hmem⟩
    · -- 3. Diverging target executions imply diverging source executions
      intro hdivY
      -- Build a `PlusStep` progress invariant `P cX := ∃ inj cY, ¬ CanAbort cX ∧ R inj cX cY ∧ Diverges cY`
      let P : Config → Prop := fun cX => ∃ inj cY, ¬ CanAbort cX ∧ R inj cX cY ∧ Diverges cY
      -- Helper: by strong induction on `m = measure cY`, any `P cX` takes ≥ 1 step to another `P cX'`
      have hAdvance : ∀ m cX inj cY, measure cY = m →
          ¬ CanAbort cX → R inj cX cY → Diverges cY →
          ∃ trX cX', PlusStep cX trX cX' ∧ P cX' := by
        intro m
        induction m using Nat.strongRecOn with
        | ind m ih =>
          intro cX inj cY hm hnoX hR hdiv
          obtain ⟨evY, cY', hsY, hdiv'⟩ := Diverges.step_inv hdiv
          rcases hStep inj cX cY evY cY' hR hsY with hAb | ⟨trX, cX', inj', _, hmv, _, hR'⟩
          · exact absurd hAb hnoX
          · rcases hmv with hplus | ⟨rfl, _, hlt⟩
            · have hnoX' : ¬ CanAbort cX' := fun h => hnoX (CanAbort.of_starStep (StarStep.of_plusStep hplus) h)
              exact ⟨trX, cX', hplus, inj', cY', hnoX', hR', hdiv'⟩
            · rw [hm] at hlt
              exact ih (measure cY') hlt cX' inj' cY' rfl hnoX hR' hdiv'
      refine Diverges.of_plusStep_progress (P := P) ?_ ⟨inj0, cY0, habortX0, hR0, hdivY⟩
      rintro cX ⟨inj, cY, hnoX, hR, hdiv⟩
      exact hAdvance (measure cY) cX inj cY rfl hnoX hR hdiv

/-! ### Module-Aware Behavioral Definition Refinement (`RefinementEnv`) -/

/--
Execution environment for behavioral refinement: semantics configuration, data layout,
and surrounding module functions and external declarations.
-/
structure RefinementEnv : Type where
  cfg   : SemanticsConfig := .modern
  dl    : AST.DataLayout := .default64LE
  fns   : AssocMap AST.FunctionId AST.Definition := ∅
  decls : AssocMap AST.FunctionId AST.Declaration := ∅

namespace RefinementEnv

/-- Default environment (`SemanticsConfig.modern`, `DataLayout.default64LE`, empty module). -/
def default : RefinementEnv := {}

/-- Extract a `RefinementEnv` (module functions & external declarations) from an `AST.TopLevel`. -/
def ofTopLevel (m : AST.TopLevel) (cfg : SemanticsConfig := .modern)
    (dl : AST.DataLayout := .default64LE) : RefinementEnv :=
  let (fns, decls) := m.entities.foldl (fun (acc : AssocMap AST.FunctionId AST.Definition × AssocMap AST.FunctionId AST.Declaration) ent =>
    match ent with
    | .definition d => (acc.1.insert d.prototype.name d, acc.2)
    | .declaration decl => (acc.1, acc.2.insert decl.name decl)
    | .global _ | .typeDef _ _ => acc) (∅, ∅)
  { cfg := cfg, dl := dl, fns := fns, decls := decls }

end RefinementEnv

/--
Full behavioral small-step semantic refinement on LLVM definitions in a `RefinementEnv`
(source `x` is refined by target `y`).

Source `x` is refined by target `y` in `env` iff:
- `x` and `y` have compatible function signatures (`Definition.SignatureCompatible x y`), and
- For every well-formed initial caller memory `initMem` and well-formed argument list `args`:
  `Config.IsRefinedBy initMem.allocIds cX cY`, where `cX` and `cY` are the initial call
  configurations of `x` and `y` in `(env.cfg, env.dl, initMem, env.fns, env.decls)`.
-/
def Definition.IsRefinedByIn (env : RefinementEnv) (x y : AST.Definition) : Prop :=
  Definition.SignatureCompatible x y ∧
  ∀ (initMem : MemoryState) (args : List RegisterValue),
    MemoryState.WellFormed initMem →
    Semantics.Definition.ArgValuesWellFormed x args →
    let cX := initCallConfig env.cfg env.dl initMem env.fns env.decls x args
    let cY := initCallConfig env.cfg env.dl initMem env.fns env.decls y args
    Config.IsRefinedBy initMem.allocIds cX cY

/-- Config/layout-parameterized refinement (standalone definition with empty module context). -/
abbrev Definition.IsRefinedByWith (cfg : SemanticsConfig) (dl : AST.DataLayout := .default64LE)
    (x y : AST.Definition) : Prop :=
  Definition.IsRefinedByIn { cfg := cfg, dl := dl } x y

/-- Config-explicit refinement notation: `x ⊒[cfg] y` (source `x` is refined by target `y`). -/
notation:50 x " ⊒[" cfg "] " y => Definition.IsRefinedByWith cfg AST.DataLayout.default64LE x y

/-- Module-environment refinement notation: `x ⊒⟨env⟩ y` (source `x` is refined by target `y` in `env`). -/
notation:50 x " ⊒⟨" env "⟩ " y => Definition.IsRefinedByIn env x y

/-- Default refinement uses `SemanticsConfig.modern` (`undef` disabled). -/
def Definition.IsRefinedBy (x y : AST.Definition) : Prop :=
  Definition.IsRefinedByIn {} x y

instance : Refinement AST.Definition where
  IsRefinedBy := Definition.IsRefinedBy

/-- Reflexivity holds for every LLVM definition in any `RefinementEnv`. -/
theorem Definition.IsRefinedByIn.refl (env : RefinementEnv) (d : AST.Definition) :
    Definition.IsRefinedByIn env d d :=
  ⟨rfl, fun initMem _ _ _ => Config.IsRefinedBy.refl initMem.allocIds _⟩

theorem Definition.IsRefinedByWith.refl (cfg : SemanticsConfig)
    (dl : AST.DataLayout := .default64LE) (d : AST.Definition) :
    Definition.IsRefinedByWith cfg dl d d :=
  Definition.IsRefinedByIn.refl { cfg := cfg, dl := dl } d

theorem Definition.IsRefinedBy.refl (d : AST.Definition) : d ⊒ d :=
  Definition.IsRefinedByIn.refl {} d

/-- Transitivity holds unconditionally via `MemoryInjection.comp`, enabling multi-pass
    refinement chaining and Lean `calc` blocks (`x ⊒ y ⊒ z`). -/
theorem Definition.IsRefinedByIn.trans {env : RefinementEnv}
    {x y z : AST.Definition}
    (hxy : Definition.IsRefinedByIn env x y)
    (hyz : Definition.IsRefinedByIn env y z) :
    Definition.IsRefinedByIn env x z := by
  obtain ⟨hsigXY, hbehXY⟩ := hxy
  obtain ⟨hsigYZ, hbehYZ⟩ := hyz
  refine ⟨hsigXY.trans hsigYZ, ?_⟩
  intro initMem args hwfMem hargsX
  have hargsY := argValuesWellFormed_of_signatureCompatible hsigXY hargsX
  exact Config.IsRefinedBy.trans (hbehXY initMem args hwfMem hargsX) (hbehYZ initMem args hwfMem hargsY)

theorem Definition.IsRefinedByWith.trans {cfg : SemanticsConfig} {dl : AST.DataLayout}
    {x y z : AST.Definition}
    (hxy : Definition.IsRefinedByWith cfg dl x y)
    (hyz : Definition.IsRefinedByWith cfg dl y z) :
    Definition.IsRefinedByWith cfg dl x z :=
  Definition.IsRefinedByIn.trans hxy hyz

theorem Definition.IsRefinedBy.trans {x y z : AST.Definition}
    (hxy : x ⊒ y) (hyz : y ⊒ z) : x ⊒ z :=
  Definition.IsRefinedByIn.trans hxy hyz

instance (env : RefinementEnv) :
    Trans (Definition.IsRefinedByIn env)
          (Definition.IsRefinedByIn env)
          (Definition.IsRefinedByIn env) where
  trans := Definition.IsRefinedByIn.trans

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

/-! ### Contextual / Common-Tail Congruence -/

/--
Common-tail congruence: if source `cX` silently steps to a shared continuation `cMid`, and
target `cY` cannot abort/terminate/diverge except through `cMid`, then `Config.IsRefinedBy callerIds cX cY`.
-/
theorem Config.IsRefinedBy.of_common_tail {callerIds : List AllocId}
    {cX cY cMid : Config}
    (hX : StarStep cX [] cMid)
    (hY_noAbort : ¬ CanAbort cMid → ¬ CanAbort cY)
    (hY_term : ∀ tr ret mem, Terminates cY tr ret mem → Terminates cMid tr ret mem)
    (hY_div : Diverges cY → Diverges cMid) :
    Config.IsRefinedBy callerIds cX cY := by
  by_cases hAb : CanAbort cMid
  · exact Or.inl (CanAbort.of_starStep hX hAb)
  · refine Or.inr ⟨hY_noAbort hAb, ?_, fun hdY => diverges_of_starStep hX (hY_div hdY)⟩
    intro trY retY memY htY
    have htMid := hY_term trY retY memY htY
    exact ⟨trY, retY, memY, .id,
      MemoryInjection.id_idOn callerIds,
      by simpa using StarStep.trans hX htMid,
      Trace.IsRefinedBy.refl trY,
      RegisterValue.IsRefinedBy.refl retY,
      MemoryState.IsRefinedBy.refl callerIds memY⟩

end LeanNanoLlvm.Refinement
