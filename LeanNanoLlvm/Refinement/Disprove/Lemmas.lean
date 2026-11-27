import LeanNanoLlvm.Refinement.Lemmas

/-! # Kernel-Pure Refutation Lemmas for `llvm_disprove`

Pure Lean lemmas that turn a concrete diverging execution into a proof of `¬ (src ⊒ tgt)`.
No meta code lives here, so the heuristics in `Disprove.Search` and `Disprove.Stepper`
can change without rebuilding these lemmas. -/

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm AST Semantics

/-! ## Section 1: Kernel-Pure Refutation Lemmas -/

/-- A halted configuration cannot abort. -/
theorem CanAbort.not_halted {v : RegisterValue} {m : MemoryState} :
    ¬ CanAbort (.halted v m) := by
  rintro (⟨tr, msg, hstar⟩ | ⟨tr, err, hstar⟩)
  all_goals
    cases hstar with
    | step hs _ => cases hs

/-- A halted configuration terminates uniquely at `(v, m)` with empty trace. -/
theorem Terminates.halted_iff {v : RegisterValue} {m : MemoryState}
    {tr : List TraceEvent} {ret : RegisterValue} {mem : MemoryState} :
    Terminates (.halted v m) tr ret mem ↔ tr = [] ∧ ret = v ∧ mem = m := by
  constructor
  · intro h
    cases h with
    | refl => exact ⟨rfl, rfl, rfl⟩
    | step hs _ => cases hs
  · rintro ⟨rfl, rfl, rfl⟩
    exact StarStep.refl _

/-- Deterministic silent step on the source side preserves `Config.IsRefinedBy`. -/
theorem Config.IsRefinedBy.det_step_left {callerIds : List AllocId}
    {stX : MachineState} {cX' cY : Config}
    (hdetX : ∀ ev c', Step (.running stX) ev c' ↔ ev = none ∧ c' = cX')
    (h : Config.IsRefinedBy callerIds (.running stX) cY) :
    Config.IsRefinedBy callerIds cX' cY := by
  rcases h with habort | ⟨hnoY, hterm, hdiv⟩
  · rw [CanAbort.of_det_step hdetX] at habort
    exact Or.inl habort
  · refine Or.inr ⟨hnoY, ?_, ?_⟩
    · intro trY retY memY htY
      obtain ⟨trX, retX, memX, inj, hid, htermX, htr, hret, hmem⟩ := hterm trY retY memY htY
      rw [terminates_of_det_step_none hdetX] at htermX
      exact ⟨trX, retX, memX, inj, hid, htermX, htr, hret, hmem⟩
    · intro hdY
      have hdX := hdiv hdY
      rw [Diverges.of_det_step hdetX] at hdX
      exact hdX

/-- Contrapositive form of `det_step_left` for refutation goals `⊢ ¬ Config.IsRefinedBy ...`. -/
theorem Config.IsRefinedBy.not_of_det_step_left {callerIds : List AllocId}
    {stX : MachineState} {cX' cY : Config}
    (hdetX : ∀ ev c', Step (.running stX) ev c' ↔ ev = none ∧ c' = cX')
    (hnot : ¬ Config.IsRefinedBy callerIds cX' cY) :
    ¬ Config.IsRefinedBy callerIds (.running stX) cY :=
  fun h => hnot (Config.IsRefinedBy.det_step_left hdetX h)

/-- Any silent step on the target side preserves `Config.IsRefinedBy`. -/
theorem Config.IsRefinedBy.step_right {callerIds : List AllocId} {cX cY cY' : Config}
    (hsY : Step cY none cY')
    (h : Config.IsRefinedBy callerIds cX cY) :
    Config.IsRefinedBy callerIds cX cY' := by
  rcases h with habort | ⟨hnoY, hterm, hdiv⟩
  · exact Or.inl habort
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · intro habY'
      exact hnoY (CanAbort.of_starStep (StarStep.single hsY) habY')
    · intro trY retY memY htY'
      exact hterm trY retY memY (StarStep.step (ev := none) hsY htY')
    · intro hdY'
      exact hdiv (Diverges.of_step hsY hdY')

/-- Contrapositive form of `step_right` for refutation goals `⊢ ¬ Config.IsRefinedBy ...`. -/
theorem Config.IsRefinedBy.not_of_step_right {callerIds : List AllocId} {cX cY cY' : Config}
    (hsY : Step cY none cY')
    (hnot : ¬ Config.IsRefinedBy callerIds cX cY') :
    ¬ Config.IsRefinedBy callerIds cX cY :=
  fun h => hnot (Config.IsRefinedBy.step_right hsY h)

/-- A halted source configuration cannot be refined by a target configuration that can abort. -/
theorem Config.IsRefinedBy.not_of_halted_left_canAbort_right {callerIds : List AllocId}
    {vX : RegisterValue} {mX : MemoryState} {cY : Config}
    (habY : CanAbort cY) :
    ¬ Config.IsRefinedBy callerIds (.halted vX mX) cY := by
  rintro (habX | ⟨hnoY, _, _⟩)
  · exact CanAbort.not_halted habX
  · exact hnoY habY

/-- A halted source configuration cannot be refined by an immediate UB target configuration. -/
theorem Config.IsRefinedBy.not_of_halted_ub {callerIds : List AllocId}
    {vX : RegisterValue} {mX : MemoryState} {msg : String} :
    ¬ Config.IsRefinedBy callerIds (.halted vX mX) (.ub msg) :=
  Config.IsRefinedBy.not_of_halted_left_canAbort_right (Or.inl ⟨[], msg, StarStep.refl _⟩)

/-- Halted-vs-halted refinement implies `RegisterValue.IsRefinedBy` on the return values. -/
theorem Config.IsRefinedBy.halted_halted_ret {callerIds : List AllocId}
    {vX vY : RegisterValue} {mX mY : MemoryState}
    (h : Config.IsRefinedBy callerIds (.halted vX mX) (.halted vY mY)) :
    ∃ inj, RegisterValue.IsRefinedBy inj vX vY := by
  rcases h with habX | ⟨_, hterm, _⟩
  · exact False.elim (CanAbort.not_halted habX)
  · obtain ⟨trX, retX, memX, inj, _, htermX, _, hret, _⟩ := hterm [] vY mY (StarStep.refl _)
    rw [Terminates.halted_iff] at htermX
    obtain ⟨_, rfl, _⟩ := htermX
    exact ⟨inj, hret⟩

/-- Halted-vs-halted bitvector refinement failure. -/
theorem Config.IsRefinedBy.not_of_halted_bv {callerIds : List AllocId}
    {w : Nat} {pX pY : PoisonOr (BitVec w)} {mX mY : MemoryState}
    (hnot : ¬ PoisonOr.IsRefinedBy pX pY) :
    ¬ Config.IsRefinedBy callerIds (.halted (.bv w pX) mX) (.halted (.bv w pY) mY) := by
  intro h
  obtain ⟨_, hret⟩ := Config.IsRefinedBy.halted_halted_ret h
  cases pX <;> cases pY <;> simp [RegisterValue.IsRefinedBy, PoisonOr.IsRefinedBy] at hret hnot
  exact hnot hret

/-- Halted-vs-halted float refinement failure. -/
theorem Config.IsRefinedBy.not_of_halted_float {callerIds : List AllocId}
    {ft : FloatType} {pX pY : PoisonOr (IEEEFloat ft.format)} {mX mY : MemoryState}
    (hnot : ¬ PoisonOr.IsRefinedBy pX pY) :
    ¬ Config.IsRefinedBy callerIds (.halted (.float ft pX) mX) (.halted (.float ft pY) mY) := by
  intro h
  obtain ⟨_, hret⟩ := Config.IsRefinedBy.halted_halted_ret h
  cases pX <;> cases pY <;> simp [RegisterValue.IsRefinedBy, PoisonOr.IsRefinedBy] at hret hnot
  exact hnot hret

/-- Refute `x ⊒ y` by exhibiting a single well-formed concrete argument list on empty memory. -/
theorem Definition.IsRefinedBy.not_of_witness {x y : AST.Definition}
    (args : List RegisterValue)
    (hargs : Semantics.Definition.ArgValuesWellFormed x args)
    (hnot : ¬ Config.IsRefinedBy ({} : MemoryState).allocIds
      (initCallConfig .modern .default64LE {} ∅ ∅ x args)
      (initCallConfig .modern .default64LE {} ∅ ∅ y args)) :
    ¬ (x ⊒ y) := by
  intro h
  exact hnot (h.2 {} args MemoryState.empty_wf hargs)

/-- `sdiv`/`udiv`/`srem`/`urem` division-by-zero or signed overflow immediately aborts. -/
theorem Step.intBinaryOp_ub_canAbort {st frame callers iid op ty e1 e2 rest v1 v2 msg}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = (iid, .intBinaryOp op ty e1 e2) :: rest)
    (he1 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty e1 = some (.ok v1))
    (he2 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty e2 = some (.ok v2))
    (hop : liftBinaryPure ty.scalarType v1 v2 (evalIntBinaryScalarPure op) = .error (.immediateUB msg)) :
    CanAbort (.running st) := by
  have hstep : Step (.running st) none (.ub msg) := by
    have hs := Step.instr hf hc (StepInstr.intBinaryOp_eval_err (.leaf_ok he1) (.leaf_ok he2) hop)
    simpa [Config.ofError] using hs
  exact Or.inl ⟨[], msg, StarStep.single hstep⟩

end LeanNanoLlvm.Refinement
