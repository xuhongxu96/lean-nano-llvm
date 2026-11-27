import LeanNanoLlvm.Semantics.Step

/-!
# Inversion lemmas for `Step`

Lemmas that characterize the steps from particular configurations (terminal configurations,
and one lemma per opcode for deterministic instructions). Refinement proofs use them to compute
executions without unfolding `Step`.
-/

namespace LeanNanoLlvm.Semantics

open AST

/-! ### Terminal Configuration & Deterministic-Step Inversion Lemmas -/

theorem Step.not_halted {v mem ev c'} : ¬ Step (.halted v mem) ev c' := by intro h; cases h
theorem Step.not_ub {msg ev c'} : ¬ Step (.ub msg) ev c' := by intro h; cases h
theorem Step.not_staticError {msg ev c'} : ¬ Step (.staticError msg) ev c' := by intro h; cases h
theorem Step.not_resourceError {err ev c'} : ¬ Step (.resourceError err) ev c' := by intro h; cases h

theorem StarStep.halted_inv {v mem tr c'} (h : StarStep (.halted v mem) tr c') :
    tr = [] ∧ c' = .halted v mem := by
  cases h with
  | refl _ => exact ⟨rfl, rfl⟩
  | step hs _ => exact False.elim (Step.not_halted hs)

theorem StarStep.ub_inv {msg tr c'} (h : StarStep (.ub msg) tr c') :
    tr = [] ∧ c' = .ub msg := by
  cases h with
  | refl _ => exact ⟨rfl, rfl⟩
  | step hs _ => exact False.elim (Step.not_ub hs)

theorem StarStep.staticError_inv {msg tr c'} (h : StarStep (.staticError msg) tr c') :
    tr = [] ∧ c' = .staticError msg := by
  cases h with
  | refl _ => exact ⟨rfl, rfl⟩
  | step hs _ => exact False.elim (Step.not_staticError hs)

theorem StarStep.resourceError_inv {err tr c'} (h : StarStep (.resourceError err) tr c') :
    tr = [] ∧ c' = .resourceError err := by
  cases h with
  | refl _ => exact ⟨rfl, rfl⟩
  | step hs _ => exact False.elim (Step.not_resourceError hs)

theorem not_canUB_halted {v mem} : ¬ CanUB (.halted v mem) := by
  rintro ⟨tr, msg, h⟩; obtain ⟨_, heq⟩ := StarStep.halted_inv h; cases heq

theorem not_canResourceError_halted {v mem} : ¬ CanResourceError (.halted v mem) := by
  rintro ⟨tr, err, h⟩; obtain ⟨_, heq⟩ := StarStep.halted_inv h; cases heq

theorem not_canAbort_halted {v mem} : ¬ CanAbort (.halted v mem) := by
  rintro (h | h)
  · exact not_canUB_halted h
  · exact not_canResourceError_halted h

theorem not_diverges_halted {v mem} : ¬ Diverges (.halted v mem) := by
  rintro ⟨f, ev, h0, hstep⟩; have h1 := hstep 0; rw [h0] at h1; exact Step.not_halted h1

theorem not_diverges_ub {msg} : ¬ Diverges (.ub msg) := by
  rintro ⟨f, ev, h0, hstep⟩; have h1 := hstep 0; rw [h0] at h1; exact Step.not_ub h1

theorem not_diverges_staticError {msg} : ¬ Diverges (.staticError msg) := by
  rintro ⟨f, ev, h0, hstep⟩; have h1 := hstep 0; rw [h0] at h1; exact Step.not_staticError h1

theorem not_diverges_resourceError {err} : ¬ Diverges (.resourceError err) := by
  rintro ⟨f, ev, h0, hstep⟩; have h1 := hstep 0; rw [h0] at h1; exact Step.not_resourceError h1

theorem Diverges.of_step {c ev c'} (hs : Step c ev c') (hd : Diverges c') : Diverges c := by
  obtain ⟨f, evf, h0, hstep⟩ := hd
  refine ⟨fun n => match n with | 0 => c | k + 1 => f k,
          fun n => match n with | 0 => ev | k + 1 => evf k, rfl, ?_⟩
  intro n
  cases n with
  | zero => simpa [h0] using hs
  | succ k => exact hstep k

theorem Diverges.step_inv {c} (hd : Diverges c) : ∃ ev c', Step c ev c' ∧ Diverges c' := by
  obtain ⟨f, evf, h0, hstep⟩ := hd
  have hs0 : Step c (evf 0) (f 1) := h0 ▸ hstep 0
  exact ⟨evf 0, f 1, hs0, ⟨fun n => f (n + 1), fun n => evf (n + 1), rfl, fun n => hstep (n + 1)⟩⟩

theorem CanAbort.of_starStep {c1 tr c2} (hstar : StarStep c1 tr c2) (ha : CanAbort c2) :
    CanAbort c1 := by
  rcases ha with ⟨tr', msg, h⟩ | ⟨tr', err, h⟩
  · exact Or.inl ⟨tr ++ tr', msg, StarStep.trans hstar h⟩
  · exact Or.inr ⟨tr ++ tr', err, StarStep.trans hstar h⟩

/-- Coinductive construction of `Diverges` from a single-step progress invariant. -/
theorem Diverges.of_progress {P : Config → Prop}
    (hprog : ∀ c, P c → ∃ ev c', Step c ev c' ∧ P c')
    {c0 : Config} (h0 : P c0) : Diverges c0 := by
  let stepEv : ∀ s : { c : Config // P c }, Option TraceEvent :=
    fun s => Classical.choose (hprog s.1 s.2)
  let stepNext : ∀ s : { c : Config // P c }, { c : Config // P c } :=
    fun s =>
      let h1 := Classical.choose_spec (hprog s.1 s.2)
      ⟨Classical.choose h1, (Classical.choose_spec h1).2⟩
  let stepProof : ∀ s : { c : Config // P c }, Step s.1 (stepEv s) (stepNext s).1 :=
    fun s =>
      let h1 := Classical.choose_spec (hprog s.1 s.2)
      (Classical.choose_spec h1).1
  let seq : Nat → { c : Config // P c } :=
    Nat.rec ⟨c0, h0⟩ (fun _ prev => stepNext prev)
  exact ⟨fun n => (seq n).1, fun n => stepEv (seq n), rfl, fun n => stepProof (seq n)⟩

/-- Coinductive construction of `Diverges` from a `PlusStep` (≥ 1 step) progress invariant. -/
theorem Diverges.of_plusStep_progress {P : Config → Prop}
    (hprog : ∀ c, P c → ∃ tr c', PlusStep c tr c' ∧ P c')
    {c0 : Config} (h0 : P c0) : Diverges c0 := by
  let Q : Config → Prop := fun c => ∃ tr cEnd, StarStep c tr cEnd ∧ P cEnd
  refine Diverges.of_progress (P := Q) ?_ ⟨[], c0, StarStep.refl c0, h0⟩
  rintro c ⟨tr, cEnd, hstar, hp⟩
  cases hstar with
  | refl _ =>
    obtain ⟨tr', cEnd', ⟨ev, cm, tr2, hs, hrest, _⟩, hp'⟩ := hprog c hp
    exact ⟨ev, cm, hs, tr2, cEnd', hrest, hp'⟩
  | step hs hrest =>
    exact ⟨_, _, hs, _, cEnd, hrest, hp⟩

theorem StarStep.of_det_step {st : MachineState} {ev0 : Option TraceEvent} {c1 : Config}
    (hdet : ∀ ev c', Step (.running st) ev c' ↔ ev = ev0 ∧ c' = c1)
    {tr : List TraceEvent} {v : RegisterValue} {m : MemoryState} :
    StarStep (.running st) tr (.halted v m) ↔
      ∃ tr', tr = ev0.toList ++ tr' ∧ StarStep c1 tr' (.halted v m) := by
  constructor
  · intro h
    cases h with
    | step hs hrest =>
      obtain ⟨rfl, rfl⟩ := (hdet _ _).mp hs
      exact ⟨_, rfl, hrest⟩
  · rintro ⟨tr', rfl, hrest⟩
    exact StarStep.step ((hdet ev0 c1).mpr ⟨rfl, rfl⟩) hrest

theorem CanUB.of_det_step {st : MachineState} {ev0 : Option TraceEvent} {c1 : Config}
    (hdet : ∀ ev c', Step (.running st) ev c' ↔ ev = ev0 ∧ c' = c1) :
    CanUB (.running st) ↔ CanUB c1 := by
  constructor
  · rintro ⟨tr, msg, h⟩
    cases h with
    | step hs hrest => obtain ⟨rfl, rfl⟩ := (hdet _ _).mp hs; exact ⟨_, msg, hrest⟩
  · rintro ⟨tr, msg, h⟩
    exact ⟨ev0.toList ++ tr, msg, StarStep.step ((hdet ev0 c1).mpr ⟨rfl, rfl⟩) h⟩

theorem CanResourceError.of_det_step {st : MachineState} {ev0 : Option TraceEvent} {c1 : Config}
    (hdet : ∀ ev c', Step (.running st) ev c' ↔ ev = ev0 ∧ c' = c1) :
    CanResourceError (.running st) ↔ CanResourceError c1 := by
  constructor
  · rintro ⟨tr, err, h⟩
    cases h with
    | step hs hrest => obtain ⟨rfl, rfl⟩ := (hdet _ _).mp hs; exact ⟨_, err, hrest⟩
  · rintro ⟨tr, err, h⟩
    exact ⟨ev0.toList ++ tr, err, StarStep.step ((hdet ev0 c1).mpr ⟨rfl, rfl⟩) h⟩

theorem CanAbort.of_det_step {st : MachineState} {ev0 : Option TraceEvent} {c1 : Config}
    (hdet : ∀ ev c', Step (.running st) ev c' ↔ ev = ev0 ∧ c' = c1) :
    CanAbort (.running st) ↔ CanAbort c1 := by
  simp only [CanAbort, CanUB.of_det_step hdet, CanResourceError.of_det_step hdet]

theorem Diverges.of_det_step {st : MachineState} {ev0 : Option TraceEvent} {c1 : Config}
    (hdet : ∀ ev c', Step (.running st) ev c' ↔ ev = ev0 ∧ c' = c1) :
    Diverges (.running st) ↔ Diverges c1 := by
  constructor
  · intro hd
    obtain ⟨ev, c', hs, hd'⟩ := Diverges.step_inv hd
    obtain ⟨rfl, rfl⟩ := (hdet _ _).mp hs
    exact hd'
  · intro hd
    exact Diverges.of_step ((hdet ev0 c1).mpr ⟨rfl, rfl⟩) hd

/-! ### Fast Indexed Inversion Lemmas (O(1) per opcode!) -/

theorem Step.instr_iff {st frame callers iid instr rest ev c'}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = (iid, instr) :: rest) :
    Step (.running st) ev c' ↔ StepInstr st frame callers iid rest instr ev c' := by
  constructor
  · intro hs
    cases hs with
    | empty_stack he => rw [hf] at he; cases he
    | instr hf' hc' hi => rw [hf] at hf'; cases hf'; rw [hc] at hc'; cases hc'; exact hi
    | term hf' hc' _ _ => rw [hf] at hf'; cases hf'; rw [hc] at hc'; cases hc'
  · exact Step.instr hf hc

theorem Step.term_iff {st frame callers tid term ev c'}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = [])
    (ht : frame.terminator = (tid, term)) :
    Step (.running st) ev c' ↔ ev = none ∧ StepTerm st frame callers tid term c' := by
  constructor
  · intro hs
    cases hs with
    | empty_stack he => rw [hf] at he; cases he
    | instr hf' hc' _ => rw [hf] at hf'; cases hf'; rw [hc] at hc'; cases hc'
    | term hf' hc' ht' hst =>
      rw [hf] at hf'; cases hf'; rw [ht] at ht'; cases ht'
      exact ⟨rfl, hst⟩
  · rintro ⟨rfl, hst⟩
    exact Step.term hf hc ht hst

theorem EvalExp.leaf_iff {dl cfg regs mem ty e v}
    (h : evalPureLeafExp? dl cfg regs mem ty e = some (.ok v))
    (res : Except ExecError (RegisterValue × MemoryState)) :
    EvalExp dl cfg regs mem ty e res ↔ res = .ok (v, mem) := by
  constructor
  · intro he
    cases he with
    | leaf_ok h' => rw [h] at h'; cases h'; rfl
    | leaf_err h' => rw [h] at h'; cases h'
    | _ => simp [evalPureLeafExp?] at h
  · rintro rfl; exact EvalExp.leaf_ok h

theorem EvalExp.undef_iff {dl cfg regs mem ty} (hallow : cfg.allowUndef = true)
    (hnoFn : ty.hasFunction = false)
    (res : Except ExecError (RegisterValue × MemoryState)) :
    EvalExp dl cfg regs mem ty .undef res ↔ ∃ v, res = .ok (v, mem) ∧ UndefValRel dl cfg ty v := by
  constructor
  · intro he
    cases he with
    | leaf_ok h' => simp [evalPureLeafExp?] at h'
    | leaf_err h' => simp [evalPureLeafExp?] at h'
    | undef_ok _ hu => exact ⟨_, rfl, hu⟩
    | undef_err hbad =>
      rcases hbad with hd | hfn
      · simp [SemanticsConfig.allowUndef, hd] at hallow
      · rw [hnoFn] at hfn; cases hfn
  · rintro ⟨v, rfl, hu⟩
    exact EvalExp.undef_ok hallow hu

/-- Deterministic inversion for `intBinaryOp` with pure leaf operands. -/
theorem Step.intBinaryOp_leaf_iff {st frame callers iid op ty e1 e2 rest v1 v2}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = (iid, .intBinaryOp op ty e1 e2) :: rest)
    (h1 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty e1 = some (.ok v1))
    (h2 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty e2 = some (.ok v2))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔
      ev = none ∧
      c' = match liftBinaryPure ty.scalarType v1 v2 (evalIntBinaryScalarPure op) with
           | .ok res => finishRegInstr st frame callers rest iid res st.memory
           | .error err => Config.ofError err := by
  rw [Step.instr_iff hf hc]
  constructor
  · intro hi
    cases hi with
    | intBinaryOp_ok he1 he2 hbin =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
      rw [hbin]; exact ⟨rfl, rfl⟩
    | intBinaryOp_e1_err he1 => have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
    | intBinaryOp_e2_err he1 he2 =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
    | intBinaryOp_eval_err he1 he2 hbin =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
      rw [hbin]; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    cases hbin : liftBinaryPure ty.scalarType v1 v2 (evalIntBinaryScalarPure op) with
    | ok res => exact StepInstr.intBinaryOp_ok (EvalExp.leaf_ok h1) (EvalExp.leaf_ok h2) hbin
    | error err => exact StepInstr.intBinaryOp_eval_err (EvalExp.leaf_ok h1) (EvalExp.leaf_ok h2) hbin

/-- Deterministic inversion for `icmp` with pure leaf operands. -/
theorem Step.icmp_leaf_iff {st frame callers iid ss pred ty e1 e2 rest v1 v2}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = (iid, .icmp ss pred ty e1 e2) :: rest)
    (h1 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty e1 = some (.ok v1))
    (h2 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty e2 = some (.ok v2))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔
      ev = none ∧
      c' = match liftBinaryPure .i1 v1 v2 (evalICmpScalarPure st.dataLayout ss pred) with
           | .ok res => finishRegInstr st frame callers rest iid res st.memory
           | .error err => Config.ofError err := by
  rw [Step.instr_iff hf hc]
  constructor
  · intro hi
    cases hi with
    | icmp_ok he1 he2 hcmp =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
      rw [hcmp]; exact ⟨rfl, rfl⟩
    | icmp_e1_err he1 => have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
    | icmp_e2_err he1 he2 =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
    | icmp_eval_err he1 he2 hcmp =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
      rw [hcmp]; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    cases hcmp : liftBinaryPure .i1 v1 v2 (evalICmpScalarPure st.dataLayout ss pred) with
    | ok res => exact StepInstr.icmp_ok (EvalExp.leaf_ok h1) (EvalExp.leaf_ok h2) hcmp
    | error err => exact StepInstr.icmp_eval_err (EvalExp.leaf_ok h1) (EvalExp.leaf_ok h2) hcmp

/-- Deterministic inversion for `select` (no FMF) with pure leaf operands. -/
theorem Step.select_leaf_iff {st frame callers iid condTy cond valTy tv fv rest cV tV fV}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = (iid, .select {} condTy cond valTy tv fv) :: rest)
    (h1 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory condTy cond = some (.ok cV))
    (h2 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory valTy tv = some (.ok tV))
    (h3 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory valTy fv = some (.ok fV))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔
      ev = none ∧
      c' = match evalSelectPure cV tV fV with
           | .ok res => finishRegInstr st frame callers rest iid res st.memory
           | .error err => Config.ofError err := by
  rw [Step.instr_iff hf hc]
  constructor
  · intro hi
    cases hi with
    | select_ok he1 he2 he3 hsel hfmf =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
      have hv3 := (EvalExp.leaf_iff h3 _).mp he3; cases hv3
      obtain ⟨o, o', hfo⟩ := hfmf
      simp only [applyInputFMFExec_none, Except.ok.injEq, Prod.mk.injEq] at hfo
      obtain ⟨rfl, _⟩ := hfo
      rw [hsel]; exact ⟨rfl, rfl⟩
    | select_cond_err he1 => have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
    | select_tv_err he1 he2 =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
    | select_fv_err he1 he2 he3 =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
      have hv3 := (EvalExp.leaf_iff h3 _).mp he3; cases hv3
    | select_eval_err he1 he2 he3 hsel =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
      have hv3 := (EvalExp.leaf_iff h3 _).mp he3; cases hv3
      rw [hsel]; exact ⟨rfl, rfl⟩
    | select_fmf_err _ _ _ _ hfmf =>
      obtain ⟨o, hfo⟩ := hfmf; simp [applyInputFMFExec_none] at hfo
  · rintro ⟨rfl, rfl⟩
    cases hsel : evalSelectPure cV tV fV with
    | ok res =>
      exact StepInstr.select_ok (EvalExp.leaf_ok h1) (EvalExp.leaf_ok h2) (EvalExp.leaf_ok h3) hsel
        ⟨default, default, rfl⟩
    | error err =>
      exact StepInstr.select_eval_err (EvalExp.leaf_ok h1) (EvalExp.leaf_ok h2) (EvalExp.leaf_ok h3) hsel

/-- Deterministic inversion for `store` with pure leaf operands and concrete pointer. -/
theorem Step.store_leaf_iff {st frame callers iid valTy valExp ptrTy ptrExp align? isVol rest val as p}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = (iid, .store valTy valExp ptrTy ptrExp align? isVol) :: rest)
    (h1 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory valTy valExp = some (.ok val))
    (h2 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ptrTy ptrExp = some (.ok (.ptr as (.value p))))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔
      match st.memory.verifyMemAccess p (st.dataLayout.typeStoreSize valTy)
              (align?.getD (st.dataLayout.typeABIAlign valTy)) true with
      | .ok (mo, offset) =>
        ev = (if isVol then some (.volatileStore mo.addrSpace p.addr.toNat
                (valueToBytes st.dataLayout st.config val valTy)) else none) ∧
        c' = finishVoidInstr st frame callers rest
               ((st.memory.bindWildcard p.prov mo.allocId).writeObjectBytes mo.allocId offset (valueToBytes st.dataLayout st.config val valTy))
      | .error err =>
        ev = none ∧ c' = Config.ofError err := by
  rw [Step.instr_iff hf hc]
  constructor
  · intro hi
    cases hi with
    | store_ok he1 he2 hver =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
      rw [hver]; exact ⟨rfl, rfl⟩
    | store_val_err he1 => have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
    | store_ptr_err he1 he2 =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
    | store_ptr_poison he1 he2 =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
    | store_ptr_nonptr he1 he2 hnp =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
      exact False.elim (hnp _ _ rfl)
    | store_mem_err he1 he2 hver =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
      rw [hver]; exact ⟨rfl, rfl⟩
  · intro hrhs
    cases hver : st.memory.verifyMemAccess p (st.dataLayout.typeStoreSize valTy)
        (align?.getD (st.dataLayout.typeABIAlign valTy)) true with
    | ok pair =>
      rw [hver] at hrhs; obtain ⟨rfl, rfl⟩ := hrhs
      exact StepInstr.store_ok (EvalExp.leaf_ok h1) (EvalExp.leaf_ok h2) hver
    | error err =>
      rw [hver] at hrhs; obtain ⟨rfl, rfl⟩ := hrhs
      exact StepInstr.store_mem_err (EvalExp.leaf_ok h1) (EvalExp.leaf_ok h2) hver

/-- Deterministic inversion for top-level `ret ty e` with a pure leaf operand. -/
theorem Step.ret_top_leaf_iff {st frame tid ty e v}
    (hf : st.frames = [frame])
    (hc : frame.remainingCode = [])
    (hretTy : frame.defn.retType? = some (.ret ty))
    (hterm : frame.terminator = (tid, .ret (ty, e)))
    (he : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty e = some (.ok v))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔
      ev = none ∧
      c' = match applyRetFMFAndAttrsPure st.dataLayout (freeAllocaList st.memory frame.frameAllocas)
                   (.ret ty) {} frame.defn.prototype.retAttrs v with
           | .ok v' => .halted v' (freeAllocaList st.memory frame.frameAllocas)
           | .error err => Config.ofError err := by
  rw [Step.term_iff hf hc hterm]
  constructor
  · rintro ⟨rfl, ht⟩
    cases ht with
    | ret_ok _ he' hr =>
      have hv := (EvalExp.leaf_iff he _).mp he'; cases hv
      cases hr with
      | top_ok _ hattr => rw [hattr]; exact ⟨rfl, rfl⟩
      | call_ok hne _ _ _ _ => cases hne
      | noreturn_ub hne _ _ _ => cases hne
      | callee_attr_err hattr => rw [hattr]; exact ⟨rfl, rfl⟩
      | caller_attr_err hne _ _ _ _ => cases hne
      | missing_dest hne _ _ => cases hne
    | ret_exp_err _ he' => have hv := (EvalExp.leaf_iff he _).mp he'; cases hv
    | ret_ty_err hne => exact False.elim (hne hretTy)
  · rintro ⟨rfl, rfl⟩
    refine ⟨rfl, ?_⟩
    cases hattr : applyRetFMFAndAttrsPure st.dataLayout (freeAllocaList st.memory frame.frameAllocas)
        (.ret ty) {} frame.defn.prototype.retAttrs v with
    | ok v' => exact StepTerm.ret_ok hretTy (EvalExp.leaf_ok he) (StepRet.top_ok rfl hattr)
    | error err => exact StepTerm.ret_ok hretTy (EvalExp.leaf_ok he) (StepRet.callee_attr_err hattr)

/-- Deterministic inversion for top-level `ret void`. -/
theorem Step.retVoid_top_iff {st frame tid}
    (hf : st.frames = [frame])
    (hc : frame.remainingCode = [])
    (hretTy : frame.defn.retType? = some .void)
    (hterm : frame.terminator = (tid, .retVoid))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔
      ev = none ∧
      c' = .halted .void (freeAllocaList st.memory frame.frameAllocas) := by
  have hattr : applyRetFMFAndAttrsPure st.dataLayout (freeAllocaList st.memory frame.frameAllocas)
      .void {} frame.defn.prototype.retAttrs .void = .ok .void := rfl
  rw [Step.term_iff hf hc hterm]
  constructor
  · rintro ⟨rfl, ht⟩
    cases ht with
    | retVoid_ok _ hr =>
      cases hr with
      | top_ok _ hattr' => rw [hattr] at hattr'; cases hattr'; exact ⟨rfl, rfl⟩
      | call_ok hne _ _ _ _ => cases hne
      | noreturn_ub hne _ _ _ => cases hne
      | callee_attr_err hattr' => rw [hattr] at hattr'; cases hattr'
      | caller_attr_err hne _ _ _ _ => cases hne
      | missing_dest hne _ _ => cases hne
    | retVoid_ty_err hne => exact False.elim (hne hretTy)
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, StepTerm.retVoid_ok hretTy (StepRet.top_ok rfl hattr)⟩

/-- Deterministic inversion for `unreachable`. -/
theorem Step.unreachable_iff {st frame callers tid}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = [])
    (hterm : frame.terminator = (tid, .unreachable))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔ ev = none ∧ ∃ msg, c' = .ub msg := by
  rw [Step.term_iff hf hc hterm]
  constructor
  · rintro ⟨rfl, ht⟩
    cases ht with
    | unreachable_ub => exact ⟨rfl, _, rfl⟩
  · rintro ⟨rfl, msg, rfl⟩
    exact ⟨rfl, StepTerm.unreachable_ub⟩

end LeanNanoLlvm.Semantics
