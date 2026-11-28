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
      | top_ok _ hattr => rw [retAttrsAtReturn_nil] at hattr; rw [hattr]; exact ⟨rfl, rfl⟩
      | call_ok hne _ _ _ _ => cases hne
      | noreturn_ub hne _ _ _ => cases hne
      | callee_attr_err hattr => rw [retAttrsAtReturn_nil] at hattr; rw [hattr]; exact ⟨rfl, rfl⟩
      | caller_attr_err hne _ _ _ _ => cases hne
      | missing_dest hne _ _ => cases hne
    | ret_exp_err _ he' => have hv := (EvalExp.leaf_iff he _).mp he'; cases hv
    | ret_ty_err hne => exact False.elim (hne hretTy)
  · rintro ⟨rfl, rfl⟩
    refine ⟨rfl, ?_⟩
    cases hattr : applyRetFMFAndAttrsPure st.dataLayout (freeAllocaList st.memory frame.frameAllocas)
        (.ret ty) {} frame.defn.prototype.retAttrs v with
    | ok v' => exact StepTerm.ret_ok hretTy (EvalExp.leaf_ok he) (StepRet.top_ok rfl (by rw [retAttrsAtReturn_nil]; exact hattr))
    | error err => exact StepTerm.ret_ok hretTy (EvalExp.leaf_ok he) (StepRet.callee_attr_err (by rw [retAttrsAtReturn_nil]; exact hattr))

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
      .void {} (retAttrsAtReturn frame []) .void = .ok .void := rfl
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

/-- Deterministic inversion for `conversionOp` with pure leaf operand and oracle-independent result. -/
theorem Step.conversionOp_leaf_iff {st frame callers iid op fromTy e toTy rest v res}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = (iid, .conversionOp op fromTy e toTy) :: rest)
    (h1 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory fromTy e = some (.ok v))
    (hconv : ∀ o, evalConversionExec st.dataLayout (frameDenormalCfg st frame) st.memory op fromTy v toTy o =
      .ok (res, st.memory, o))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔
      ev = none ∧ c' = finishRegInstr st frame callers rest iid res st.memory := by
  rw [Step.instr_iff hf hc]
  constructor
  · intro hi
    cases hi with
    | conversionOp_ok he1 hok =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      obtain ⟨o, o', ho⟩ := hok
      rw [hconv o] at ho; cases ho; exact ⟨rfl, rfl⟩
    | conversionOp_e_err he1 =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
    | conversionOp_eval_err he1 herr =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      obtain ⟨o, ho⟩ := herr
      rw [hconv o] at ho; cases ho
  · rintro ⟨rfl, rfl⟩
    exact StepInstr.conversionOp_ok (EvalExp.leaf_ok h1) ⟨default, default, hconv default⟩

/-- Deterministic inversion for `floatUnaryOp` with pure leaf operand and oracle-independent result. -/
theorem Step.floatUnaryOp_leaf_iff {st frame callers iid op ty e rest v res}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = (iid, .floatUnaryOp op ty e) :: rest)
    (h1 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty e = some (.ok v))
    (hfp : ∀ o, evalFloatUnaryExec op ty v o = .ok (res, o))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔
      ev = none ∧ c' = finishRegInstr st frame callers rest iid res st.memory := by
  rw [Step.instr_iff hf hc]
  constructor
  · intro hi
    cases hi with
    | floatUnaryOp_ok he1 hok =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      obtain ⟨o, o', ho⟩ := hok
      rw [hfp o] at ho; cases ho; exact ⟨rfl, rfl⟩
    | floatUnaryOp_e_err he1 =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
    | floatUnaryOp_eval_err he1 herr =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      obtain ⟨o, ho⟩ := herr
      rw [hfp o] at ho; cases ho
  · rintro ⟨rfl, rfl⟩
    exact StepInstr.floatUnaryOp_ok (EvalExp.leaf_ok h1) ⟨default, default, hfp default⟩

/-- Deterministic inversion for `freeze` of a non-poison bitvector leaf operand. -/
theorem Step.freeze_bv_val_iff {st frame callers iid ty e rest w b}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = (iid, .freeze (ty, e)) :: rest)
    (h1 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty e =
      some (.ok (.bv w (.value b))))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔
      ev = none ∧ c' = finishRegInstr st frame callers rest iid (.bv w (.value b)) st.memory := by
  rw [Step.instr_iff hf hc]
  constructor
  · intro hi
    cases hi with
    | freeze_ok he1 hfr =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      cases hfr; exact ⟨rfl, rfl⟩
    | freeze_err he1 =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
  · rintro ⟨rfl, rfl⟩
    exact StepInstr.freeze_ok (EvalExp.leaf_ok h1) (FreezeRel.bv_val w b)

/-- Stepping `freeze` of a poison bitvector leaf operand can produce any `BitVec w`
    (when `freezeMode ≠ .zero`). -/
theorem Step.freeze_bv_poison_step {st frame callers iid ty e rest w}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = (iid, .freeze (ty, e)) :: rest)
    (h1 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty e =
      some (.ok (.bv w .poison)))
    (b : BitVec w) (hmode : st.config.freezeMode = .zero → b = BitVec.ofNat w 0) :
    Step (.running st) none
      (finishRegInstr st frame callers rest iid (.bv w (.value b)) st.memory) :=
  Step.instr hf hc (StepInstr.freeze_ok (EvalExp.leaf_ok h1) (FreezeRel.bv_poison w b hmode))

/-- Inversion for `freeze` of a poison bitvector leaf operand. -/
theorem Step.freeze_bv_poison_inv {st frame callers iid ty e rest w ev c'}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = (iid, .freeze (ty, e)) :: rest)
    (h1 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty e =
      some (.ok (.bv w .poison)))
    (hs : Step (.running st) ev c') :
    ev = none ∧ ∃ b : BitVec w,
      (st.config.freezeMode = .zero → b = BitVec.ofNat w 0) ∧
      c' = finishRegInstr st frame callers rest iid (.bv w (.value b)) st.memory := by
  rw [Step.instr_iff hf hc] at hs
  cases hs with
  | freeze_ok he1 hfr =>
    have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
    cases hfr with
    | bv_poison _ b hm => exact ⟨rfl, b, hm, rfl⟩
  | freeze_err he1 =>
    have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1

theorem EvalPhis.nil_iff {dl cfg regs predId mem res} :
    EvalPhis dl cfg regs predId mem [] res ↔ res = .ok ([], mem) := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact EvalPhis.nil

theorem EvalPhis.cons_leaf_iff {dl cfg regs predId mem rid ty incs rest incExp b v ups}
    (hlook : incs.find? (fun (_, b') => b' == predId) = some (incExp, b))
    (he : evalPureLeafExp? dl cfg regs mem ty incExp = some (.ok v))
    (hrest : ∀ res, EvalPhis dl cfg regs predId mem rest res ↔ res = .ok (ups, mem))
    (res : Except ExecError (List (RawId × RegisterValue) × MemoryState)) :
    EvalPhis dl cfg regs predId mem ((.id rid, .phi ty {} incs []) :: rest) res ↔
      res = .ok ((rid, v) :: ups, mem) := by
  constructor
  · intro h
    cases h with
    | cons_ok hl' he' hfmf hmd hr' =>
      rw [hlook] at hl'; cases hl'
      have hv := (EvalExp.leaf_iff he _).mp he'; cases hv
      obtain ⟨o, o', ho⟩ := hfmf
      simp only [applyInputFMFExec_none, Except.ok.injEq, Prod.mk.injEq] at ho
      obtain ⟨rfl, _⟩ := ho
      simp only [applyValueAttrsPure_nil, Except.ok.injEq] at hmd; subst hmd
      have hru := (hrest _).mp hr'; cases hru
      rfl
    | cons_missing_pred hl' => rw [hlook] at hl'; cases hl'
    | cons_exp_err hl' he' =>
      rw [hlook] at hl'; cases hl'
      have hv := (EvalExp.leaf_iff he _).mp he'; cases hv
    | cons_fmf_err hl' he' hfmf =>
      rw [hlook] at hl'; cases hl'
      have hv := (EvalExp.leaf_iff he _).mp he'; cases hv
      obtain ⟨o, ho⟩ := hfmf; simp [applyInputFMFExec_none] at ho
    | cons_md_err hl' he' hfmf hmd =>
      rw [hlook] at hl'; cases hl'
      have hv := (EvalExp.leaf_iff he _).mp he'; cases hv
      obtain ⟨o, o', ho⟩ := hfmf
      simp only [applyInputFMFExec_none, Except.ok.injEq, Prod.mk.injEq] at ho
      obtain ⟨rfl, _⟩ := ho
      simp [applyValueAttrsPure_nil] at hmd
    | cons_tail_err hl' he' hfmf hmd hr' =>
      rw [hlook] at hl'; cases hl'
      have hv := (EvalExp.leaf_iff he _).mp he'; cases hv
      obtain ⟨o, o', ho⟩ := hfmf
      simp only [applyInputFMFExec_none, Except.ok.injEq, Prod.mk.injEq] at ho
      obtain ⟨rfl, _⟩ := ho
      simp only [applyValueAttrsPure_nil, Except.ok.injEq] at hmd; subst hmd
      have hru := (hrest _).mp hr'; cases hru
    | cons_nonphi_err hnp => exact False.elim (hnp _ _ _ _ rfl)
  · rintro rfl
    exact EvalPhis.cons_ok hlook (EvalExp.leaf_ok he) ⟨default, default, rfl⟩ rfl
      ((hrest _).mpr rfl)

theorem StepJump.det_iff {st frame callers mem dest nextBlk phis body ups c'}
    (hfind : frame.defn.findBlock? dest = some nextBlk)
    (hsplit : splitPhis nextBlk.code = (phis, body))
    (hphis : ∀ res, EvalPhis st.dataLayout st.config frame.registers frame.curBlock mem phis res ↔
      res = .ok (ups, mem)) :
    StepJump st frame callers mem dest c' ↔
      c' = .running (st.withFramesAndMemory
        (frame.jumpTo nextBlk.id body nextBlk.terminator (commitPhiUpdates frame.registers ups) :: callers)
        mem) := by
  constructor
  · intro hj
    cases hj with
    | ok hf' hs' hp' =>
      rw [hfind] at hf'; cases hf'
      rw [hsplit] at hs'; cases hs'
      have hp := (hphis _).mp hp'; cases hp
      rfl
    | phi_err hf' hs' hp' =>
      rw [hfind] at hf'; cases hf'
      rw [hsplit] at hs'; cases hs'
      have hp := (hphis _).mp hp'; cases hp
    | missing_block hf' => rw [hfind] at hf'; cases hf'
  · rintro rfl
    exact StepJump.ok hfind hsplit ((hphis _).mpr rfl)

/-- Deterministic inversion for unconditional `br label %dest`. -/
theorem Step.br_det_iff {st frame callers tid dest nextBlk phis body ups}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = [])
    (hterm : frame.terminator = (tid, .br dest))
    (hfind : frame.defn.findBlock? dest = some nextBlk)
    (hsplit : splitPhis nextBlk.code = (phis, body))
    (hphis : ∀ res, EvalPhis st.dataLayout st.config frame.registers frame.curBlock st.memory phis res ↔
      res = .ok (ups, st.memory))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔
      ev = none ∧
      c' = .running (st.withFramesAndMemory
        (frame.jumpTo nextBlk.id body nextBlk.terminator (commitPhiUpdates frame.registers ups) :: callers)
        st.memory) := by
  rw [Step.term_iff hf hc hterm]
  constructor
  · rintro ⟨rfl, ht⟩
    cases ht with
    | br_step hj => exact ⟨rfl, (StepJump.det_iff hfind hsplit hphis).mp hj⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, StepTerm.br_step ((StepJump.det_iff hfind hsplit hphis).mpr rfl)⟩

/-- Deterministic inversion for `condBr` with a concrete `i1` value leaf operand. -/
theorem Step.condBr_val_det_iff {st frame callers tid condExp tDest fDest b nextBlk phis body ups}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = [])
    (hterm : frame.terminator = (tid, .condBr condExp tDest fDest))
    (hcond : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory .i1 condExp =
      some (.ok (.bv 1 (.value b))))
    (hfind : frame.defn.findBlock? (if b != 0 then tDest else fDest) = some nextBlk)
    (hsplit : splitPhis nextBlk.code = (phis, body))
    (hphis : ∀ res, EvalPhis st.dataLayout st.config frame.registers frame.curBlock st.memory phis res ↔
      res = .ok (ups, st.memory))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔
      ev = none ∧
      c' = .running (st.withFramesAndMemory
        (frame.jumpTo nextBlk.id body nextBlk.terminator (commitPhiUpdates frame.registers ups) :: callers)
        st.memory) := by
  rw [Step.term_iff hf hc hterm]
  constructor
  · rintro ⟨rfl, ht⟩
    cases ht with
    | condBr_ok he hj =>
      have hv := (EvalExp.leaf_iff hcond _).mp he; cases hv
      exact ⟨rfl, (StepJump.det_iff hfind hsplit hphis).mp hj⟩
    | condBr_poison he =>
      have hv := (EvalExp.leaf_iff hcond _).mp he; cases hv
    | condBr_err he =>
      have hv := (EvalExp.leaf_iff hcond _).mp he; cases hv
    | condBr_nonbool he hnb =>
      have hv := (EvalExp.leaf_iff hcond _).mp he; cases hv
      exact False.elim (hnb _ rfl)
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, StepTerm.condBr_ok (EvalExp.leaf_ok hcond)
      ((StepJump.det_iff hfind hsplit hphis).mpr rfl)⟩

/-- Branching on `poison` immediately causes UB (`CanAbort`). -/
theorem Step.condBr_poison_canAbort {st frame callers tid condExp tDest fDest}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = [])
    (hterm : frame.terminator = (tid, .condBr condExp tDest fDest))
    (hcond : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory .i1 condExp =
      some (.ok (.bv 1 .poison))) :
    CanAbort (.running st) :=
  Or.inl ⟨[], "Branch on poison condition",
    StarStep.single (Step.term hf hc hterm (StepTerm.condBr_poison (EvalExp.leaf_ok hcond)))⟩

/-- Deterministic single-step characterization of `switch` when its selector is a concrete bitvector. -/
theorem Step.switch_val_det_iff {st frame callers tid ty condExp defDest cases w bv nextBlk phis body ups}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = [])
    (hterm : frame.terminator = (tid, .switch ty condExp defDest cases))
    (hcond : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty condExp =
      some (.ok (.bv w (.value bv))))
    (hfind : frame.defn.findBlock?
      (match cases.find? (fun (cv, _) => BitVec.ofInt w cv == bv) with
       | some (_, lbl) => lbl
       | none => defDest) = some nextBlk)
    (hsplit : splitPhis nextBlk.code = (phis, body))
    (hphis : ∀ res, EvalPhis st.dataLayout st.config frame.registers frame.curBlock st.memory phis res ↔
      res = .ok (ups, st.memory))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔
      ev = none ∧
      c' = .running (st.withFramesAndMemory
        (frame.jumpTo nextBlk.id body nextBlk.terminator (commitPhiUpdates frame.registers ups) :: callers)
        st.memory) := by
  rw [Step.term_iff hf hc hterm]
  constructor
  · rintro ⟨rfl, ht⟩
    cases ht with
    | switch_ok he hj =>
      have hv := (EvalExp.leaf_iff hcond _).mp he; cases hv
      exact ⟨rfl, (StepJump.det_iff hfind hsplit hphis).mp hj⟩
    | switch_poison he =>
      have hv := (EvalExp.leaf_iff hcond _).mp he; cases hv
    | switch_err he =>
      have hv := (EvalExp.leaf_iff hcond _).mp he; cases hv
    | switch_nonint he hni =>
      have hv := (EvalExp.leaf_iff hcond _).mp he; cases hv
      exact False.elim (hni _ _ rfl)
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, StepTerm.switch_ok (EvalExp.leaf_ok hcond)
      ((StepJump.det_iff hfind hsplit hphis).mpr rfl)⟩

/-- Switching on `poison` immediately causes UB (`CanAbort`). -/
theorem Step.switch_poison_canAbort {st frame callers tid ty condExp defDest cases w}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = [])
    (hterm : frame.terminator = (tid, .switch ty condExp defDest cases))
    (hcond : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty condExp =
      some (.ok (.bv w .poison))) :
    CanAbort (.running st) :=
  Or.inl ⟨[], "Switch on poison condition",
    StarStep.single (Step.term hf hc hterm (StepTerm.switch_poison (EvalExp.leaf_ok hcond)))⟩

end LeanNanoLlvm.Semantics
