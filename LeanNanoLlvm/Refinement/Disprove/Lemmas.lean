import LeanNanoLlvm.Refinement.Lemmas
import LeanNanoLlvm.Semantics.Exec

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


/-! ## Section 2: Target Behaviours From the Executable Interpreter

A refutation needs one behaviour of the target that the source cannot match. Any run of the
executable interpreter is such a behaviour (`runSteps_sound`), so the target side is certified by
evaluating `runSteps` in the kernel, whatever instructions it executes; only the source side,
whose behaviours must all be known, is stepped with deterministic-step lemmas. -/

/-- `c` is an abort (immediate UB or a resource error). -/
def _root_.LeanNanoLlvm.Semantics.Config.isAbortB : Config → Bool
  | .ub _ | .resourceError _ => true
  | _ => false

/-- The return value of a halted configuration. -/
def _root_.LeanNanoLlvm.Semantics.Config.haltedVal? : Config → Option RegisterValue
  | .halted v _ => some v
  | _ => none

/-- The initial configuration of a call on empty memory is well-formed. -/
theorem initCallConfig_empty_wf (cfg : SemanticsConfig) (dl : DataLayout)
    (fns : AssocMap FunctionId AST.Definition) (decls : AssocMap FunctionId AST.Declaration)
    (defn : AST.Definition) (args : List RegisterValue) :
    Config.WellFormed (initCallConfig cfg dl {} fns decls defn args) := by
  unfold initCallConfig
  cases h : mkEntryFrameWithMem dl cfg {} defn args with
  | ok r =>
    obtain ⟨frame', mem'⟩ := r
    exact mkEntryFrameWithMem_preserves_wf MemoryState.empty_wf h
  | error e => cases e <;> trivial

/-- An interpreter run that aborts shows that the configuration can abort. -/
theorem CanAbort.of_runSteps (fuel : Nat) (o : OracleState) {c : Config}
    (hwf : Config.WellFormed c) (h : (runSteps fuel o c).2.1.isAbortB = true) : CanAbort c := by
  have hs := runSteps_sound fuel o c hwf
  revert h hs
  generalize (runSteps fuel o c).2.1 = cf
  generalize (runSteps fuel o c).1 = tr
  intro h hs
  cases cf with
  | ub msg => exact Or.inl ⟨tr, msg, hs⟩
  | resourceError err => exact Or.inr ⟨tr, err, hs⟩
  | _ => simp [Config.isAbortB] at h

/-- An interpreter run that halts with `v` emitting no events is a termination. -/
theorem Terminates.of_runSteps (fuel : Nat) (o : OracleState) {c : Config} {v : RegisterValue}
    (hwf : Config.WellFormed c) (htr : (runSteps fuel o c).1 = [])
    (h : (runSteps fuel o c).2.1.haltedVal? = some v) : ∃ m, Terminates c [] v m := by
  have hs := runSteps_sound fuel o c hwf
  rw [htr] at hs
  revert h hs
  generalize (runSteps fuel o c).2.1 = cf
  intro h hs
  cases cf with
  | halted v' m =>
    simp only [Config.haltedVal?, Option.some.injEq] at h
    subst h
    exact ⟨m, hs⟩
  | _ => simp [Config.haltedVal?] at h

/-- If the target can abort, refuting against it is refuting against an immediate-UB target:
both are refined exactly when the source can abort. -/
theorem Config.IsRefinedBy.not_of_canAbort_right {callerIds : List AllocId} {cX cY : Config}
    (habY : CanAbort cY) (h : ¬ Config.IsRefinedBy callerIds cX (.ub "")) :
    ¬ Config.IsRefinedBy callerIds cX cY := by
  rintro (habX | ⟨hnoY, _, _⟩)
  · exact h (Or.inl habX)
  · exact hnoY habY

/-- If the target can terminate with `vY` (no events), refuting against it reduces to refuting
against a target that has halted with `vY`, whatever its memory. -/
theorem Config.IsRefinedBy.not_of_terminates_right {callerIds : List AllocId} {cX cY : Config}
    {vY : RegisterValue} (hT : ∃ m, Terminates cY [] vY m)
    (h : ∀ m, ¬ Config.IsRefinedBy callerIds cX (.halted vY m)) :
    ¬ Config.IsRefinedBy callerIds cX cY := by
  obtain ⟨mY, hT⟩ := hT
  rintro (habX | ⟨_, hterm, _⟩)
  · exact h mY (Or.inl habX)
  · refine h mY (Or.inr ⟨CanAbort.not_halted, ?_, ?_⟩)
    · intro trY retY memY ht
      rw [Terminates.halted_iff] at ht
      obtain ⟨rfl, rfl, rfl⟩ := ht
      exact hterm _ _ _ hT
    · rintro ⟨f, ev, h0, hs⟩
      have h1 := hs 0
      rw [h0] at h1
      cases h1


/-! ## Section 3: Deterministic Intrinsic Calls on the Source Side -/

/-- The values of call arguments that are all pure leaves (constants or registers) with
attributes that do not fail; `none` otherwise. -/
def leafCallArgs? (dl : DataLayout) (cfg : SemanticsConfig) (regs : AssocMap AST.Identifier RegisterValue)
    (mem : MemoryState) : List (AST.LlvmType × AST.Exp × List AST.ValueAttr) → Option (List RegisterValue)
  | [] => some []
  | (ty, e, attrs) :: rest =>
    match evalPureLeafExp? dl cfg regs mem ty e with
    | some (.ok rawV) =>
      match applyValueAttrsPure dl mem ty rawV (byvalDeferredAttrs attrs) with
      | .ok v => (leafCallArgs? dl cfg regs mem rest).map (v :: ·)
      | .error _ => none
    | _ => none

theorem EvalCallArgs.leaf_iff {dl cfg regs mem} :
    ∀ {args : List (AST.LlvmType × AST.Exp × List AST.ValueAttr)} {vs : List RegisterValue},
    leafCallArgs? dl cfg regs mem args = some vs →
    ∀ res, EvalCallArgs dl cfg regs mem args res ↔ res = .ok (vs, mem)
  | [], vs, h, res => by
    simp only [leafCallArgs?, Option.some.injEq] at h
    subst h
    constructor
    · intro he; cases he; rfl
    · rintro rfl; exact EvalCallArgs.nil
  | (ty, e, attrs) :: rest, vs, h, res => by
    simp only [leafCallArgs?] at h
    split at h
    · rename_i rawV hleaf
      split at h
      · rename_i v hattr
        cases hrest : leafCallArgs? dl cfg regs mem rest with
        | none => rw [hrest] at h; cases h
        | some vs' =>
          rw [hrest] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          have ih := EvalCallArgs.leaf_iff hrest
          constructor
          · intro he
            cases he with
            | cons_ok he1 ha hr =>
              have := (EvalExp.leaf_iff hleaf _).mp he1; cases this
              rw [hattr] at ha; cases ha
              have := (ih _).mp hr; cases this; rfl
            | cons_exp_err he1 => have := (EvalExp.leaf_iff hleaf _).mp he1; cases this
            | cons_attr_err he1 ha =>
              have := (EvalExp.leaf_iff hleaf _).mp he1; cases this
              rw [hattr] at ha; cases ha
            | cons_tail_err he1 ha hr =>
              have := (EvalExp.leaf_iff hleaf _).mp he1; cases this
              rw [hattr] at ha; cases ha
              have := (ih _).mp hr; cases this
          · rintro rfl
            exact EvalCallArgs.cons_ok (EvalExp.leaf_ok hleaf) hattr ((ih _).mpr rfl)
      · cases h
    · cases h

theorem EvalCallee.direct_iff {dl cfg regs mem} (fid : FunctionId) (res) :
    EvalCallee dl cfg regs mem (.identifier (.global_id fid)) res ↔ res = .ok (fid, mem) := by
  constructor
  · intro h
    cases h with
    | direct => rfl
    | indirect_ok hne _ _ => exact absurd rfl (hne fid)
    | indirect_exp_err hne _ => exact absurd rfl (hne fid)
    | indirect_poison hne _ => exact absurd rfl (hne fid)
    | indirect_bad_addr hne _ _ => exact absurd rfl (hne fid)
    | indirect_nonptr hne _ _ => exact absurd rfl (hne fid)
  · rintro rfl; exact EvalCallee.direct

theorem EvalAssumeBundles.nil_iff {dl cfg regs mem} (res) :
    EvalAssumeBundles dl cfg regs mem [] res ↔ res = .ok mem := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact EvalAssumeBundles.nil

/-- Deterministic inversion for a direct call of a non-allocating intrinsic with leaf arguments,
no evaluated operand bundles, and a result that does not depend on the oracle. -/
theorem Step.call_intrinsic_leaf_iff {st frame callers iid rest retTy fmf fid args retAttrs bundles
      isNoRet site vs rawRet m3}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode =
      (iid, .call retTy fmf (.identifier (.global_id fid)) args retAttrs bundles isNoRet site) :: rest)
    (hargs : leafCallArgs? st.dataLayout st.config frame.registers
      (st.memory.hide (tailHidden site frame)) args = some vs)
    (hna : (st.allowLibcallsFor fid && isAllocLibcall fid.toString) = false)
    (hspec : specLoadOracleCall? st (st.memory.hide (tailHidden site frame)) fid.toString vs = none)
    (hb : (if fid.toString == "llvm.assume" then bundles else []) = [])
    (hint : ∀ o, ∃ o', evalNonAllocIntrinsicExec? st.dataLayout (frameDenormalCfg st frame)
      (st.memory.hide (tailHidden site frame)) fid.toString retTy fmf vs o (st.allowLibcallsFor fid)
      (args.map (fun a => a.2.2)) = some (.ok (rawRet, m3, o')))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔
      ev = none ∧
      c' = match applyRetFMFAndAttrsPure st.dataLayout m3 retTy fmf retAttrs rawRet with
           | .ok fr => finishCallResult st frame callers rest iid retTy fr (m3.unhide (tailHidden site frame))
           | .error err => Config.ofError err := by
  rw [Step.instr_iff hf hc]
  have hA := EvalCallArgs.leaf_iff hargs
  constructor
  · intro hi
    cases hi with
    | call_args_err ha => cases (hA _).mp ha
    | call_callee_err ha hcl => cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl
    | call_alloc_ok ha hcl hal =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl; rw [hna] at hal; cases hal
    | call_alloc_retattr_err ha hcl hal =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl; rw [hna] at hal; cases hal
    | call_alloc_err ha hcl hal =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl; rw [hna] at hal; cases hal
    | call_intrinsic_ok ha hcl _ hi hbund hret =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl
      obtain ⟨o, o1, hi⟩ := hi
      obtain ⟨o2, hi2⟩ := hint o
      rw [hi2] at hi; cases hi
      rw [hb] at hbund; cases (EvalAssumeBundles.nil_iff _).mp hbund
      rw [hret]; exact ⟨rfl, rfl⟩
    | call_intrinsic_bundle_err ha hcl _ hi hbund =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl
      obtain ⟨o, o1, hi⟩ := hi
      obtain ⟨o2, hi2⟩ := hint o
      rw [hi2] at hi; cases hi
      rw [hb] at hbund; cases (EvalAssumeBundles.nil_iff _).mp hbund
    | call_intrinsic_retattr_err ha hcl _ hi hbund hret =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl
      obtain ⟨o, o1, hi⟩ := hi
      obtain ⟨o2, hi2⟩ := hint o
      rw [hi2] at hi; cases hi
      rw [hb] at hbund; cases (EvalAssumeBundles.nil_iff _).mp hbund
      rw [hret]; exact ⟨rfl, rfl⟩
    | call_intrinsic_err ha hcl _ hi =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl
      obtain ⟨o, hi⟩ := hi
      obtain ⟨o2, hi2⟩ := hint o
      rw [hi2] at hi; cases hi
    | call_user_ok ha hcl _ hnone =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl
      obtain ⟨o2, hi2⟩ := hint default; rw [hnone] at hi2; cases hi2
    | call_user_entry_err ha hcl _ hnone =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl
      obtain ⟨o2, hi2⟩ := hint default; rw [hnone] at hi2; cases hi2
    | call_user_overflow ha hcl _ hnone =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl
      obtain ⟨o2, hi2⟩ := hint default; rw [hnone] at hi2; cases hi2
    | call_spec_oracle_ok ha hcl _ hs =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl; rw [hspec] at hs; cases hs
    | call_spec_oracle_entry_err ha hcl _ hs =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl; rw [hspec] at hs; cases hs
    | call_spec_oracle_overflow ha hcl _ hs =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl; rw [hspec] at hs; cases hs
    | call_external_err ha hcl _ hnone =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl
      obtain ⟨o2, hi2⟩ := hint default; rw [hnone] at hi2; cases hi2
  · rintro ⟨rfl, rfl⟩
    have hbund : EvalAssumeBundles st.dataLayout st.config frame.registers m3
        (if fid.toString == "llvm.assume" then bundles else []) (.ok m3) := by
      rw [hb]; exact EvalAssumeBundles.nil
    cases hret : applyRetFMFAndAttrsPure st.dataLayout m3 retTy fmf retAttrs rawRet with
    | ok fr =>
      exact StepInstr.call_intrinsic_ok ((hA _).mpr rfl) EvalCallee.direct hna
        ⟨default, hint default⟩ hbund hret
    | error err =>
      exact StepInstr.call_intrinsic_retattr_err ((hA _).mpr rfl) EvalCallee.direct hna
        ⟨default, hint default⟩ hbund hret

/-- Deterministic inversion for a direct intrinsic call (leaf arguments) that fails with `err`
for every oracle state (e.g. `llvm.assume(false)`: immediate UB). -/
theorem Step.call_intrinsic_leaf_err_iff {st frame callers iid rest retTy fmf fid args retAttrs
      bundles isNoRet site vs err}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode =
      (iid, .call retTy fmf (.identifier (.global_id fid)) args retAttrs bundles isNoRet site) :: rest)
    (hargs : leafCallArgs? st.dataLayout st.config frame.registers
      (st.memory.hide (tailHidden site frame)) args = some vs)
    (hna : (st.allowLibcallsFor fid && isAllocLibcall fid.toString) = false)
    (hspec : specLoadOracleCall? st (st.memory.hide (tailHidden site frame)) fid.toString vs = none)
    (hint : ∀ o, evalNonAllocIntrinsicExec? st.dataLayout (frameDenormalCfg st frame)
      (st.memory.hide (tailHidden site frame)) fid.toString retTy fmf vs o (st.allowLibcallsFor fid)
      (args.map (fun a => a.2.2)) = some (.error err))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔ ev = none ∧ c' = Config.ofError err := by
  rw [Step.instr_iff hf hc]
  have hA := EvalCallArgs.leaf_iff hargs
  constructor
  · intro hi
    cases hi with
    | call_args_err ha => cases (hA _).mp ha
    | call_callee_err ha hcl => cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl
    | call_alloc_ok ha hcl hal =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl; rw [hna] at hal; cases hal
    | call_alloc_retattr_err ha hcl hal =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl; rw [hna] at hal; cases hal
    | call_alloc_err ha hcl hal =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl; rw [hna] at hal; cases hal
    | call_intrinsic_ok ha hcl _ hi =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl
      obtain ⟨o, o1, hi⟩ := hi; rw [hint o] at hi; cases hi
    | call_intrinsic_bundle_err ha hcl _ hi =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl
      obtain ⟨o, o1, hi⟩ := hi; rw [hint o] at hi; cases hi
    | call_intrinsic_retattr_err ha hcl _ hi =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl
      obtain ⟨o, o1, hi⟩ := hi; rw [hint o] at hi; cases hi
    | call_intrinsic_err ha hcl _ hi =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl
      obtain ⟨o, hi⟩ := hi; rw [hint o] at hi; cases hi; exact ⟨rfl, rfl⟩
    | call_user_ok ha hcl _ hnone =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl
      have := hint default; rw [hnone] at this; cases this
    | call_user_entry_err ha hcl _ hnone =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl
      have := hint default; rw [hnone] at this; cases this
    | call_user_overflow ha hcl _ hnone =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl
      have := hint default; rw [hnone] at this; cases this
    | call_spec_oracle_ok ha hcl _ hs =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl; rw [hspec] at hs; cases hs
    | call_spec_oracle_entry_err ha hcl _ hs =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl; rw [hspec] at hs; cases hs
    | call_spec_oracle_overflow ha hcl _ hs =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl; rw [hspec] at hs; cases hs
    | call_external_err ha hcl _ hnone =>
      cases (hA _).mp ha; cases (EvalCallee.direct_iff _ _).mp hcl
      have := hint default; rw [hnone] at this; cases this
  · rintro ⟨rfl, rfl⟩
    exact StepInstr.call_intrinsic_err ((hA _).mpr rfl) EvalCallee.direct hna ⟨default, hint default⟩


/-- Deterministic inversion for `extractvalue` with a pure leaf aggregate operand. -/
theorem Step.extractvalue_leaf_iff {st frame callers iid rest aggTy aggExp idxs aggV}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = (iid, .extractvalue aggTy aggExp idxs) :: rest)
    (h1 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory aggTy aggExp = some (.ok aggV))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔
      ev = none ∧
      c' = match extractValueAux aggV idxs with
           | .ok res => finishRegInstr st frame callers rest iid res st.memory
           | .error err => Config.ofError err := by
  rw [Step.instr_iff hf hc]
  constructor
  · intro hi
    cases hi with
    | extractvalue_ok he hx =>
      cases (EvalExp.leaf_iff h1 _).mp he; rw [hx]; exact ⟨rfl, rfl⟩
    | extractvalue_e_err he => cases (EvalExp.leaf_iff h1 _).mp he
    | extractvalue_eval_err he hx =>
      cases (EvalExp.leaf_iff h1 _).mp he; rw [hx]; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    cases hx : extractValueAux aggV idxs with
    | ok res => exact StepInstr.extractvalue_ok (EvalExp.leaf_ok h1) hx
    | error err => exact StepInstr.extractvalue_eval_err (EvalExp.leaf_ok h1) hx

/-- Deterministic inversion for `fcmp` with pure leaf operands and an oracle-independent result. -/
theorem Step.fcmp_leaf_iff {st frame callers iid rest fmf pred ty e1 e2 v1 v2 res}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = (iid, .fcmp fmf pred ty e1 e2) :: rest)
    (h1 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty e1 = some (.ok v1))
    (h2 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty e2 = some (.ok v2))
    (hcmp : ∀ o, ∃ o', evalFCmpExec (frameDenormalCfg st frame) fmf pred v1 v2 o = .ok (res, o'))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔
      ev = none ∧ c' = finishRegInstr st frame callers rest iid res st.memory := by
  rw [Step.instr_iff hf hc]
  constructor
  · intro hi
    cases hi with
    | fcmp_ok he1 he2 hx =>
      cases (EvalExp.leaf_iff h1 _).mp he1; cases (EvalExp.leaf_iff h2 _).mp he2
      obtain ⟨o, o1, hx⟩ := hx; obtain ⟨o2, hx2⟩ := hcmp o
      rw [hx2] at hx; cases hx; exact ⟨rfl, rfl⟩
    | fcmp_e1_err he1 => cases (EvalExp.leaf_iff h1 _).mp he1
    | fcmp_e2_err he1 he2 =>
      cases (EvalExp.leaf_iff h1 _).mp he1; cases (EvalExp.leaf_iff h2 _).mp he2
    | fcmp_eval_err he1 he2 hx =>
      cases (EvalExp.leaf_iff h1 _).mp he1; cases (EvalExp.leaf_iff h2 _).mp he2
      obtain ⟨o, hx⟩ := hx; obtain ⟨o2, hx2⟩ := hcmp o
      rw [hx2] at hx; cases hx
  · rintro ⟨rfl, rfl⟩
    exact StepInstr.fcmp_ok (EvalExp.leaf_ok h1) (EvalExp.leaf_ok h2) ⟨default, hcmp default⟩

end LeanNanoLlvm.Refinement
