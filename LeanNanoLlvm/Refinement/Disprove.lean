import Lean
import LeanNanoLlvm.Refinement.Refinement
import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.Semantics.Module

/-!
# Kernel-Pure Refinement Disproof Tactic (`llvm_disprove`)

Proves negations of LLVM IR refinement (`¬ (src ⊒ tgt)`) with **100% kernel purity**
(ONLY `{propext, Classical.choice, Quot.sound}`).

Supports two modes:
- `llvm_disprove [arg1, arg2, ...]` — certify a specific concrete counterexample `List RegisterValue`.
- `llvm_disprove` / `llvm_disprove (timeout := 5000)` — run a fast, timeout-bounded
  meta-level heuristic witness search (no bitwidth cap; works for `i1`..`i128`+) prioritizing
  `poison`, AST-extracted constants (`c`, `c ± 1`, `-c`, `~c`), bitwidth boundaries
  (`0, 1, -1, INT_MIN, INT_MAX, w, w-1`), powers of two, and PRNG bit patterns, then
  synthesize a kernel-pure refutation proof from the discovered witness.
-/

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

/-! ## Section 2: Meta-Level Heuristic Witness Search (Timeout-Bounded) -/

private def collectExpInts : AST.Exp → List Int
  | .int n => [n]
  | _ => []

private def collectInstrInts : AST.Instruction → List Int
  | .intBinaryOp _ _ e1 e2 => collectExpInts e1 ++ collectExpInts e2
  | .icmp _ _ _ e1 e2 => collectExpInts e1 ++ collectExpInts e2
  | .select _ _ c _ t f => collectExpInts c ++ collectExpInts t ++ collectExpInts f
  | .conversionOp _ _ e _ => collectExpInts e
  | .freeze (_, e) => collectExpInts e
  | .phi _ _ entries => entries.foldl (fun acc (e, _) => acc ++ collectExpInts e) []
  | _ => []

private def collectTermInts : AST.Terminator → List Int
  | .ret (_, e) => collectExpInts e
  | .condBr c _ _ => collectExpInts c
  | .switch _ v _ cases =>
    collectExpInts v ++ cases.foldl (fun acc (n, _) => n :: acc) []
  | _ => []

private def collectDefInts (d : AST.Definition) : List Int :=
  d.blocks.foldl (fun acc blk =>
    let acc1 := blk.code.foldl (fun a (_, ins) => a ++ collectInstrInts ins) acc
    acc1 ++ collectTermInts blk.terminator.2) []

private def pushUniqueBv (w : Nat) (seen : Array Nat) (out : Array RegisterValue) (n : Nat) :
    Array Nat × Array RegisterValue :=
  let m := n % (2 ^ w)
  if seen.contains m then (seen, out)
  else (seen.push m, out.push (.bv w (.value (BitVec.ofNat w m))))

/-- Build priority-ordered heuristic candidate values for an integer parameter of width `w`.
    Works for arbitrary bitwidths (`i1`, `i8`, `i32`, `i64`, `i128`, ...) with no width cap. -/
private def buildCandidatesForWidth (w : Nat) (astConsts : List Int) (prngCount : Nat := 16) :
    Array RegisterValue := Id.run do
  let mut seen : Array Nat := #[]
  let mut out : Array RegisterValue := #[.bv w .poison]
  if w == 0 then
    return out.push (.bv 0 (.value 0#0))
  let modulus := 2 ^ w
  let half := 2 ^ (w - 1)
  let addInt (s : Array Nat) (o : Array RegisterValue) (k : Int) :=
    pushUniqueBv w s o (BitVec.ofInt w k).toNat
  -- Priority 1: 0, 1, -1
  for k in ([0, 1, -1] : List Int) do
    (seen, out) := addInt seen out k
  -- Priority 2: AST-extracted constants and their neighbors (c, c-1, c+1, -c, ~c)
  for c in astConsts do
    for k in [c, c - 1, c + 1, -c, -(c + 1)] do
      (seen, out) := addInt seen out k
  -- Priority 3: bitwidth boundaries & shift-amount boundaries
  for k in ([2, -2, 3, 4, (w : Int), (w : Int) - 1] : List Int) do
    (seen, out) := addInt seen out k
  for n in [half, half - 1, half + 1, modulus - 2] do
    (seen, out) := pushUniqueBv w seen out n
  -- Priority 4: powers of two and low-bit masks
  let maxPow := min w 64
  for k in [:maxPow] do
    let p := 2 ^ k
    (seen, out) := pushUniqueBv w seen out p
    (seen, out) := pushUniqueBv w seen out (p - 1)
  -- Priority 5: deterministic PRNG bit-patterns (scaled to width `w`)
  let mut state : UInt64 := 0x9e3779b97f4a7c15 + w.toUInt64
  for _ in [:prngCount] do
    state := state * 6364136223846793005 + 1442695040888963407
    let mut val : Nat := state.toNat
    if w > 64 then
      let chunks := (w + 63) / 64
      for _ in [1:chunks] do
        state := state * 6364136223846793005 + 1442695040888963407
        val := (val <<< 64) ||| state.toNat
    (seen, out) := pushUniqueBv w seen out val
  return out

private def isCounterexampleConfig (cSrc cTgt : Config) : Bool :=
  match cSrc, cTgt with
  | .halted (.bv w1 (.value a)) _, .halted (.bv w2 (.value b)) _ =>
    if h : w1 = w2 then a != (h ▸ b) else true
  | .halted (.bv _ (.value _)) _, .halted (.bv _ .poison) _ => true
  | .halted (.float ft1 (.value a)) _, .halted (.float ft2 (.value b)) _ =>
    if h : ft1 = ft2 then a != (h ▸ b) else true
  | .halted (.float _ (.value _)) _, .halted (.float _ .poison) _ => true
  | .halted _ _, .ub _ => true
  | _, _ => false

private def testWitness (src tgt : AST.Definition) (args : List RegisterValue) : Bool :=
  let (_, cSrc, _) := runDefinitionWithTrace src args
  match cSrc with
  | .halted _ _ =>
    let (_, cTgt, _) := runDefinitionWithTrace tgt args
    isCounterexampleConfig cSrc cTgt
  | _ => false

/-- Enumerate index tuples into `pools` whose index sum equals `targetSum`, bounded by fuel
    and wall-clock `deadlineMs`. Total (no `partial`). -/
private def searchByPrioritySum (src tgt : AST.Definition) (pools : List (Array RegisterValue))
    (deadlineMs : Nat) (maxSum : Nat) : IO (Option (List RegisterValue)) := do
  -- Recursive helper over remaining pools (structurally recursive on `pools`)
  let rec go (rem : List (Array RegisterValue)) (budget : Nat) (acc : List RegisterValue) :
      IO (Option (List RegisterValue)) := do
    match rem with
    | [] =>
      if budget != 0 then return none
      let now ← IO.monoMsNow
      if now >= deadlineMs then return none
      let args := acc.reverse
      if testWitness src tgt args then return some args else return none
    | pool :: rest =>
      let limit := min (budget + 1) pool.size
      for i in [:limit] do
        let now ← IO.monoMsNow
        if now >= deadlineMs then return none
        match ← go rest (budget - i) (pool[i]! :: acc) with
        | some w => return some w
        | none => pure ()
      return none
  for s in [:maxSum + 1] do
    let now ← IO.monoMsNow
    if now >= deadlineMs then return none
    match ← go pools s [] with
    | some w => return some w
    | none => pure ()
  return none

/-- Timeout-bounded heuristic counterexample search for `src ⊒ tgt`. -/
private def findCounterexample (src tgt : AST.Definition) (timeoutMs : Nat) :
    IO (Option (List RegisterValue)) := do
  let paramTypes :=
    match src.prototype.type with
    | .function _ pts => pts
    | _ => []
  let astConsts := collectDefInts src ++ collectDefInts tgt
  let mut pools : List (Array RegisterValue) := []
  for ty in paramTypes do
    match ty with
    | .int w => pools := pools ++ [buildCandidatesForWidth w astConsts]
    | _ => return none
  let startMs ← IO.monoMsNow
  let deadlineMs := startMs + timeoutMs
  let maxSum := pools.foldl (fun acc p => acc + p.size) 0
  match ← searchByPrioritySum src tgt pools deadlineMs maxSum with
  | some w => return some w
  | none =>
    -- Fallback: deterministic PRNG sampling over the full pools until timeout
    let mut state : UInt64 := 0x243f6a8885a308d3
    for _ in [:20000] do
      let now ← IO.monoMsNow
      if now >= deadlineMs then return none
      let mut args : List RegisterValue := []
      for pool in pools do
        state := state * 6364136223846793005 + 1442695040888963407
        let idx := (state.toNat) % pool.size
        args := args ++ [pool[idx]!]
      if testWitness src tgt args then
        return some args
    return none

open Lean Elab Tactic Meta

unsafe def evalDefImpl (e : Expr) : MetaM AST.Definition :=
  Lean.Meta.evalExpr AST.Definition (mkConst ``AST.Definition) e

@[implemented_by evalDefImpl]
private def evalDef (_ : Expr) : MetaM AST.Definition :=
  throwError "evalDef requires compiled VM"

/-! ## Section 3: Kernel-Pure Concrete Stepper for Refutation Goals -/

private def quoteRegisterValue : RegisterValue → Expr
  | .bv w .poison =>
    mkApp2 (mkConst ``RegisterValue.bv) (mkNatLit w)
      (mkApp (mkConst ``PoisonOr.poison) (mkApp (mkConst ``BitVec) (mkNatLit w)))
  | .bv w (.value bv) =>
    let bvExpr := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit w) (mkNatLit bv.toNat)
    mkApp2 (mkConst ``RegisterValue.bv) (mkNatLit w)
      (mkApp2 (mkConst ``PoisonOr.value) (mkApp (mkConst ``BitVec) (mkNatLit w)) bvExpr)
  | _ => mkConst ``RegisterValue.void

private def quoteRegisterValueList (vs : List RegisterValue) : Expr :=
  let ty := mkConst ``RegisterValue
  vs.foldr (fun v acc => mkApp3 (mkConst ``List.cons [levelZero]) ty (quoteRegisterValue v) acc)
    (mkApp (mkConst ``List.nil [levelZero]) ty)

/-- Inspect the two `Config` arguments of `⊢ ¬ Config.IsRefinedBy callerIds cX cY`. -/
private def getNotRefinedConfigs : TacticM (Option (Expr × Expr)) := do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  if tgt.isAppOfArity ``Not 1 then
    let inner := tgt.appArg!
    if inner.isAppOfArity ``Config.IsRefinedBy 3 then
      return some (inner.getArg! 1, inner.getArg! 2)
  return none

private inductive ConcreteAction
  | halted
  | ub
  | instr (name : Name)
  | term (name : Name)
  | unknown

private def inspectConcreteConfig (c : Expr) : TacticM ConcreteAction := do
  let c ← whnf c
  if c.isAppOf ``Config.halted then return .halted
  if c.isAppOf ``Config.ub then return .ub
  if !c.isAppOf ``Config.running then return .unknown
  let st ← whnf c.appArg!
  if !st.isAppOf ``MachineState.mk then return .unknown
  let frames ← whnf (st.getArg! 0)
  if !frames.isAppOf ``List.cons then return .unknown
  let frame ← whnf (frames.getArg! 1)
  if !frame.isAppOf ``CallFrame.mk then return .unknown
  let rem ← whnf (frame.getArg! 2)
  if rem.isAppOf ``List.cons then
    let pair ← whnf (rem.getArg! 1)
    if pair.isAppOf ``Prod.mk then
      let ins ← whnf (pair.getArg! 3)
      if let some nm := ins.getAppFn.constName? then
        return .instr nm
  else if rem.isAppOf ``List.nil then
    let termPair ← whnf (frame.getArg! 3)
    if termPair.isAppOf ``Prod.mk then
      let term ← whnf (termPair.getArg! 3)
      if let some nm := term.getAppFn.constName? then
        return .term nm
  return .unknown

private def simpConcreteStep : TacticM Unit := do
  try
    evalTactic (← `(tactic|
      simp only [simp_step,
        bitvec_ofInt_ofNat, bitvec_ofInt_neg, bitvec_ofInt_negSucc,
        BitVec.ofNat_eq_ofNat,
        AST.LlvmType.scalarType, AST.FastMathFlags.any,
        Bool.or_self, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte,
        beq_self_eq_true, Config.ofError]))
  catch _ => pure ()

private def solveConcretePhis : Nat → TacticM Unit
  | 0 => pure ()
  | fuel + 1 => do
    let s ← saveState
    try
      evalTactic (← `(tactic| exact fun _ => EvalPhis.nil_iff))
    catch _ =>
      restoreState s
      evalTactic (← `(tactic| intro res_phi; apply EvalPhis.cons_leaf_iff))
      evalTactic (← `(tactic| (simp [List.find?, -Prod.mk.injEq, -Option.some.injEq]; rfl)))
      evalTactic (← `(tactic| ((try llvm_step); rfl)))
      solveConcretePhis fuel

/-- Step the source (`cX`) deterministically in `⊢ ¬ Config.IsRefinedBy ids cX cY`. -/
private def stepConcreteLeft (act : ConcreteAction) : TacticM Bool := do
  match act with
  | .instr nm =>
    if nm == ``AST.Instruction.intBinaryOp then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.not_of_det_step_left
            (Step.intBinaryOp_leaf_iff rfl rfl (by llvm_step; rfl) (by llvm_step; rfl)) ?_))
        simpConcreteStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.icmp then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.not_of_det_step_left
            (Step.icmp_leaf_iff rfl rfl (by llvm_step; rfl) (by llvm_step; rfl)) ?_))
        simpConcreteStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.select then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.not_of_det_step_left
            (Step.select_leaf_iff rfl rfl (by llvm_step; rfl) (by llvm_step; rfl) (by llvm_step; rfl)) ?_))
        simpConcreteStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.conversionOp then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.not_of_det_step_left
            (Step.conversionOp_leaf_iff rfl rfl (by llvm_step; rfl) (fun _ => rfl)) ?_))
        simpConcreteStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.freeze then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.not_of_det_step_left
            (Step.freeze_bv_val_iff rfl rfl (by llvm_step; rfl)) ?_))
        simpConcreteStep; return true
      catch _ => restoreState s; return false
    else return false
  | .term nm =>
    if nm == ``AST.Terminator.ret then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.not_of_det_step_left
            (Step.ret_top_leaf_iff rfl rfl rfl rfl (by llvm_step; rfl)) ?_))
        simpConcreteStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.br then
      let s ← saveState
      try
        evalTactic (← `(tactic| apply Config.IsRefinedBy.not_of_det_step_left))
        evalTactic (← `(tactic| apply Step.br_det_iff rfl rfl rfl))
        evalTactic (← `(tactic| (simp [AST.Definition.findBlock?]; rfl)))
        evalTactic (← `(tactic| (simp only [splitPhis]; rfl)))
        solveConcretePhis 16
        simpConcreteStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.condBr then
      let s ← saveState
      try
        evalTactic (← `(tactic| apply Config.IsRefinedBy.not_of_det_step_left))
        evalTactic (← `(tactic| apply Step.condBr_val_det_iff rfl rfl rfl))
        evalTactic (← `(tactic| ((try llvm_step); rfl)))
        evalTactic (← `(tactic| (simp [AST.Definition.findBlock?]; rfl)))
        evalTactic (← `(tactic| (simp only [splitPhis]; rfl)))
        solveConcretePhis 16
        simpConcreteStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.switch then
      let s ← saveState
      try
        evalTactic (← `(tactic| apply Config.IsRefinedBy.not_of_det_step_left))
        evalTactic (← `(tactic| apply Step.switch_val_det_iff rfl rfl rfl))
        evalTactic (← `(tactic| ((try llvm_step); rfl)))
        evalTactic (← `(tactic| (simp [AST.Definition.findBlock?, List.find?, bitvec_ofInt_ofNat, bitvec_ofInt_negSucc]; rfl)))
        evalTactic (← `(tactic| (simp only [splitPhis]; rfl)))
        solveConcretePhis 16
        simpConcreteStep; return true
      catch _ => restoreState s; return false
    else return false
  | _ => return false

/-- Step the target (`cY`) in `⊢ ¬ Config.IsRefinedBy ids cX cY` (or close if `cY` aborts while
    `cX` is halted). -/
private def stepConcreteRight (actL actR : ConcreteAction) : TacticM Bool := do
  match actR with
  | .instr nm =>
    if nm == ``AST.Instruction.intBinaryOp then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.not_of_step_right
            ((Step.intBinaryOp_leaf_iff rfl rfl (by (try llvm_step); rfl) (by (try llvm_step); rfl) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpConcreteStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.icmp then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.not_of_step_right
            ((Step.icmp_leaf_iff rfl rfl (by (try llvm_step); rfl) (by (try llvm_step); rfl) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpConcreteStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.select then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.not_of_step_right
            ((Step.select_leaf_iff rfl rfl (by (try llvm_step); rfl) (by (try llvm_step); rfl) (by (try llvm_step); rfl) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpConcreteStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.conversionOp then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.not_of_step_right
            ((Step.conversionOp_leaf_iff rfl rfl (by (try llvm_step); rfl) (fun _ => rfl) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpConcreteStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.freeze then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.not_of_step_right
            ((Step.freeze_bv_val_iff rfl rfl (by (try llvm_step); rfl) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpConcreteStep; return true
      catch _ => restoreState s; return false
    else return false
  | .term nm =>
    if nm == ``AST.Terminator.ret then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.not_of_step_right
            ((Step.ret_top_leaf_iff rfl rfl rfl rfl (by (try llvm_step); rfl) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpConcreteStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.br then
      let s ← saveState
      try
        evalTactic (← `(tactic| apply Config.IsRefinedBy.not_of_step_right))
        evalTactic (← `(tactic| apply Step.br_det rfl rfl rfl))
        evalTactic (← `(tactic| (simp [AST.Definition.findBlock?]; rfl)))
        evalTactic (← `(tactic| (simp only [splitPhis]; rfl)))
        solveConcretePhis 16
        simpConcreteStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.condBr then
      if match actL with | .halted => true | _ => false then
        let sUb ← saveState
        try
          evalTactic (← `(tactic|
            apply Config.IsRefinedBy.not_of_halted_left_canAbort_right;
            apply Step.condBr_poison_canAbort rfl rfl rfl;
            (try llvm_step); (try rfl); done))
          return true
        catch _ => restoreState sUb
      let s ← saveState
      try
        evalTactic (← `(tactic| apply Config.IsRefinedBy.not_of_step_right))
        evalTactic (← `(tactic| apply Step.condBr_val_det rfl rfl rfl))
        evalTactic (← `(tactic| ((try llvm_step); rfl)))
        evalTactic (← `(tactic| (simp [AST.Definition.findBlock?]; rfl)))
        evalTactic (← `(tactic| (simp only [splitPhis]; rfl)))
        solveConcretePhis 16
        simpConcreteStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.switch then
      if match actL with | .halted => true | _ => false then
        let sUb ← saveState
        try
          evalTactic (← `(tactic|
            apply Config.IsRefinedBy.not_of_halted_left_canAbort_right;
            apply Step.switch_poison_canAbort rfl rfl rfl;
            (try llvm_step); (try rfl); done))
          return true
        catch _ => restoreState sUb
      let s ← saveState
      try
        evalTactic (← `(tactic| apply Config.IsRefinedBy.not_of_step_right))
        evalTactic (← `(tactic| apply Step.switch_val_det rfl rfl rfl))
        evalTactic (← `(tactic| ((try llvm_step); rfl)))
        evalTactic (← `(tactic| (simp [AST.Definition.findBlock?, List.find?, bitvec_ofInt_ofNat, bitvec_ofInt_negSucc]; rfl)))
        evalTactic (← `(tactic| (simp only [splitPhis]; rfl)))
        solveConcretePhis 16
        simpConcreteStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.unreachable then
      if match actL with | .halted => true | _ => false then
        let sUb ← saveState
        try
          evalTactic (← `(tactic|
            exact Config.IsRefinedBy.not_of_halted_left_canAbort_right
              (Or.inl ⟨[], "unreachable", StarStep.single ((Step.unreachable_iff rfl rfl rfl).mpr ⟨rfl, rfl⟩)⟩)))
          return true
        catch _ => restoreState sUb
      return false
    else return false
  | _ => return false

/-- Step both concrete configurations until halted/UB, then close the contradiction. -/
private def runConcreteRefutation (fuel : Nat) : TacticM Unit := do
  match fuel with
  | 0 => pure ()
  | n + 1 =>
    if (← getGoals).isEmpty then return ()
    let some (cX, cY) ← getNotRefinedConfigs | return ()
    let actL ← inspectConcreteConfig cX
    let actR ← inspectConcreteConfig cY
    match actL, actR with
    | .halted, .ub =>
      evalTactic (← `(tactic| exact Config.IsRefinedBy.not_of_halted_ub))
      return ()
    | .halted, .halted =>
      evalTactic (← `(tactic|
        first
        | (apply Config.IsRefinedBy.not_of_halted_bv;
           simp [simp_llvm, PoisonOr.IsRefinedBy, BitVec.msb,
             BitVec.saddOverflow, BitVec.uaddOverflow,
             BitVec.ssubOverflow, BitVec.usubOverflow,
             BitVec.smulOverflow, BitVec.umulOverflow];
           try decide)
        | (apply Config.IsRefinedBy.not_of_halted_float;
           simp [simp_llvm, PoisonOr.IsRefinedBy];
           try decide)))
      return ()
    | _, _ =>
      let steppedL ← stepConcreteLeft actL
      if steppedL then
        runConcreteRefutation n
      else
        let steppedR ← stepConcreteRight actL actR
        if steppedR then
          runConcreteRefutation n
        else
          return ()

/-- Extract `(srcExpr, tgtExpr)` from `⊢ ¬ (src ⊒ tgt)`. -/
private def extractNotDefRefines : TacticM (Expr × Expr) := do
  let tgt ← instantiateMVars (← (← getMainGoal).getType)
  if tgt.isAppOfArity ``Not 1 then
    let inner ← whnfR tgt.appArg!
    if inner.isAppOfArity ``HRefinement.IsRefinedBy 5 then
      return (inner.getArg! 3, inner.getArg! 4)
    if inner.isAppOfArity ``Definition.IsRefinedBy 2 then
      return (inner.getArg! 0, inner.getArg! 1)
  throwError "llvm_disprove: expected goal of the form `¬ (src ⊒ tgt)`, got:{indentExpr tgt}"

/-- Prove `⊢ ¬ (src ⊒ tgt)` given an explicit `Expr` of type `List RegisterValue`. -/
private def proveDisproofWithExpr (argsExpr : Expr) : TacticM Unit := do
  -- Unfold named `Definition` constants (if any) so `ArgValuesWellFormed` and `initCallConfig` reduce.
  let (srcExpr, tgtExpr) ← extractNotDefRefines
  for e in #[srcExpr, tgtExpr] do
    if let some nm := e.getAppFn.constName? then
      if nm != ``AST.Definition.mk then
        let id := mkIdent nm
        try evalTactic (← `(tactic| dsimp only [$id:ident])) catch _ => pure ()
  let witnessTerm ← Lean.PrettyPrinter.delab argsExpr
  evalTactic (← `(tactic|
    refine Definition.IsRefinedBy.not_of_witness $witnessTerm ?_ ?_))
  -- Goal 1: ArgValuesWellFormed
  focus (evalTactic (← `(tactic|
    (simp [Semantics.Definition.ArgValuesWellFormed,
           Semantics.RegisterValue.WellFormedForList,
           Semantics.RegisterValue.WellFormedFor]; done))))
  -- Goal 2: ¬ Config.IsRefinedBy ...
  evalTactic (← `(tactic|
    simp only [initCallConfig, mkEntryFrameWithMem, mkEntryFrame, bindFrameArgs, bindFrameArgs.go,
      applyByValCopies, applyByValCopies.go, splitPhis,
      RegisterValue.matchesType, byvalDeferredAttrs, applyValueAttrsPure,
      List.length_nil, List.length_cons, List.any_nil, List.any_cons,
      List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.getD_some, Option.getD_none,
      Bool.or_self, Bool.or_false, Bool.false_or, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte, ite_self, List.isEmpty_nil,
      Bool.not_true, Bool.not_false, beq_self_eq_true]))
  runConcreteRefutation 256
  if !(← getGoals).isEmpty then
    throwError "llvm_disprove: could not close refutation goal with witness {argsExpr}"

/-- Format a single `RegisterValue` in human-readable form for `llvm_disprove?`. -/
private def formatRegisterValue : RegisterValue → String
  | .bv w .poison => s!"i{w} poison"
  | .bv w (.value bv) => s!"{bv.toNat}#{w}"
  | .float fty .poison => s!"{fty.print} poison"
  | .float fty (.value bits) => s!"{fty.print} bits({bits})"
  | _ => "<value>"

/-- Format the counterexample argument bindings (e.g. `%x = 2147483647#32, %y = poison`). -/
private def formatCounterexample (args : List AST.RawId) (witness : List RegisterValue) : String :=
  let pairs := (args.zip witness).map fun (id, v) =>
    let name := match id with
      | .name s => s!"%{s}"
      | .anonymous n => s!"%{n}"
    s!"{name} = {formatRegisterValue v}"
  String.intercalate ", " pairs

/-- Disprove an unsound LLVM IR refinement `¬ (src ⊒ tgt)` using an explicit witness list. -/
elab "llvm_disprove " "[" args:term,* "]" : tactic => do
  let listTerm ← `([$args,*])
  let argsExpr ← elabTerm listTerm (some (mkApp (mkConst ``List [levelZero]) (mkConst ``RegisterValue)))
  proveDisproofWithExpr argsExpr

/-- Disprove an unsound LLVM IR refinement `¬ (src ⊒ tgt)` via timeout-bounded heuristic
    counterexample search (default `timeout := 2000` ms) + kernel-pure certification. -/
syntax "llvm_disprove" ("(" "timeout" ":=" num ")")? : tactic

/-- Like `llvm_disprove`, but also displays the found counterexample and emits a clickable
    `Try this: llvm_disprove [...]` suggestion (like `simp?`). -/
syntax "llvm_disprove?" ("(" "timeout" ":=" num ")")? : tactic

private def runDisproveSearch (stx : Syntax) (timeoutMs : Nat) (suggest : Bool) : TacticM Unit := do
  let (srcExpr, tgtExpr) ← extractNotDefRefines
  let srcDef ← evalDef srcExpr
  let tgtDef ← evalDef tgtExpr
  match ← findCounterexample srcDef tgtDef timeoutMs with
  | none =>
    throwError "llvm_disprove: no counterexample found within {timeoutMs}ms"
  | some witness =>
    let argsExpr := quoteRegisterValueList witness
    proveDisproofWithExpr argsExpr
    if suggest then
      let elemTerms ← witness.toArray.mapM fun v =>
        Lean.PrettyPrinter.delab (quoteRegisterValue v)
      let suggStx ← `(tactic| llvm_disprove [$elemTerms,*])
      let header := s!"Counterexample: {formatCounterexample srcDef.args witness}\nTry this:"
      Lean.Meta.Tactic.TryThis.addSuggestion stx
        { suggestion := .tsyntax suggStx }
        (origSpan? := some stx)
        (header := header)

elab_rules : tactic
  | `(tactic| llvm_disprove $[(timeout := $t)]?) => do
    let timeoutMs := match t with | some n => n.getNat | none => 2000
    runDisproveSearch (← getRef) timeoutMs false
  | `(tactic| llvm_disprove? $[(timeout := $t)]?) => do
    let timeoutMs := match t with | some n => n.getNat | none => 2000
    runDisproveSearch (← getRef) timeoutMs true

end LeanNanoLlvm.Refinement
