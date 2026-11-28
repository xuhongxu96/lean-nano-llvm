import Lean
import LeanNanoLlvm.Refinement.Disprove.Lemmas

/-! # Kernel-Pure Concrete Stepper for `llvm_disprove`

Given a concrete witness, steps both programs symbolically and closes the refutation goal
with the lemmas from `LeanNanoLlvm.Refinement.Disprove.Lemmas`. -/

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm AST Semantics
open Lean Elab Tactic Meta

/-! ## Section 3: Kernel-Pure Concrete Stepper for Refutation Goals -/

def quoteRegisterValue : RegisterValue → Expr
  | .bv w .poison =>
    mkApp2 (mkConst ``RegisterValue.bv) (mkNatLit w)
      (mkApp (mkConst ``PoisonOr.poison) (mkApp (mkConst ``BitVec) (mkNatLit w)))
  | .bv w (.value bv) =>
    let bvExpr := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit w) (mkNatLit bv.toNat)
    mkApp2 (mkConst ``RegisterValue.bv) (mkNatLit w)
      (mkApp2 (mkConst ``PoisonOr.value) (mkApp (mkConst ``BitVec) (mkNatLit w)) bvExpr)
  | .float ft v =>
    let ftE := mkConst (match ft with
      | .half => ``AST.FloatType.half | .bfloat => ``AST.FloatType.bfloat
      | .float => ``AST.FloatType.float | .double => ``AST.FloatType.double
      | .x86_fp80 => ``AST.FloatType.x86_fp80 | .fp128 => ``AST.FloatType.fp128
      | .ppc_fp128 => ``AST.FloatType.ppc_fp128)
    let fmtE := mkApp (mkConst ``AST.FloatType.format) ftE
    let tyE := mkApp (mkConst ``IEEEFloat) fmtE
    let valE := match v with
      | .poison => mkApp (mkConst ``PoisonOr.poison) tyE
      | .value x =>
        mkApp2 (mkConst ``PoisonOr.value) tyE (mkApp2 (mkConst ``IEEEFloat.ofNatBits) fmtE (mkNatLit x.bits.toNat))
    mkApp2 (mkConst ``RegisterValue.float) ftE valE
  | _ => mkConst ``RegisterValue.void

def quoteRegisterValueList (vs : List RegisterValue) : Expr :=
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

/-- When set, the stepper also evaluates the concrete operations bound in registers
(`simp_llvm`, BitVec literals), so that values computed in one block can decide branches later
(loops). Used by the second pass of `proveDisproofWithExpr`. -/
initialize strongConcreteSimp : IO.Ref Bool ← IO.mkRef false

private def simpConcreteStep : TacticM Unit := do
  if ← strongConcreteSimp.get then
    try
      evalTactic (← `(tactic|
        simp (config := { decide := true }) only [simp_step, simp_llvm,
          bitvec_ofInt_ofNat, bitvec_ofInt_neg, bitvec_ofInt_negSucc,
          BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceMul,
          BitVec.reduceULT, BitVec.reduceSLT, BitVec.reduceULE, BitVec.reduceSLE,
          AST.LlvmType.scalarType, AST.FastMathFlags.any,
          Bool.or_self, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte,
          beq_self_eq_true, Config.ofError]))
    catch _ => pure ()
    return
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
    else if nm == ``AST.Instruction.extractvalue then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.not_of_det_step_left
            (Step.extractvalue_leaf_iff rfl rfl (by llvm_step; rfl)) ?_))
        simpConcreteStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.fcmp then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.not_of_det_step_left
            (Step.fcmp_leaf_iff rfl rfl (by llvm_step; rfl) (by llvm_step; rfl) (fun _ => ⟨_, rfl⟩)) ?_))
        simpConcreteStep; return true
      catch e =>
        restoreState s
        if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then logInfo m!"DTFCMP {e.toMessageData}"
        return false
    else if nm == ``AST.Instruction.call then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          first
          | refine Config.IsRefinedBy.not_of_det_step_left
              (Step.call_intrinsic_leaf_iff rfl rfl
                (by first | rfl | (simp [leafCallArgs?, simp_step]; rfl))
                rfl rfl rfl (fun _ => ⟨_, rfl⟩)) ?_
          | refine Config.IsRefinedBy.not_of_det_step_left
              (Step.call_intrinsic_leaf_err_iff rfl rfl
                (by first | rfl | (simp [leafCallArgs?, simp_step]; rfl))
                rfl rfl (fun _ => rfl)) ?_))
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
    else if nm == ``AST.Terminator.retVoid then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.not_of_det_step_left (Step.retVoid_top_iff rfl rfl rfl rfl) ?_))
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
    else if nm == ``AST.Terminator.retVoid then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.not_of_step_right
            ((Step.retVoid_top_iff rfl rfl rfl rfl none _).mpr ⟨rfl, rfl⟩) ?_))
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
def extractNotDefRefines : TacticM (Expr × Expr) := do
  let tgt ← instantiateMVars (← (← getMainGoal).getType)
  if tgt.isAppOfArity ``Not 1 then
    let inner ← whnfR tgt.appArg!
    if inner.isAppOfArity ``HRefinement.IsRefinedBy 5 then
      return (inner.getArg! 3, inner.getArg! 4)
    if inner.isAppOfArity ``Definition.IsRefinedBy 2 then
      return (inner.getArg! 0, inner.getArg! 1)
  throwError "llvm_disprove: expected goal of the form `¬ (src ⊒ tgt)`, got:{indentExpr tgt}"

/-- Run `c` with the executable interpreter (default oracle) to a final configuration, at most
`fuel` steps; also return the steps taken. Tail-recursive (see `Disprove.Search.runToFinal`). -/
private def runCounting (fuel used : Nat) (o : OracleState) (c : Semantics.Config) :
    Semantics.Config × Nat :=
  match fuel with
  | 0 => (c, used)
  | n + 1 =>
    match c with
    | .running _ =>
      let (_, c1, o1) := execStep o c
      runCounting n (used + 1) o1 c1
    | _ => (c, used)

/-- The events a run emits (whether the trace is empty decides whether its termination counts). -/
private def runEvents (fuel : Nat) (c : Semantics.Config) : List TraceEvent :=
  (runSteps fuel default c).1

private unsafe def evalArgsImpl (e : Expr) : MetaM (List RegisterValue) :=
  Lean.Meta.evalExpr (List RegisterValue) (mkApp (mkConst ``List [levelZero]) (mkConst ``RegisterValue)) e

@[implemented_by evalArgsImpl]
private def evalArgs (_ : Expr) : MetaM (List RegisterValue) :=
  throwError "evalArgs requires compiled VM"

private unsafe def evalDefnImpl (e : Expr) : MetaM AST.Definition :=
  Lean.Meta.evalExpr AST.Definition (mkConst ``AST.Definition) e

@[implemented_by evalDefnImpl]
private def evalDefn (_ : Expr) : MetaM AST.Definition :=
  throwError "evalDefn requires compiled VM"

/-- Replace the target configuration of `⊢ ¬ Config.IsRefinedBy ids cX (initCallConfig … tgt args)`
by the outcome of running it with the executable interpreter, certified in the kernel
(`runSteps_sound`): `.ub ""` if the run aborts, `.halted vY m` (for every `m`) if it returns `vY`
without emitting events. This handles any instruction on the target side. Returns `false` (goal
unchanged) if the run neither aborts nor halts silently with a quotable value. -/
private def replaceTargetByExecution (tgtExpr argsExpr : Expr) : TacticM Bool := do
  let tgt ← evalDefn tgtExpr
  let args ← evalArgs argsExpr
  let cfg : SemanticsConfig := .modern
  let c0 := initCallConfig cfg .default64LE {} ∅ ∅ tgt args
  let (cf, used) := runCounting cfg.maxSteps 0 default c0
  let fuel := Syntax.mkNumLit (toString (used + 1))
  let s ← saveState
  try
    if cf.isAbortB then
      evalTactic (← `(tactic|
        refine Config.IsRefinedBy.not_of_canAbort_right
          (CanAbort.of_runSteps $fuel default (initCallConfig_empty_wf _ _ _ _ _ _)
            (by decide +kernel)) ?_))
      return true
    match cf with
    | .halted v _ =>
      if !(runEvents (used + 1) c0).isEmpty then return false
      let ok := match v with
        | .bv _ _ | .void | .float _ _ => true
        | _ => false
      if !ok then
        if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then
          logInfo m!"DTSTUCK target-returns-unquotable {v.inferType?.map (·.print)}"
        return false
      let vStx ← Lean.Elab.Term.exprToSyntax (quoteRegisterValue v)
      evalTactic (← `(tactic|
        refine Config.IsRefinedBy.not_of_terminates_right (vY := $vStx)
          (Terminates.of_runSteps $fuel default (initCallConfig_empty_wf _ _ _ _ _ _)
            (by decide +kernel) (by decide +kernel)) ?_))
      evalTactic (← `(tactic| intro _))
      return true
    | _ =>
      if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then
        let k := match cf with
          | .running _ => "running" | .staticError m => s!"staticError {m}" | _ => "other"
        logInfo m!"DTSTUCK target-run-ends {k} after {used} steps"
      return false
  catch e =>
    restoreState s
    if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then
      logInfo m!"DTSTUCK target-cert-error {e.toMessageData}"
    return false

/-- Unfold the initial configurations in a refutation goal so the concrete stepper can see them. -/
private def unfoldInitConfigs : TacticM Unit := do
  evalTactic (← `(tactic|
    simp only [initCallConfig, mkEntryFrameWithMem, mkEntryFrame, bindFrameArgs, bindFrameArgs.go,
      applyByValCopies, applyByValCopies.go, splitPhis,
      RegisterValue.matchesType, byvalDeferredAttrs, applyValueAttrsPure, applyValueAttrsSeq, reduceOrderValueAttrs,
      List.length_nil, List.length_cons, List.any_nil, List.any_cons,
      List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.getD_some, Option.getD_none,
      Bool.or_self, Bool.or_false, Bool.false_or, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte, ite_self, List.isEmpty_nil,
      Bool.not_true, Bool.not_false, beq_self_eq_true]))

/-- Prove `⊢ ¬ (src ⊒ tgt)` given an explicit `Expr` of type `List RegisterValue`. -/
def proveDisproofWithExpr (argsExpr : Expr) : TacticM Unit := do
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
  -- First: step both sides with the deterministic-step lemmas.
  let s ← saveState
  unfoldInitConfigs
  runConcreteRefutation 256
  if (← getGoals).isEmpty then return
  -- Otherwise: certify the target's behaviour by execution, then step only the source.
  restoreState s
  if ← replaceTargetByExecution tgtExpr argsExpr then
    unfoldInitConfigs
    strongConcreteSimp.set true
    try runConcreteRefutation 4096 finally strongConcreteSimp.set false
    if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome && !(← getGoals).isEmpty then
      let desc : ConcreteAction → String
        | .halted => "halted" | .ub => "ub" | .instr n => s!"instr {n}" | .term n => s!"term {n}"
        | .unknown => "unknown"
      match ← getNotRefinedConfigs with
      | some (cX, cY) =>
        logInfo m!"DTSTUCK left={desc (← inspectConcreteConfig cX)} right={desc (← inspectConcreteConfig cY)}"
      | none => logInfo m!"DTSTUCK goal={← getMainTarget}"
  else if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then
    logInfo m!"DTSTUCK target-not-certified"
  if !(← getGoals).isEmpty then
    throwError "llvm_disprove: could not close refutation goal with witness {argsExpr}"

end LeanNanoLlvm.Refinement
