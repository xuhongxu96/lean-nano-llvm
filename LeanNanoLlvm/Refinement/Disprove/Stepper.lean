import Lean
import LeanNanoLlvm.Refinement.Disprove.Lemmas

/-! # Kernel-Pure Concrete Stepper for `llvm_disprove`

Given a concrete witness, steps both programs symbolically and closes the refutation goal
with the lemmas from `LeanNanoLlvm.Refinement.Disprove.Lemmas`. -/

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm AST Semantics
open Lean Elab Tactic Meta

/-- A debugging line on standard error (`LNL_DISPROVE_DEBUG`); unlike a message, it survives
`restoreState`. -/
private def dbgLog (m : MessageData) : MetaM Unit := do
  IO.eprintln (← m.toString)

/-- Add a closed theorem checked by the kernel only (no elaboration-side processing of its
possibly large proof term). -/
private def kernelTheorem (type value : Expr) : MetaM Expr := do
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  if type.hasMVar || value.hasMVar then throwError "kernelTheorem: metavariables in the certificate"
  return mkConst (← mkAuxLemma [] type value (cache := false))

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
        if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then dbgLog m!"DTFCMP {e.toMessageData}"
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
private def replaceTargetByExecution (tgtExpr argsExpr : Expr) : TacticM Bool :=
  withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := max ctx.maxRecDepth 100000 }) do
  let tgt ← evalDefn tgtExpr
  let args ← evalArgs argsExpr
  let cfg : SemanticsConfig := .modern
  let c0 := initCallConfig cfg .default64LE {} ∅ ∅ tgt args
  let (cf, used) := runCounting cfg.maxSteps 0 default c0
  let some (_, cY) ← getNotRefinedConfigs | do
      if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then dbgLog m!"DTSTUCK target-no-goal"
      return false
  let fuelE := mkNatLit (used + 1)
  let auxEq (lhs rhs ty : Expr) : MetaM Expr :=
    kernelTheorem (mkApp3 (mkConst ``Eq [1]) ty lhs rhs) (mkApp2 (mkConst ``Eq.refl [1]) ty rhs)
  let runCfgE := mkApp2 (mkConst ``runCfg) fuelE cY
  let s ← saveState
  try
    if cf.isAbortB then
      let h ← auxEq (mkApp (mkConst ``Semantics.Config.isAbortB) runCfgE) (mkConst ``Bool.true) (mkConst ``Bool)
      let hStx ← Term.exprToSyntax h
      let fStx := Syntax.mkNumLit (toString (used + 1))
      evalTactic (← `(tactic|
        refine Config.IsRefinedBy.not_of_canAbort_right
          (CanAbort.of_runCfg $fStx (initCallConfig_empty_wf _ _ _ _ _ _) $hStx) ?_))
      return true
    match cf with
    | .halted v _ =>
      if !(runEvents (used + 1) c0).isEmpty then
        if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then dbgLog m!"DTSTUCK target-emits-events"
        return false
      let ok := match v with
        | .bv _ _ | .void | .float _ _ => true
        | _ => false
      if !ok then
        if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then
          dbgLog m!"DTSTUCK target-returns-unquotable {v.inferType?.map (·.print)}"
        return false
      let vE := quoteRegisterValue v
      let listTy := mkApp (mkConst ``List [0]) (mkConst ``TraceEvent)
      let htr ← auxEq (mkApp2 (mkConst ``runTrace) fuelE cY) (mkApp (mkConst ``List.nil [0]) (mkConst ``TraceEvent)) listTy
      let optTy := mkApp (mkConst ``Option [0]) (mkConst ``RegisterValue)
      let hv ← auxEq (mkApp (mkConst ``Semantics.Config.haltedVal?) runCfgE)
        (mkApp2 (mkConst ``Option.some [0]) (mkConst ``RegisterValue) vE) optTy
      let htrStx ← Term.exprToSyntax htr
      if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then dbgLog m!"DTSTEP tgt-aux-done"
      let hvStx ← Term.exprToSyntax hv
      let fStx := Syntax.mkNumLit (toString (used + 1))
      evalTactic (← `(tactic|
        refine Config.IsRefinedBy.not_of_terminates_right
          (Terminates.of_runCfg $fStx (initCallConfig_empty_wf _ _ _ _ _ _) $htrStx $hvStx) ?_))
      evalTactic (← `(tactic| intro _))
      if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then dbgLog m!"DTSTEP tgt-refined"
      return true
    | _ =>
      if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then
        let k := match cf with
          | .running _ => "running" | .staticError m => s!"staticError {m}" | _ => "other"
        dbgLog m!"DTSTUCK target-run-ends {k} after {used} steps"
      return false
  catch e =>
    restoreState s
    if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then
      dbgLog m!"DTSTUCK target-cert-error {e.toMessageData}"
    return false

/-- Run the source with the interpreter: `.ok (n, final)` if each of its first `n` steps is
choice-free and silent and it then stops (`final` halted or stuck), else why not. -/
private def runSourceDet (c0 : Semantics.Config) (fuel : Nat) : Except String (Nat × Semantics.Config) := Id.run do
  let mut c := c0
  let mut n := 0
  for _ in [:fuel] do
    match c with
    | .running _ =>
      if !c.nextChoiceFree then return .error s!"step {n} takes a choice"
      let (ev, c1, _) := execStep default c
      if ev.isSome then return .error s!"step {n} emits an event"
      c := c1; n := n + 1
    | _ => break
  match c with
  | .halted _ _ | .staticError _ => return .ok (n, c)
  | .ub _ => return .error s!"the source run aborts after {n} steps"
  | _ => return .error s!"the source run does not stop within {fuel} steps"

/-- Certify the source side by execution (`DetRun`, `Config.IsRefinedBy.not_of_detRun_left`) and
close the goal `¬ Config.IsRefinedBy ids cX cY`, where `cY` is `.ub _` or `.halted vY m` (after
`replaceTargetByExecution`). The run is checked in the kernel, with the oracle a free variable for
the independence of each step, so every instruction is supported. Returns `false` (goal unchanged)
if the source run takes a choice, emits an event, or does not stop. -/
private def certifySourceByExecution (srcExpr argsExpr : Expr) : TacticM Bool :=
  withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := max ctx.maxRecDepth 100000 }) do
  let some (cX, cY) ← getNotRefinedConfigs | do
      if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then dbgLog m!"DTSTUCK source-no-goal"
      return false
  let src ← evalDefn srcExpr
  let args ← evalArgs argsExpr
  let cfg : SemanticsConfig := .modern
  let c0 := initCallConfig cfg .default64LE {} ∅ ∅ src args
  let (n, final) ← match runSourceDet c0 cfg.maxSteps with
    | .ok r => pure r
    | .error why =>
      if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then dbgLog m!"DTSTUCK source-run {why}"
      return false
  let s ← saveState
  try
    -- the certificate, in chunks of `chunk` steps (`DetRun k c` for each), built right to left
    let oracleTy := mkConst ``OracleState
    let dflt ← mkAppOptM ``Inhabited.default #[some oracleTy, none]
    let reflTrue := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    let evTy := mkApp (mkConst ``Option [0]) (mkConst ``TraceEvent)
    let cfgTy := mkConst ``Semantics.Config
    let reflNone := mkApp2 (mkConst ``Eq.refl [1]) evTy (mkApp (mkConst ``Option.none [0]) (mkConst ``TraceEvent))
    let chunk := 100000
    let mut left := n
    while left > 0 do
      let m := min chunk left
      let some (cX, _) ← getNotRefinedConfigs | throwError "lost the refutation goal"
      let mut cs : Array Expr := #[cX]
      for _ in [:m] do
        cs := cs.push (mkApp (mkConst ``succCfg) cs.back!)
      let mut proof := mkConst ``True.intro
      for k' in [:m] do
        let k := m - 1 - k'
        let ck := cs[k]!
        let x := mkApp2 (mkConst ``stepEvOf) dflt ck
        let y := mkApp2 (mkConst ``stepCfgErased) dflt ck
        let indep ← withLocalDeclD `o oracleTy fun o => do
          let a := mkApp3 (mkConst ``Eq [1]) evTy (mkApp2 (mkConst ``stepEvOf) o ck) x
          let b := mkApp3 (mkConst ``Eq [1]) cfgTy (mkApp2 (mkConst ``stepCfgErased) o ck) y
          mkLambdaFVars #[o] (mkApp4 (mkConst ``And.intro) a b
            (mkApp2 (mkConst ``Eq.refl [1]) evTy x) (mkApp2 (mkConst ``Eq.refl [1]) cfgTy y))
        proof := mkAppN (mkConst ``DetRun.cons)
          #[mkNatLit k', ck, reflTrue, reflTrue, reflNone, indep, proof]
      let cert ← kernelTheorem (mkApp2 (mkConst ``DetRun) (mkNatLit m) cX) proof
      if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then dbgLog m!"DTSTEP src-cert-done"
      let certStx ← Term.exprToSyntax cert
      evalTactic (← `(tactic| refine Config.IsRefinedBy.not_of_detRun_left _ $certStx ?_))
      left := left - m
      if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then dbgLog m!"DTSTEP src-chunk-applied"
    -- compare the final configurations
    if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then dbgLog m!"DTSTEP src-compare"
    let some (finalE, _) ← getNotRefinedConfigs | throwError "lost the refutation goal"
    let cYw ← whnfR cY
    let auxEq (lhs rhs ty : Expr) (lvl : Level) : MetaM Expr :=
      kernelTheorem (mkApp3 (mkConst ``Eq [lvl]) ty lhs rhs) (mkApp2 (mkConst ``Eq.refl [lvl]) ty rhs)
    match final with
    | .halted vX _ =>
      if cYw.isAppOf ``Semantics.Config.ub then
        let h ← auxEq (mkApp (mkConst ``Option.isSome [0]) (mkConst ``RegisterValue) |>.app
          (mkApp (mkConst ``Semantics.Config.haltedVal?) finalE)) (mkConst ``Bool.true) (mkConst ``Bool) 1
        let hStx ← Term.exprToSyntax h
        evalTactic (← `(tactic| exact Config.IsRefinedBy.not_of_haltedB_ub $hStx))
      else
        let vXE := quoteRegisterValue vX
        let optTy := mkApp (mkConst ``Option [0]) (mkConst ``RegisterValue)
        let h ← auxEq (mkApp (mkConst ``Semantics.Config.haltedVal?) finalE)
          (mkApp2 (mkConst ``Option.some [0]) (mkConst ``RegisterValue) vXE) optTy 1
        let hStx ← Term.exprToSyntax h
        -- the values are unrelated: decided by evaluation (`scalarRefinesB`)
        let vYE := cYw.getArg! 0
        let hb ← auxEq (mkApp2 (mkConst ``scalarRefinesB) vXE vYE) (mkConst ``Bool.false) (mkConst ``Bool) 1
        let hne := mkApp3 (mkConst ``not_isRefinedBy_of_scalarRefinesB) vXE vYE hb
        let hneStx ← Term.exprToSyntax hne
        evalTactic (← `(tactic| exact Config.IsRefinedBy.not_of_haltedVal_halted $hStx $hneStx))
    | .staticError _ =>
      let h ← auxEq (mkApp (mkConst ``Semantics.Config.isStaticB) finalE) (mkConst ``Bool.true) (mkConst ``Bool) 1
      let hStx ← Term.exprToSyntax h
      if cYw.isAppOf ``Semantics.Config.ub then
        evalTactic (← `(tactic| exact Config.IsRefinedBy.not_of_static_ub $hStx))
      else
        evalTactic (← `(tactic| exact Config.IsRefinedBy.not_of_static_halted $hStx))
    | _ => throwError "unexpected final source configuration"
    if !(← getGoals).isEmpty then if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then dbgLog m!"DTSTUCK source-goals-left {← getMainTarget}"
    return (← getGoals).isEmpty
  catch e =>
    restoreState s
    if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then
      dbgLog m!"DTSTUCK source-cert-error {e.toMessageData}"
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
  let s0 ← saveState
  -- 1. Certify both sides by execution: the target's behaviour from an interpreter run
  --    (`runSteps_sound`), the source's whole behaviour from a kernel-checked deterministic run
  --    (`DetRun`, for any instruction whose step takes no choice).
  let ok1 ← tryCatchRuntimeEx
    (do
      if ← replaceTargetByExecution tgtExpr argsExpr then certifySourceByExecution srcExpr argsExpr
      else pure false)
    (fun e => do
      if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then dbgLog m!"DTSTUCK path1 {e.toMessageData}"
      pure false)
  if ok1 then return
  restoreState s0
  -- 2. Step both sides with the deterministic-step lemmas (sources with choices the lemmas cover).
  let ok2 ← tryCatchRuntimeEx
    (do unfoldInitConfigs; runConcreteRefutation 256; pure (← getGoals).isEmpty)
    (fun _ => pure false)
  if ok2 then return
  restoreState s0
  -- 3. The target by execution, the source with the deterministic-step lemmas.
  tryCatchRuntimeEx (do
    if ← replaceTargetByExecution tgtExpr argsExpr then
      unfoldInitConfigs
      strongConcreteSimp.set true
      try runConcreteRefutation 4096 finally strongConcreteSimp.set false
      if (← getGoals).isEmpty then return
      if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then
        let desc : ConcreteAction → String
          | .halted => "halted" | .ub => "ub" | .instr n => s!"instr {n}" | .term n => s!"term {n}"
          | .unknown => "unknown"
        match ← getNotRefinedConfigs with
        | some (cX, cY) =>
          dbgLog m!"DTSTUCK left={desc (← inspectConcreteConfig cX)} right={desc (← inspectConcreteConfig cY)}"
        | none => dbgLog m!"DTSTUCK goal={← getMainTarget}"
    else if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then
      dbgLog m!"DTSTUCK target-not-certified")
    (fun e => do
      if (← IO.getEnv "LNL_DISPROVE_DEBUG").isSome then dbgLog m!"DTSTUCK error {e.toMessageData}")
  throwError "llvm_disprove: could not close refutation goal with witness {argsExpr}"

end LeanNanoLlvm.Refinement
