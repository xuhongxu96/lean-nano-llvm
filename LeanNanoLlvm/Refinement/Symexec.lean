import Lean
import LeanNanoLlvm.Refinement.Lemmas

/-!
# Symbolic Execution (`llvm_intro`, `llvm_symexec`, `llvm_guard`)

The first two layers of the refinement pipeline (see `LeanNanoLlvm.Refinement.Tactic` for the
whole pipeline and when to use each layer):

1. `llvm_intro`   — Unpacks `Definition.IsRefinedBy*`, checks signature compatibility, introduces
                    `initMem` and `args`, destructures `args` into `arg0`, `arg1`, ... for any
                    arity, and reduces `initCallConfig` on both sides to `.running` states.
2. `llvm_symexec` — Dispatches on the head AST constructor of the current instruction/terminator
                    to symbolically execute source and target (`intBinaryOp`, `icmp`, `select`,
                    `conversionOp`, `floatUnaryOp`, `freeze`, `br`, `condBr`, `switch`, `phi`,
                    `ret`, `retVoid`, `unreachable`), short-circuiting on source `.ub` / `CanAbort`
                    and reducing `.halted` vs `.halted` to `RegisterValue.IsRefinedBy .id retX retY`.
                    When a `condBr` depends on a symbolic `i1` value, it asks the step
                    lemma which value that is and case-splits on it; the case is kept as a
                    named hypothesis `h_br` (normalized from `BitVec.ofBool b` to a statement
                    about `b`). A goal it cannot advance stays as `Config.IsRefinedBy`.

`llvm_guard tac` is a helper used by the later layers: it turns runtime exceptions raised by
`tac` into ordinary failures.

All tactics produce standard kernel proof terms using only `{propext, Classical.choice,
Quot.sound}` (no `bv_decide`, `native_decide`, or `Lean.ofReduceBool`). The `simp_llvm` /
`simp_step` lemmas they rely on live in `LeanNanoLlvm.Refinement.Lemmas`.
-/

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

/-! ### Symbolic Execution Tactics -/

section Tactics

open Lean Meta Elab Tactic

/-- `llvm_guard tac` runs `tac` and turns a runtime exception (such as `maximum recursion depth`,
    which `rfl` or `decide` can raise on `BitVec` goals with large literals) into an ordinary
    failure. `try` and `first` do not catch runtime exceptions, so without this guard one such
    closer aborts the whole tactic instead of leaving the goal open. -/
elab "llvm_guard " t:tacticSeq : tactic => do
  let s ← saveState
  tryCatchRuntimeEx (evalTactic t) fun e => do
    restoreState s
    if e.isRuntime then throwError "llvm_guard: {e.toMessageData}" else throw e

/-! ### Script recording (for `llvm_refine??`)

When the option `llvm.recordScript` is set, every step the pipeline takes is recorded as a
surface tactic together with the goal it ran on and the goals it produced. `llvm_refine??`
turns these records into a nested proof script. A record is an info message tagged
`scriptTag`, so that backtracking (`restoreState`) discards the records of abandoned attempts
together with the attempt itself; `llvm_refine??` removes the records from the message log
before it finishes. Inside a recorded step, nested steps are not recorded. -/

/-- The tag of a step record in the message log. -/
def scriptTag : Name := `LeanNanoLlvm.Refinement.scriptStep

/-- Are steps being recorded at this point (recording on, and not inside a recorded step)? -/
def recordingScript : CoreM Bool := do
  let o ← getOptions
  return o.getBool `llvm.recordScript && !o.getBool `llvm.inStep

/-- Record that `text` turned goal `g` into the goals `outs`. An empty `text` records that `g`
    was replaced by `outs` without a visible step. -/
def recordStep (g : MVarId) (outs : List MVarId) (text : String) : CoreM Unit := do
  if !(← recordingScript) then return
  let sep := "\x1f"
  let enc := s!"{g.name}{sep}{",".intercalate (outs.map (toString ·.name))}{sep}{text}"
  logInfo (.tagged scriptTag (MessageData.ofFormat (format enc)))

/-- Source text of a tactic, with hygienic suffixes removed so that it can be pasted. -/
def showTactic (stx : Syntax) : CoreM String := do
  let stx := stx.rewriteBottomUp fun
    | .ident info raw n pre => .ident info raw n.eraseMacroScopes pre
    | s => s
  return toString (← PrettyPrinter.ppTactic ⟨stx⟩)

/-- `evalTactic`, recording the step (see above) when recording is on. `display?` overrides
    the recorded text. -/
def evalStep (stx : Syntax) (display? : Option String := none) : TacticM Unit := do
  if !(← recordingScript) then return ← evalTactic stx
  match ← getGoals with
  | [] => evalTactic stx
  | g :: rest =>
    withOptions (fun o => o.setBool `llvm.inStep true) (evalTactic stx)
    let outs := (← getGoals).filter (!rest.contains ·)
    recordStep g outs (← match display? with | some d => pure d | none => showTactic stx)

/-- Extract head definition names of `x` and `y` in `Definition.IsRefinedBy*` (when they are
    user-defined constants rather than raw `AST.Definition.mk` constructors). -/
private def getRefinementDefConsts : TacticM (List Name) := do
  let goal ← instantiateMVars (← getMainTarget)
  let fn := goal.getAppFn
  let args := goal.getAppArgs
  let pair? : Option (Expr × Expr) :=
    if fn.isConstOf ``HRefinement.IsRefinedBy && args.size ≥ 5 then
      some (args[3]!, args[4]!)
    else if fn.isConstOf ``Definition.IsRefinedBy && args.size ≥ 2 then
      some (args[0]!, args[1]!)
    else if fn.isConstOf ``Definition.IsRefinedByWith && args.size ≥ 4 then
      some (args[2]!, args[3]!)
    else if fn.isConstOf ``Definition.IsRefinedByIn && args.size ≥ 3 then
      some (args[1]!, args[2]!)
    else none
  let mut names : List Name := []
  if let some (x, y) := pair? then
    for e in [x, y] do
      let h := e.getAppFn
      if let .const nm _ := h then
        if nm != ``AST.Definition.mk && !names.contains nm then
          names := nm :: names
  return names

/-- Fuel-bounded destructuring of `hargs` after rewriting with `wellFormedForList_*_iff`. -/
private def destructArgHyps (fuel idx : Nat) (hargsId : Ident) : TacticM Unit := do
  match fuel with
  | 0 => return ()
  | fuel + 1 =>
    let argId := mkIdent (Name.mkSimple s!"arg{idx}")
    let progressed ←
      try
        evalStep (← `(tactic|
          rcases $hargsId:ident with ⟨_, _, h_eq_args, ⟨$argId:ident, h_eq_val⟩, $hargsId:ident⟩;
          subst h_eq_val; subst h_eq_args))
        pure true
      catch _ =>
        try
          evalStep (← `(tactic| subst $hargsId:ident))
          pure false
        catch _ =>
          pure false
    if progressed then
      destructArgHyps fuel (idx + 1) hargsId

/-- `llvm_intro` unpacks `Definition.IsRefinedBy*`, discharges `SignatureCompatible` via `rfl`,
    introduces `initMem` & `args`, destructures `args` for any arity `0..N`, and reduces
    `initCallConfig` on both source and target to `.running` configurations. -/
elab "llvm_intro" : tactic => do
  let defNames ← getRefinementDefConsts
  evalStep (← `(tactic|
    dsimp only [HRefinement.IsRefinedBy, Refinement.IsRefinedBy, instHRefinementOfRefinement,
      Definition.IsRefinedBy, Definition.IsRefinedByWith, Definition.IsRefinedByIn]))
  evalStep (← `(tactic| refine ⟨rfl, ?_⟩))
  let initMemId := mkIdent `initMem
  let argsId := mkIdent `args
  let hwfMemId := mkIdent `hwfMem
  let hargsId := mkIdent `hargs
  evalStep (← `(tactic| intro $initMemId:ident $argsId:ident $hwfMemId:ident $hargsId:ident))
  for nm in defNames do
    let id := mkIdent nm
    try evalStep (← `(tactic| dsimp only [$id:ident] at $hargsId:ident ⊢)) catch _ => pure ()
  evalStep (← `(tactic|
    simp only [Semantics.Definition.ArgValuesWellFormed,
      RegisterValue.wellFormedForList_cons_iff, RegisterValue.wellFormedForList_nil_iff,
      RegisterValue.wellFormedFor_int_iff, RegisterValue.wellFormedFor_float_iff,
      RegisterValue.wellFormedFor_ptr_iff] at $hargsId:ident))
  destructArgHyps 32 0 hargsId
  evalStep (← `(tactic|
    simp only [initCallConfig, mkEntryFrameWithMem, mkEntryFrame, bindFrameArgs, bindFrameArgs.go,
      applyByValCopies, applyByValCopies.go, splitPhis,
      RegisterValue.matchesType, byvalDeferredAttrs, applyValueAttrsPure, applyValueAttrsSeq, reduceOrderValueAttrs,
      applySingleAttrPure_noundef_bv_value, applySingleAttrPure_noundef_bv_poison,
      applySingleAttrPure_range_bv_value, applySingleAttrPure_range_bv_poison, except_bind_ok, except_bind_error,
      withSiteAttrs_nil,
      List.length_nil, List.length_cons, List.any_nil, List.any_cons,
      List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.getD_some, Option.getD_none,
      Bool.or_self, Bool.or_false, Bool.false_or, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte, ite_self, List.isEmpty_nil,
      Bool.not_true, Bool.not_false, beq_self_eq_true]))

/-- Classification of the next action for a `Config` expression (O(1) AST head inspection). -/
private inductive NextAction
  | ub
  | halted
  | instr (headConst : Name)
  | term (headConst : Name)
  | unknown

/-- Inspect a `Config` expression without triggering expensive `simp` calls. -/
private def inspectConfig (c : Expr) : MetaM NextAction := do
  withTransparency .reducible do
    let c ← whnf c
    if c.isAppOf ``Config.ub then return .ub
    if c.isAppOf ``Config.halted then return .halted
    if !c.isAppOf ``Config.running then return .unknown
    let st ← whnf c.appArg!
    if !st.isAppOf ``MachineState.mk then return .unknown
    let stArgs := st.getAppArgs
    if stArgs.size < 1 then return .unknown
    let frames ← whnf stArgs[0]!
    if !frames.isAppOf ``List.cons then return .unknown
    let frame ← whnf frames.getAppArgs[1]!
    if !frame.isAppOf ``CallFrame.mk then return .unknown
    let fArgs := frame.getAppArgs
    if fArgs.size < 4 then return .unknown
    let remCode ← whnf fArgs[2]!
    let termPair ← whnf fArgs[3]!
    if remCode.isAppOf ``List.cons then
      let hd ← whnf remCode.getAppArgs[1]!
      if hd.isAppOf ``Prod.mk && hd.getAppArgs.size ≥ 4 then
        let instr ← whnf hd.getAppArgs[3]!
        if let .const nm _ := instr.getAppFn then
          return .instr nm
      return .unknown
    else if remCode.isAppOf ``List.nil then
      if termPair.isAppOf ``Prod.mk && termPair.getAppArgs.size ≥ 4 then
        let term ← whnf termPair.getAppArgs[3]!
        if let .const nm _ := term.getAppFn then
          return .term nm
      return .unknown
    else
      return .unknown

/-- Close a goal of the form `∀ res, EvalPhis ... phis res ↔ res = .ok (?ups, mem)`. -/
private def solveEvalPhis (fuel : Nat) : TacticM Unit := do
  match fuel with
  | 0 => throwError "solveEvalPhis: fuel exhausted"
  | fuel + 1 =>
    let s ← saveState
    try
      evalStep (← `(tactic| exact fun _ => EvalPhis.nil_iff))
    catch _ =>
      restoreState s
      evalStep (← `(tactic| intro res_phi; apply EvalPhis.cons_leaf_iff))
      evalStep (← `(tactic| (simp [List.find?, -Prod.mk.injEq, -Option.some.injEq]; rfl)))
      evalStep (← `(tactic| ((try llvm_step); rfl)))
      solveEvalPhis fuel

/-- `llvm_simp_after_step` simplifies a `Config.IsRefinedBy` goal right after a symbolic step:
    it commits the step's frame and register updates and evaluates pure operations. -/
macro "llvm_simp_after_step" : tactic => `(tactic| (
      (try simp only [liftBinaryPure_bv, evalIntBinaryScalarPure, evalDivRemUB_ite_poison]);
      simp only [finishRegInstr, finishVoidInstr, CallFrame.advance, CallFrame.jumpTo,
        MachineState.withFrames, MachineState.withFramesAndMemory,
        commitPhiUpdates, freeAllocaList,
        applyRetFMFAndAttrsPure, applyValueAttrsPure, applyValueAttrsSeq, reduceOrderValueAttrs,
        liftBinaryPure_bv, evalIntBinaryScalarPure, evalICmpScalarPure_bv,
        evalSelectPure_bv, evalSelectPure_float, evalSelectPure_ptr,
        evalConversionExec_trunc, evalConversionExec_zext, evalConversionExec_sext,
        evalFloatUnaryExec_fneg_no_nsz, evalDivRemUB_ite_poison, evalDivRemUB, ite_except_ok, RegisterValue.poisonOf,
        bitvec_ofInt_ofNat, bitvec_ofInt_neg, bitvec_ofInt_negSucc,
        BitVec.ofNat_eq_ofNat,
        AST.LlvmType.scalarType, AST.FastMathFlags.any,
        Bool.or_self, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte,
        beq_self_eq_true, Config.ofError]))

/-- Simplify a `Config.IsRefinedBy` goal immediately after taking a symbolic step. -/
private def simpAfterStep : TacticM Unit := do
  try evalStep (← `(tactic| llvm_simp_after_step))
  catch _ => pure ()

/-- Step the source (`cX`) side based on its O(1)-inspected `NextAction`. -/
private def stepSourceAction (act : NextAction) : TacticM Bool := do
  match act with
  | .ub =>
    try evalStep (← `(tactic| exact Config.IsRefinedBy.of_ub_left)); return true
    catch _ => return false
  | .instr nm =>
    if nm == ``AST.Instruction.intBinaryOp then
      let s ← saveState
      try
        evalStep (← `(tactic|
          refine Config.IsRefinedBy.of_step_left
            ((Step.intBinaryOp_leaf_iff rfl rfl (by llvm_step; rfl) (by llvm_step; rfl) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.icmp then
      let s ← saveState
      try
        evalStep (← `(tactic|
          refine Config.IsRefinedBy.of_step_left
            ((Step.icmp_leaf_iff rfl rfl (by llvm_step; rfl) (by llvm_step; rfl) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.select then
      let s ← saveState
      try
        evalStep (← `(tactic|
          refine Config.IsRefinedBy.of_step_left
            ((Step.select_leaf_iff rfl rfl (by llvm_step; rfl) (by llvm_step; rfl) (by llvm_step; rfl) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.conversionOp then
      let s ← saveState
      try
        evalStep (← `(tactic|
          refine Config.IsRefinedBy.of_step_left
            ((Step.conversionOp_leaf_iff rfl rfl (by llvm_step; rfl) (fun _ => rfl) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.floatUnaryOp then
      let s ← saveState
      try
        evalStep (← `(tactic|
          refine Config.IsRefinedBy.of_step_left
            ((Step.floatUnaryOp_leaf_iff rfl rfl (by llvm_step; rfl)
              (fun o => evalFloatUnaryExec_fneg_no_nsz _ rfl _ (by decide) _ o) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.freeze then
      let s ← saveState
      try
        evalStep (← `(tactic| apply Config.IsRefinedBy.of_step_left))
        evalStep (← `(tactic| apply Step.freeze_bv_val rfl rfl))
        focus (evalStep (← `(tactic| (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done)))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else return false
  | .term nm =>
    if nm == ``AST.Terminator.unreachable then
      let s ← saveState
      try evalStep (← `(tactic| exact Config.IsRefinedBy.of_unreachable_left rfl rfl rfl)); return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.ret then
      let s ← saveState
      try
        evalStep (← `(tactic|
          refine Config.IsRefinedBy.of_step_left
            ((Step.ret_top_leaf_iff rfl rfl rfl rfl (by llvm_step; rfl) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.retVoid then
      let s ← saveState
      try
        evalStep (← `(tactic|
          refine Config.IsRefinedBy.of_step_left
            ((Step.retVoid_top_iff rfl rfl rfl rfl none _).mpr ⟨rfl, rfl⟩) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.br then
      let s ← saveState
      try
        evalStep (← `(tactic| apply Config.IsRefinedBy.of_step_left))
        evalStep (← `(tactic| apply Step.br_det rfl rfl rfl))
        evalStep (← `(tactic| (simp [AST.Definition.findBlock?]; rfl)))
        evalStep (← `(tactic| (simp only [splitPhis]; rfl)))
        solveEvalPhis 16; simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.condBr then
      let s ← saveState
      let isPoison ←
        try
          evalStep (← `(tactic|
            apply Config.IsRefinedBy.of_canAbort;
            apply Step.condBr_poison_canAbort rfl rfl rfl;
            (try llvm_step); (try rfl); done))
          pure true
        catch _ =>
          restoreState s
          pure false
      if isPoison then return true
      let s2 ← saveState
      try
        evalStep (← `(tactic| apply Config.IsRefinedBy.of_step_left))
        evalStep (← `(tactic| apply Step.condBr_val_det rfl rfl rfl))
        evalStep (← `(tactic| (llvm_step; rfl)))
        evalStep (← `(tactic| (simp [AST.Definition.findBlock?]; rfl)))
        evalStep (← `(tactic| (simp only [splitPhis]; rfl)))
        solveEvalPhis 16; simpAfterStep; return true
      catch _ =>
        restoreState s2
        return false
    else if nm == ``AST.Terminator.switch then
      let s ← saveState
      let isPoison ←
        try
          evalStep (← `(tactic|
            apply Config.IsRefinedBy.of_canAbort;
            apply Step.switch_poison_canAbort rfl rfl rfl;
            (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done))
          pure true
        catch _ =>
          restoreState s
          pure false
      if isPoison then return true
      let s2 ← saveState
      try
        evalStep (← `(tactic| apply Config.IsRefinedBy.of_step_left))
        evalStep (← `(tactic| apply Step.switch_val_det rfl rfl rfl))
        focus (evalStep (← `(tactic| (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done)))
        evalStep (← `(tactic| (simp [AST.Definition.findBlock?, List.find?, bitvec_ofInt_ofNat, bitvec_ofInt_negSucc]; rfl)))
        evalStep (← `(tactic| (simp only [splitPhis]; rfl)))
        solveEvalPhis 16; simpAfterStep; return true
      catch _ =>
        restoreState s2
        return false
    else return false
  | _ => return false

/-- Step the target (`cY`) side based on its O(1)-inspected `NextAction`. -/
private def stepTargetAction (act : NextAction) : TacticM Bool := do
  match act with
  | .instr nm =>
    if nm == ``AST.Instruction.intBinaryOp then
      let s ← saveState
      try
        evalStep (← `(tactic|
          refine Config.IsRefinedBy.of_det_step_right
            (Step.intBinaryOp_leaf_iff rfl rfl (by llvm_step; rfl) (by llvm_step; rfl)) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.icmp then
      let s ← saveState
      try
        evalStep (← `(tactic|
          refine Config.IsRefinedBy.of_det_step_right
            (Step.icmp_leaf_iff rfl rfl (by llvm_step; rfl) (by llvm_step; rfl)) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.select then
      let s ← saveState
      try
        evalStep (← `(tactic|
          refine Config.IsRefinedBy.of_det_step_right
            (Step.select_leaf_iff rfl rfl (by llvm_step; rfl) (by llvm_step; rfl) (by llvm_step; rfl)) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.conversionOp then
      let s ← saveState
      try
        evalStep (← `(tactic|
          refine Config.IsRefinedBy.of_det_step_right
            (Step.conversionOp_leaf_iff rfl rfl (by llvm_step; rfl) (fun _ => rfl)) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.floatUnaryOp then
      let s ← saveState
      try
        evalStep (← `(tactic|
          refine Config.IsRefinedBy.of_det_step_right
            (Step.floatUnaryOp_leaf_iff rfl rfl (by llvm_step; rfl)
              (fun o => evalFloatUnaryExec_fneg_no_nsz _ rfl _ (by decide) _ o)) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.freeze then
      let s ← saveState
      try
        evalStep (← `(tactic| apply Config.IsRefinedBy.of_det_step_right))
        evalStep (← `(tactic| apply Step.freeze_bv_val_iff rfl rfl))
        focus (evalStep (← `(tactic| (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done)))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else return false
  | .term nm =>
    if nm == ``AST.Terminator.ret then
      let s ← saveState
      try
        evalStep (← `(tactic|
          refine Config.IsRefinedBy.of_det_step_right
            (Step.ret_top_leaf_iff rfl rfl rfl rfl (by llvm_step; rfl)) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.retVoid then
      let s ← saveState
      try
        evalStep (← `(tactic|
          refine Config.IsRefinedBy.of_det_step_right
            (Step.retVoid_top_iff rfl rfl rfl rfl) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.br then
      let s ← saveState
      try
        evalStep (← `(tactic| apply Config.IsRefinedBy.of_det_step_right))
        evalStep (← `(tactic| apply Step.br_det_iff rfl rfl rfl))
        evalStep (← `(tactic| (simp [AST.Definition.findBlock?]; rfl)))
        evalStep (← `(tactic| (simp only [splitPhis]; rfl)))
        solveEvalPhis 16; simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.condBr then
      let s ← saveState
      try
        evalStep (← `(tactic| apply Config.IsRefinedBy.of_det_step_right))
        evalStep (← `(tactic| apply Step.condBr_val_det_iff rfl rfl rfl))
        evalStep (← `(tactic| ((try llvm_step); rfl)))
        evalStep (← `(tactic| (simp [AST.Definition.findBlock?]; rfl)))
        evalStep (← `(tactic| (simp only [splitPhis]; rfl)))
        solveEvalPhis 16; simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.switch then
      let s ← saveState
      try
        evalStep (← `(tactic| apply Config.IsRefinedBy.of_det_step_right))
        evalStep (← `(tactic| apply Step.switch_val_det_iff rfl rfl rfl))
        focus (evalStep (← `(tactic| (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done)))
        evalStep (← `(tactic| (simp [AST.Definition.findBlock?, List.find?, bitvec_ofInt_ofNat, bitvec_ofInt_negSucc]; rfl)))
        evalStep (← `(tactic| (simp only [splitPhis]; rfl)))
        solveEvalPhis 16; simpAfterStep; return true
      catch _ => restoreState s; return false
    else return false
  | _ => return false

/-- Try to finish a halted-vs-halted goal. -/
private def tryFinishHalted : TacticM Bool := do
  let s ← saveState
  try
    evalStep (← `(tactic| apply Config.IsRefinedBy.of_halted_same_mem))
    return true
  catch _ =>
    restoreState s
    let s2 ← saveState
    try
      evalStep (← `(tactic| apply Config.IsRefinedBy.of_halted))
      return true
    catch _ =>
      restoreState s2
      return false

/-- Evaluate value attributes (`applySingleAttrPure`) left in the goal once their value is
concrete enough: after an argument is split into `.poison`/`.value`, or a `range` condition is
decided. Only runs when the goal mentions `applySingleAttrPure` (the simp is not free on large
goals). -/
private def simpValueAttrs : TacticM Unit := do
  let hasAttr ← withMainContext do
    return ((← instantiateMVars (← getMainTarget)).find? (·.isConstOf ``applySingleAttrPure)).isSome
  if hasAttr then
    try evalStep (← `(tactic| simp only [applySingleAttrPure_noundef_bv_value,
      applySingleAttrPure_noundef_bv_poison, applySingleAttrPure_range_bv_value,
      applySingleAttrPure_range_bv_poison, except_bind_ok, except_bind_error])) catch _ => pure ()

/-- Try splitting a single `PoisonOr` hypothesis (used when symbolic `condBr`, `freeze`, or
    `evalDivRemUB` needs to inspect whether a symbolic operand is `.poison` or `.value`). -/
private def trySplitOnePoisonOr : TacticM Bool := do
  let target? ← withMainContext do
    let lctx ← getLCtx
    for decl in lctx do
      if !decl.isImplementationDetail then
        let ty ← instantiateMVars decl.type
        if ty.isAppOf ``PoisonOr || ty.isAppOf ``IntW || ty.isAppOf ``FloatW then
          return some decl.userName
    return none
  if let some nm := target? then
    let id := mkIdent nm
    evalStep (← `(tactic| cases $id:ident using PoisonOr.casesOn'))
    let mut gs ← getGoals
    -- `casesOn'` yields `[poison, value]`; the value keeps the argument's name.
    if let [gp, gv] := gs then
      setGoals [gv]
      try
        evalStep (← `(tactic| rename_i $id:ident))
        gs := [gp] ++ (← getGoals)
      catch _ => pure ()
    let mut out : List MVarId := []
    for g in gs do
      setGoals [g]
      -- parameter attributes become evaluable once the argument is `.poison` or `.value`
      simpValueAttrs
      try evalStep (← `(tactic| llvm_simp)) catch _ => pure ()
      simpAfterStep
      out := out ++ (← getGoals)
    setGoals out
    return true
  return false

theorem bitvec1_eq_zero_or_one (b : BitVec 1) : b = 0#1 ∨ b = 1#1 := by
  rcases b with ⟨⟨v, hv⟩⟩
  match v, hv with
  | 0, _ => exact Or.inl rfl
  | 1, _ => exact Or.inr rfl

/-- Try splitting a symbolic `BitVec 1` hypothesis (`0#1` vs `1#1`) for `condBr`. -/
private def trySplitOneBoolBv : TacticM Bool := do
  let target? ← withMainContext do
    let lctx ← getLCtx
    for decl in lctx do
      if !decl.isImplementationDetail then
        let ty ← instantiateMVars decl.type
        if ty.isAppOf ``BitVec && ty.getAppArgs.size == 1 then
          if ty.getAppArgs[0]! == mkNatLit 1 then
            return some decl.userName
    return none
  if let some nm := target? then
    let id := mkIdent nm
    let s ← saveState
    try
      evalStep (← `(tactic|
        rcases bitvec1_eq_zero_or_one $id:ident with h_bv1_eq | h_bv1_eq <;> subst h_bv1_eq))
      let gs ← getGoals
      let mut out : List MVarId := []
      for g in gs do
        setGoals [g]
        try evalStep (← `(tactic| llvm_simp)) catch _ => pure ()
        simpAfterStep
        out := out ++ (← getGoals)
      setGoals out
      return true
    catch _ =>
      restoreState s
      return false
  return false

/-- The value a `condBr` on side `source` (or the target) branches on, as computed by the step
    lemma's own operand evaluation. Returns it only when it is symbolic (mentions free variables),
    i.e. when the branch cannot be decided. -/
private def condBrValue? (source : Bool) : TacticM (Option Expr) := do
  let s ← saveState
  let r ← try
      if source then
        evalStep (← `(tactic| apply Config.IsRefinedBy.of_step_left))
        evalStep (← `(tactic| apply Step.condBr_val_det rfl rfl rfl))
      else
        evalStep (← `(tactic| apply Config.IsRefinedBy.of_det_step_right))
        evalStep (← `(tactic| apply Step.condBr_val_det_iff rfl rfl rfl))
      let hcondTy ← (← getMainGoal).getType
      evalStep (← `(tactic| ((try llvm_step); rfl)))
      -- `hcond : evalPureLeafExp? ... = some (.ok (.bv 1 (.value b)))`: read `b` from the rhs.
      let rhs := (← instantiateMVars hcondTy).appArg!
      let some b := (rhs.find? (·.isAppOfArity ``PoisonOr.value 2)).map (·.appArg!)
        | pure none
      if ← isDefEq (← inferType b) (mkApp (mkConst ``BitVec) (mkNatLit 1)) then pure (some b)
      else pure none
    catch _ => pure none
  restoreState s
  match r with
  | some e => return if e.hasFVar && !e.hasMVar then some e else none
  | none => return none

/-- When a `condBr` is stuck because its condition is a symbolic `i1` value `e`, case-split on
    `e = 0#1 ∨ e = 1#1`, rewrite `e` in the goal so the branch can be taken, and keep the case as
    a named hypothesis (normalized from `BitVec.ofBool b = _` to a statement about `b`). -/
private def trySplitBranchValue (actX actY : NextAction) : TacticM Bool := do
  let isCondBr : NextAction → Bool
    | .term nm => nm == ``AST.Terminator.condBr
    | _ => false
  let mut e? : Option Expr := none
  if isCondBr actX then e? ← condBrValue? true
  if e?.isNone && isCondBr actY then e? ← condBrValue? false
  let some e := e? | return false
  let s ← saveState
  try
    let g0 ← getMainGoal
    let nm := (← g0.getDecl).lctx.getUnusedName `h_br
    let hId := mkIdent nm
    let g ← g0.assert nm (← inferType (mkApp (mkConst ``bitvec1_eq_zero_or_one) e))
      (mkApp (mkConst ``bitvec1_eq_zero_or_one) e)
    let (_, g) ← g.intro1P
    recordStep g0 [g] s!"have {nm} := bitvec1_eq_zero_or_one ({← g0.withContext (ppExpr e)})"
    setGoals [g]
    evalStep (← `(tactic| rcases $hId:ident with $hId:ident | $hId:ident))
    let gs ← getGoals
    let mut out : List MVarId := []
    for sg in gs do
      setGoals [sg]
      evalStep (← `(tactic| simp only [$hId:ident]))
      try evalStep (← `(tactic|
        simp only [bitvec_ofBool_eq_zero, bitvec_ofBool_eq_one, bne_eq_false_iff_eq, bne_iff_ne,
          beq_eq_false_iff_ne, beq_iff_eq, Bool.and_eq_true, Bool.or_eq_true, Bool.and_eq_false_iff,
          Bool.or_eq_false_iff, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq,
          decide_eq_false_iff_not] at $hId:ident)) catch _ => pure ()
      -- Drop the new hypothesis if an earlier one already states the same fact.
      try
        let g ← getMainGoal
        let dup ← g.withContext do
          let lctx ← getLCtx
          let some d := lctx.findFromUserName? nm | return false
          lctx.anyM fun d' => do
            if d'.fvarId == d.fvarId || d'.isImplementationDetail then return false
            withReducible (isDefEq d'.type d.type)
        if dup then evalStep (← `(tactic| clear $hId:ident))
      catch _ => pure ()
      simpAfterStep
      out := out ++ (← getGoals)
    setGoals out
    return true
  catch _ =>
    restoreState s
    return false

/-- Handle nondeterministic `freeze` on `.poison` (peeling target via `of_freeze_poison_right` first,
    then matching source via `freeze_bv_poison_step`). -/
private def tryStepFreezePoison (actX actY : NextAction) : TacticM Bool := do
  -- 1. If target is `freeze` on `.poison`, peel target universally first
  if let .instr nmY := actY then
    if nmY == ``AST.Instruction.freeze then
      let s ← saveState
      try
        let bId := mkIdent `b_frz
        let hmId := mkIdent `hmode_frz
        evalStep (← `(tactic| apply Config.IsRefinedBy.of_freeze_poison_right rfl rfl))
        focus (evalStep (← `(tactic| (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done)))
        evalStep (← `(tactic| intro $bId:ident $hmId:ident))
        simpAfterStep
        return true
      catch _ =>
        restoreState s
  -- 2. If source is `freeze` on `.poison`, step source using `b_frz` / `hmode_frz` if present, else `0`
  if let .instr nmX := actX then
    if nmX == ``AST.Instruction.freeze then
      let s1 ← saveState
      try
        let bId := mkIdent `b_frz
        let hmId := mkIdent `hmode_frz
        evalStep (← `(tactic| apply Config.IsRefinedBy.of_step_left))
        evalStep (← `(tactic| refine Step.freeze_bv_poison_step rfl rfl ?_ $bId:ident $hmId:ident))
        focus (evalStep (← `(tactic| (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done)))
        simpAfterStep
        return true
      catch _ =>
        restoreState s1
        let s2 ← saveState
        try
          evalStep (← `(tactic| apply Config.IsRefinedBy.of_step_left))
          evalStep (← `(tactic| apply Step.freeze_bv_poison_zero rfl rfl))
          focus (evalStep (← `(tactic| (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done)))
          simpAfterStep
          return true
        catch _ =>
          restoreState s2
  return false

/-- Fuel-bounded symbolic execution loop on all open `Config.IsRefinedBy` goals. -/
private def symexecLoop (fuel : Nat) : TacticM Unit := do
  match fuel with
  | 0 => return ()
  | fuel + 1 =>
    let goals ← getGoals
    if goals.isEmpty then return ()
    let mut anyProgress := false
    let mut remaining : List MVarId := []
    for g in goals do
      setGoals [g]
      let tgt ← instantiateMVars (← getMainTarget)
      if tgt.isAppOf ``Config.IsRefinedBy && tgt.getAppArgs.size ≥ 3 then
        let cX := tgt.getAppArgs[1]!
        let cY := tgt.getAppArgs[2]!
        let (actX, actY) ← withMainContext do
          return (← inspectConfig cX, ← inspectConfig cY)
        match actX, actY with
        | .halted, .halted =>
          if ← tryFinishHalted then
            anyProgress := true
            remaining := remaining ++ (← getGoals)
          else
            remaining := remaining ++ [g]
        | _, _ =>
          let p1 ← stepSourceAction actX
          if p1 then
            anyProgress := true
            remaining := remaining ++ (← getGoals)
          else
            let p2 ← stepTargetAction actY
            if p2 then
              anyProgress := true
              remaining := remaining ++ (← getGoals)
            else
              -- Try nondeterministic `freeze` on `.poison`
              let p3 ← tryStepFreezePoison actX actY
              if p3 then
                anyProgress := true
                remaining := remaining ++ (← getGoals)
              else
                -- Try simplifying / splitting when stuck on symbolic `condBr`, `switch`, `freeze`, or `div`/`rem`
                let needsSplit :=
                  match actX, actY with
                  | .term ``AST.Terminator.condBr, _ => true
                  | _, .term ``AST.Terminator.condBr => true
                  | .term ``AST.Terminator.switch, _ => true
                  | _, .term ``AST.Terminator.switch => true
                  | .instr ``AST.Instruction.freeze, _ => true
                  | _, .instr ``AST.Instruction.freeze => true
                  | .unknown, _ => true
                  | _, .unknown => true
                  | _, _ => false
                if needsSplit && (← trySplitBranchValue actX actY) then
                  anyProgress := true
                  remaining := remaining ++ (← getGoals)
                else if needsSplit then
                  let p4 ← trySplitOnePoisonOr
                  if p4 then
                    anyProgress := true
                    remaining := remaining ++ (← getGoals)
                  else
                    let p5 ← trySplitOneBoolBv
                    if p5 then
                      anyProgress := true
                      remaining := remaining ++ (← getGoals)
                    else
                      let sSplit ← saveState
                      let p6 ←
                        try
                          let cond? ← withMainContext do
                            let tgt ← instantiateMVars (← getMainTarget)
                            let found := tgt.find? fun e => e.isAppOf ``ite && e.getAppArgs.size ≥ 5
                            match found with
                            | some e => return some e.getAppArgs[1]!
                            | none => return none
                          if let some condExpr := cond? then
                            let hName := mkIdent ((← getMainDecl).lctx.getUnusedName `h_ite_sym)
                            let condStx ← withMainContext (Lean.PrettyPrinter.delab condExpr)
                            evalStep (← `(tactic| by_cases $hName:ident : $condStx))
                            let gs ← getGoals
                            let mut out : List MVarId := []
                            for sg in gs do
                              setGoals [sg]
                              try evalStep (← `(tactic| simp only [$hName:ident, ↓reduceIte, not_false_eq_true])) catch _ => pure ()
                              simpValueAttrs
                              simpAfterStep
                              out := out ++ (← getGoals)
                            setGoals out
                            pure true
                          else
                            pure false
                        catch _ =>
                          restoreState sSplit
                          pure false
                      if p6 then
                        anyProgress := true
                        remaining := remaining ++ (← getGoals)
                      else
                        remaining := remaining ++ [g]
                else
                  remaining := remaining ++ [g]
      else
        remaining := remaining ++ [g]
    setGoals remaining
    if anyProgress then
      symexecLoop fuel

/-- `llvm_symexec` symbolically executes deterministic silent instructions and terminators on
    source and target using O(1) AST head dispatch, handles symbolic `condBr`/`switch` branching
    and nondeterministic `freeze`, closes `.ub` / `unreachable` / `condBr poison` / `switch poison`
    goals immediately, and reduces `.halted` vs `.halted` to `RegisterValue.IsRefinedBy .id retX retY`. -/
elab "llvm_symexec" : tactic => do
  symexecLoop 128

end Tactics

end LeanNanoLlvm.Refinement

