import Lean
import LeanNanoLlvm.Refinement.Lemmas

/-!
# Refinement Automation Tactics (`llvm_intro`, `llvm_symexec`, `llvm_vc`, `llvm_refine`)

Kernel-pure, general-purpose automation for LLVM behavioral refinement proofs
(`x ⊒ y`, `x ⊒[cfg] y`, `x ⊒⟨env⟩ y`). All tactics produce standard Lean kernel proof terms
using only `{propext, Classical.choice, Quot.sound}` (no `bv_decide`, `native_decide`, or
`Lean.ofReduceBool`).

## Tactic Pipeline
1. `llvm_intro`   — Unpacks `Definition.IsRefinedBy*`, checks signature compatibility, introduces
                    `initMem` and `args`, destructures `args` for any arity `0..N`, and reduces
                    `initCallConfig` on both source and target to `.running` states.
2. `llvm_symexec` — Dispatches on the head AST constructor of the current instruction/terminator
                    to symbolically execute source and target (`intBinaryOp`, `icmp`, `select`,
                    `conversionOp`, `floatUnaryOp`, `freeze`, `br`, `condBr`, `switch`, `phi`,
                    `ret`, `retVoid`, `unreachable`), short-circuiting on source `.ub` / `CanAbort`
                    and reducing `.halted` vs `.halted` to `RegisterValue.IsRefinedBy .id retX retY`.
3. `llvm_vc`      — Extracts clean, pure Lean verification conditions (`BitVec` / `Bool` / `Float`)
                    by splitting `PoisonOr` cases (auto-closing `.poison ⊒ _`), unfolding pure LLVM
                    evaluators and flag guards, and closing trivial reflexive/contradictory branches.
4. `llvm_refine`  — Composes `llvm_intro; llvm_symexec; llvm_vc` and attempts standard Lean
                    closers (`rfl`, `trivial`, `contradiction`, `grind`, `bv_omega`,
                    `ext _ _; simp; grind`); any remaining pure VC is left exposed for an explicit
                    Lean proof.

The `simp_llvm` / `simp_step` lemmas these tactics rely on live in
`LeanNanoLlvm.Refinement.Lemmas`.
-/

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

/-! ### Composable Refinement Tactics (`llvm_intro`, `llvm_symexec`, `llvm_vc`, `llvm_refine`) -/

section Tactics

open Lean Meta Elab Tactic

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
        evalTactic (← `(tactic|
          rcases $hargsId:ident with ⟨_, _, h_eq_args, ⟨$argId:ident, h_eq_val⟩, $hargsId:ident⟩;
          subst h_eq_val; subst h_eq_args))
        pure true
      catch _ =>
        try
          evalTactic (← `(tactic| subst $hargsId:ident))
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
  evalTactic (← `(tactic|
    dsimp only [HRefinement.IsRefinedBy, Refinement.IsRefinedBy, instHRefinementOfRefinement,
      Definition.IsRefinedBy, Definition.IsRefinedByWith, Definition.IsRefinedByIn]))
  evalTactic (← `(tactic| refine ⟨rfl, ?_⟩))
  let initMemId := mkIdent `initMem
  let argsId := mkIdent `args
  let hwfMemId := mkIdent `hwfMem
  let hargsId := mkIdent `hargs
  evalTactic (← `(tactic| intro $initMemId:ident $argsId:ident $hwfMemId:ident $hargsId:ident))
  for nm in defNames do
    let id := mkIdent nm
    try evalTactic (← `(tactic| dsimp only [$id:ident] at $hargsId:ident ⊢)) catch _ => pure ()
  evalTactic (← `(tactic|
    simp only [Semantics.Definition.ArgValuesWellFormed,
      RegisterValue.wellFormedForList_cons_iff, RegisterValue.wellFormedForList_nil_iff,
      RegisterValue.wellFormedFor_int_iff, RegisterValue.wellFormedFor_float_iff,
      RegisterValue.wellFormedFor_ptr_iff] at $hargsId:ident))
  destructArgHyps 32 0 hargsId
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
      evalTactic (← `(tactic| exact fun _ => EvalPhis.nil_iff))
    catch _ =>
      restoreState s
      evalTactic (← `(tactic| intro res_phi; apply EvalPhis.cons_leaf_iff))
      evalTactic (← `(tactic| (simp [List.find?, -Prod.mk.injEq, -Option.some.injEq]; rfl)))
      evalTactic (← `(tactic| ((try llvm_step); rfl)))
      solveEvalPhis fuel

/-- Simplify a `Config.IsRefinedBy` goal immediately after taking a symbolic step. -/
private def simpAfterStep : TacticM Unit := do
  try
    evalTactic (← `(tactic|
      (try simp only [liftBinaryPure_bv, evalIntBinaryScalarPure, evalDivRemUB_ite_poison]);
      simp only [finishRegInstr, finishVoidInstr, CallFrame.advance, CallFrame.jumpTo,
        MachineState.withFrames, MachineState.withFramesAndMemory,
        commitPhiUpdates, freeAllocaList,
        applyRetFMFAndAttrsPure, applyValueAttrsPure,
        liftBinaryPure_bv, evalIntBinaryScalarPure, evalICmpScalarPure_bv,
        evalSelectPure_bv, evalSelectPure_float, evalSelectPure_ptr,
        evalConversionExec_trunc, evalConversionExec_zext, evalConversionExec_sext,
        evalFloatUnaryExec_fneg_no_nsz, evalDivRemUB_ite_poison, evalDivRemUB, ite_except_ok, RegisterValue.poisonOf,
        bitvec_ofInt_ofNat, bitvec_ofInt_neg, bitvec_ofInt_negSucc,
        BitVec.ofNat_eq_ofNat,
        AST.LlvmType.scalarType, AST.FastMathFlags.any,
        Bool.or_self, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte,
        beq_self_eq_true, Config.ofError]))
  catch _ => pure ()

/-- Step the source (`cX`) side based on its O(1)-inspected `NextAction`. -/
private def stepSourceAction (act : NextAction) : TacticM Bool := do
  match act with
  | .ub =>
    try evalTactic (← `(tactic| exact Config.IsRefinedBy.of_ub_left)); return true
    catch _ => return false
  | .instr nm =>
    if nm == ``AST.Instruction.intBinaryOp then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_step_left
            ((Step.intBinaryOp_leaf_iff rfl rfl (by llvm_step; rfl) (by llvm_step; rfl) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.icmp then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_step_left
            ((Step.icmp_leaf_iff rfl rfl (by llvm_step; rfl) (by llvm_step; rfl) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.select then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_step_left
            ((Step.select_leaf_iff rfl rfl (by llvm_step; rfl) (by llvm_step; rfl) (by llvm_step; rfl) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.conversionOp then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_step_left
            ((Step.conversionOp_leaf_iff rfl rfl (by llvm_step; rfl) (fun _ => rfl) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.floatUnaryOp then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_step_left
            ((Step.floatUnaryOp_leaf_iff rfl rfl (by llvm_step; rfl)
              (fun o => evalFloatUnaryExec_fneg_no_nsz _ rfl _ (by decide) _ o) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.freeze then
      let s ← saveState
      try
        evalTactic (← `(tactic| apply Config.IsRefinedBy.of_step_left))
        evalTactic (← `(tactic| apply Step.freeze_bv_val rfl rfl))
        focus (evalTactic (← `(tactic| (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done)))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else return false
  | .term nm =>
    if nm == ``AST.Terminator.unreachable then
      let s ← saveState
      try evalTactic (← `(tactic| exact Config.IsRefinedBy.of_unreachable_left rfl rfl rfl)); return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.ret then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_step_left
            ((Step.ret_top_leaf_iff rfl rfl rfl rfl (by llvm_step; rfl) none _).mpr ⟨rfl, rfl⟩) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.retVoid then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_step_left
            ((Step.retVoid_top_iff rfl rfl rfl rfl none _).mpr ⟨rfl, rfl⟩) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.br then
      let s ← saveState
      try
        evalTactic (← `(tactic| apply Config.IsRefinedBy.of_step_left))
        evalTactic (← `(tactic| apply Step.br_det rfl rfl rfl))
        evalTactic (← `(tactic| (simp [AST.Definition.findBlock?]; rfl)))
        evalTactic (← `(tactic| (simp only [splitPhis]; rfl)))
        solveEvalPhis 16; simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.condBr then
      let s ← saveState
      let isPoison ←
        try
          evalTactic (← `(tactic|
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
        evalTactic (← `(tactic| apply Config.IsRefinedBy.of_step_left))
        evalTactic (← `(tactic| apply Step.condBr_val_det rfl rfl rfl))
        evalTactic (← `(tactic| (llvm_step; rfl)))
        evalTactic (← `(tactic| (simp [AST.Definition.findBlock?]; rfl)))
        evalTactic (← `(tactic| (simp only [splitPhis]; rfl)))
        solveEvalPhis 16; simpAfterStep; return true
      catch _ =>
        restoreState s2
        return false
    else if nm == ``AST.Terminator.switch then
      let s ← saveState
      let isPoison ←
        try
          evalTactic (← `(tactic|
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
        evalTactic (← `(tactic| apply Config.IsRefinedBy.of_step_left))
        evalTactic (← `(tactic| apply Step.switch_val_det rfl rfl rfl))
        focus (evalTactic (← `(tactic| (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done)))
        evalTactic (← `(tactic| (simp [AST.Definition.findBlock?, List.find?, bitvec_ofInt_ofNat, bitvec_ofInt_negSucc]; rfl)))
        evalTactic (← `(tactic| (simp only [splitPhis]; rfl)))
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
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_det_step_right
            (Step.intBinaryOp_leaf_iff rfl rfl (by llvm_step; rfl) (by llvm_step; rfl)) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.icmp then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_det_step_right
            (Step.icmp_leaf_iff rfl rfl (by llvm_step; rfl) (by llvm_step; rfl)) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.select then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_det_step_right
            (Step.select_leaf_iff rfl rfl (by llvm_step; rfl) (by llvm_step; rfl) (by llvm_step; rfl)) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.conversionOp then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_det_step_right
            (Step.conversionOp_leaf_iff rfl rfl (by llvm_step; rfl) (fun _ => rfl)) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.floatUnaryOp then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_det_step_right
            (Step.floatUnaryOp_leaf_iff rfl rfl (by llvm_step; rfl)
              (fun o => evalFloatUnaryExec_fneg_no_nsz _ rfl _ (by decide) _ o)) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Instruction.freeze then
      let s ← saveState
      try
        evalTactic (← `(tactic| apply Config.IsRefinedBy.of_det_step_right))
        evalTactic (← `(tactic| apply Step.freeze_bv_val_iff rfl rfl))
        focus (evalTactic (← `(tactic| (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done)))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else return false
  | .term nm =>
    if nm == ``AST.Terminator.ret then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_det_step_right
            (Step.ret_top_leaf_iff rfl rfl rfl rfl (by llvm_step; rfl)) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.retVoid then
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine Config.IsRefinedBy.of_det_step_right
            (Step.retVoid_top_iff rfl rfl rfl rfl) ?_))
        simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.br then
      let s ← saveState
      try
        evalTactic (← `(tactic| apply Config.IsRefinedBy.of_det_step_right))
        evalTactic (← `(tactic| apply Step.br_det_iff rfl rfl rfl))
        evalTactic (← `(tactic| (simp [AST.Definition.findBlock?]; rfl)))
        evalTactic (← `(tactic| (simp only [splitPhis]; rfl)))
        solveEvalPhis 16; simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.condBr then
      let s ← saveState
      try
        evalTactic (← `(tactic| apply Config.IsRefinedBy.of_det_step_right))
        evalTactic (← `(tactic| apply Step.condBr_val_det_iff rfl rfl rfl))
        evalTactic (← `(tactic| ((try llvm_step); rfl)))
        evalTactic (← `(tactic| (simp [AST.Definition.findBlock?]; rfl)))
        evalTactic (← `(tactic| (simp only [splitPhis]; rfl)))
        solveEvalPhis 16; simpAfterStep; return true
      catch _ => restoreState s; return false
    else if nm == ``AST.Terminator.switch then
      let s ← saveState
      try
        evalTactic (← `(tactic| apply Config.IsRefinedBy.of_det_step_right))
        evalTactic (← `(tactic| apply Step.switch_val_det_iff rfl rfl rfl))
        focus (evalTactic (← `(tactic| (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done)))
        evalTactic (← `(tactic| (simp [AST.Definition.findBlock?, List.find?, bitvec_ofInt_ofNat, bitvec_ofInt_negSucc]; rfl)))
        evalTactic (← `(tactic| (simp only [splitPhis]; rfl)))
        solveEvalPhis 16; simpAfterStep; return true
      catch _ => restoreState s; return false
    else return false
  | _ => return false

/-- Try to finish a halted-vs-halted goal. -/
private def tryFinishHalted : TacticM Bool := do
  let s ← saveState
  try
    evalTactic (← `(tactic| apply Config.IsRefinedBy.of_halted_same_mem))
    return true
  catch _ =>
    restoreState s
    let s2 ← saveState
    try
      evalTactic (← `(tactic| apply Config.IsRefinedBy.of_halted))
      return true
    catch _ =>
      restoreState s2
      return false

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
    evalTactic (← `(tactic| cases $id:ident using PoisonOr.casesOn'))
    let gs ← getGoals
    let mut out : List MVarId := []
    for g in gs do
      setGoals [g]
      try evalTactic (← `(tactic| llvm_simp)) catch _ => pure ()
      simpAfterStep
      out := out ++ (← getGoals)
    setGoals out
    return true
  return false

private theorem bitvec1_eq_zero_or_one (b : BitVec 1) : b = 0#1 ∨ b = 1#1 := by
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
      evalTactic (← `(tactic|
        rcases bitvec1_eq_zero_or_one $id:ident with h_bv1_eq | h_bv1_eq <;> subst h_bv1_eq))
      let gs ← getGoals
      let mut out : List MVarId := []
      for g in gs do
        setGoals [g]
        try evalTactic (← `(tactic| llvm_simp)) catch _ => pure ()
        simpAfterStep
        out := out ++ (← getGoals)
      setGoals out
      return true
    catch _ =>
      restoreState s
      return false
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
        evalTactic (← `(tactic| apply Config.IsRefinedBy.of_freeze_poison_right rfl rfl))
        focus (evalTactic (← `(tactic| (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done)))
        evalTactic (← `(tactic| intro $bId:ident $hmId:ident))
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
        evalTactic (← `(tactic| apply Config.IsRefinedBy.of_step_left))
        evalTactic (← `(tactic| refine Step.freeze_bv_poison_step rfl rfl ?_ $bId:ident $hmId:ident))
        focus (evalTactic (← `(tactic| (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done)))
        simpAfterStep
        return true
      catch _ =>
        restoreState s1
        let s2 ← saveState
        try
          evalTactic (← `(tactic| apply Config.IsRefinedBy.of_step_left))
          evalTactic (← `(tactic| apply Step.freeze_bv_poison_zero rfl rfl))
          focus (evalTactic (← `(tactic| (try simp [simp_step, -RegisterValue.bv.injEq]); (try rfl); done)))
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
                if needsSplit then
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
                            let hName := mkIdent `h_ite_sym
                            let condStx ← withMainContext (Lean.PrettyPrinter.delab condExpr)
                            evalTactic (← `(tactic| by_cases $hName:ident : $condStx))
                            let gs ← getGoals
                            let mut out : List MVarId := []
                            for sg in gs do
                              setGoals [sg]
                              try evalTactic (← `(tactic| simp only [$hName:ident, ↓reduceIte, not_false_eq_true])) catch _ => pure ()
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

/-- Split all `PoisonOr` local hypotheses (`arg0`, `arg1`, ...) so pure evaluators reduce cleanly. -/
private def splitPoisonOrHyps (fuel : Nat) : TacticM Unit := do
  match fuel with
  | 0 => return ()
  | fuel + 1 =>
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
      evalTactic (← `(tactic| cases $id:ident using PoisonOr.casesOn'))
      let subgoals ← getGoals
      let mut out : List MVarId := []
      for sg in subgoals do
        setGoals [sg]
        splitPoisonOrHyps fuel
        out := out ++ (← getGoals)
      setGoals out

/-- Close only trivial LLVM-level verification conditions (reflexivity, poison, contradiction). -/
private def closeTrivialVc : TacticM Unit := do
  let s ← saveState
  try
    evalTactic (← `(tactic|
      (try intros);
      first
      | (rfl; done)
      | (trivial; done)
      | (contradiction; done)
      | (exact RegisterValue.IsRefinedBy.refl _; done)
      | (exact RegisterValue.isRefinedBy_bv_poison; done)
      | (exact RegisterValue.isRefinedBy_float_poison; done)
      | (exact RegisterValue.isRefinedBy_ptr_poison; done)))
  catch _ =>
    restoreState s

/-- `llvm_vc` extracts clean, pure Lean verification conditions (`BitVec` / `Bool` / `Float`)
    from `RegisterValue.IsRefinedBy` goals by splitting `PoisonOr` hypotheses (auto-closing
    `.poison ⊒ _`), unfolding pure LLVM evaluators and poison guards with `simp_llvm`, splitting
    remaining `if`/`match` guards, and closing trivial reflexive/contradictory branches. -/
elab "llvm_vc" : tactic => do
  let allGoals ← getGoals
  if allGoals.isEmpty then return ()
  let mut finalRemaining : List MVarId := []
  for rootGoal in allGoals do
    setGoals [rootGoal]
    let tgt ← instantiateMVars (← getMainTarget)
    if tgt.isAppOf ``Config.IsRefinedBy then
      finalRemaining := finalRemaining ++ [rootGoal]
      continue
    -- Fast path: try closing without splitting `PoisonOr` (rollback if not closed)
    let sFast ← saveState
    let closedFast ←
      try
        evalTactic (← `(tactic|
          first
          | exact RegisterValue.IsRefinedBy.refl _
          | (llvm_simp; exact RegisterValue.IsRefinedBy.refl _)
          | (llvm_simp; rfl)))
        pure (← getGoals).isEmpty
      catch _ =>
        pure false
    if closedFast then continue
    restoreState sFast
    -- General path: lift to PoisonOr.IsRefinedBy, split PoisonOr hypotheses, unfold guards
    try evalTactic (← `(tactic|
      first
      | apply RegisterValue.isRefinedBy_bv_of_poisonOr
      | apply RegisterValue.isRefinedBy_float_of_poisonOr)) catch _ => pure ()
    splitPoisonOrHyps 8
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      try evalTactic (← `(tactic| llvm_simp)) catch _ => pure ()
      if !(← getGoals).isEmpty then
        closeTrivialVc
      let cur ← getGoals
      for cg in cur do
        setGoals [cg]
        try
          evalTactic (← `(tactic| (repeat split); all_goals (try split at *)))
          evalTactic (← `(tactic| all_goals (try simp only [PoisonOr.value, PoisonOr.mk.injEq, Option.some.injEq] at *)))
          evalTactic (← `(tactic| all_goals (try subst_vars)))
          evalTactic (← `(tactic| all_goals (repeat split)))
          evalTactic (← `(tactic| all_goals (try llvm_simp)))
        catch _ => pure ()
        let leaves ← getGoals
        for lg in leaves do
          setGoals [lg]
          closeTrivialVc
          finalRemaining := finalRemaining ++ (← getGoals)
  setGoals finalRemaining

/-- Transparent refinement tactic: runs `llvm_intro; llvm_symexec; llvm_vc` and tries standard
    Lean closers (`rfl`, `trivial`, `contradiction`, `grind`, `bv_omega`, `ext _ _; simp; grind`).
    Any remaining pure verification condition is left exposed for an explicit Lean proof. -/
macro "llvm_refine" : tactic =>
  `(tactic| (llvm_intro; llvm_symexec; llvm_vc;
             all_goals (try (first
               | (rfl; done)
               | (trivial; done)
               | (contradiction; done)
               | (grind; done)
               | (bv_omega; done)
               | (ext _ _; simp; (try grind); done)))))

end Tactics

end LeanNanoLlvm.Refinement

