import Lean
import LeanNanoLlvm.Refinement.PoisonElim

/-!
# Refinement Tactics: the Pipeline and `llvm_refine`

Proof files import this module. It provides `llvm_refine` and re-exports every layer below it.

| Layer          | Module       | Turns                                    | into                                |
|----------------|--------------|------------------------------------------|-------------------------------------|
| `llvm_intro`   | `Symexec`    | `x ⊒ y` (also `⊒[cfg]`, `⊒⟨env⟩`)         | `Config.IsRefinedBy` on entry states |
| `llvm_symexec` | `Symexec`    | `Config.IsRefinedBy`                     | `RegisterValue.IsRefinedBy` of the returned values |
| `llvm_bv`      | `PoisonElim` | `RegisterValue.IsRefinedBy`              | pure `BitVec` / `Bool` / `IEEEFloat` goals with named guards |
| `llvm_refine`  | `Tactic`     | `x ⊒ y`                                  | whatever `llvm_bv` leaves, minus what the closers prove |

`llvm_disprove` (module `Disprove`, imported separately) refutes a refinement with a concrete
counterexample and is independent of this pipeline.

## Which tactic to use

* Start every refinement proof with `llvm_refine`. If it closes the goal, you are done.
* If goals remain, they are exactly the goals `llvm_bv` produces: `BitVec` statements over the
  arguments `arg0`, `arg1`, ..., with the poison guards they depend on as hypotheses `h`, `h_1`,
  .... Prove them with ordinary `BitVec` reasoning (`bv_decide` is not used in this project).
* Use `llvm_intro; llvm_symexec` by hand only when symbolic execution needs help, e.g. to
  case-split a branch condition that `llvm_symexec` cannot decide. Then finish each case with
  `llvm_refine` again: it accepts `Config.IsRefinedBy` and `RegisterValue.IsRefinedBy` goals too.
* Use `llvm_bv` directly when you do not want the closers to run (for instance, to inspect the
  goals or to keep a proof fast).
* Use `llvm_refine?` to see the proof `llvm_refine` found. Like `simp?` and `llvm_disprove?`, it
  emits a `Try this:` suggestion: `llvm_bv` followed by one bullet per leaf, in the order
  `llvm_bv` produces them, with the closer that proved the leaf, or `sorry` for a leaf left open.
  The suggested script skips the closer search, so it is also faster to re-check.
* Use `llvm_refine??` to see the complete proof: the suggestion expands `llvm_intro`,
  `llvm_symexec`, `llvm_bv` and `llvm_bool_cases` into the individual steps they took (each
  symbolic step, every `PoisonOr`, branch, guard and Bool case split as a group of bullets, the
  `simp` calls, and the closer of every leaf). The script replays on its own. It is long (tens to
  hundreds of lines), so it is meant for reading and debugging rather than for committing.
  Two helper tactics appear in it: `llvm_simp_after_step` (the simplification after each
  symbolic step) and `llvm_poison_simp` (the poison-elimination `simp` pass).

## Closers

`llvm_refine` tries, on each leaf and with runtime exceptions caught (`llvm_guard`):

1. `grind`, `bv_omega`, and `ext _ _; simp; grind`;
2. splitting every remaining `if`, then `grind` / `bv_omega` / `simp_all`;
3. signed and unsigned comparisons rewritten to `toNat` arithmetic, then `bv_omega`;
4. `llvm_bool_cases`: a case split on up to three Bool atoms of the goal (comparisons,
   `decide p`, overflow flags, `==` on bit vectors), closing every case with `simp_all` and the
   arithmetic closers.

A leaf none of them proves is left open, unchanged.
-/

namespace LeanNanoLlvm.Refinement

section Tactic

open Lean Meta Elab Tactic

/-- Is `t` a Bool atom: a non-literal `Bool` term over free variables that is not itself built
    from the Bool connectives (`&&`, `||`, `!`, `xor`)? Comparisons, `decide p`, overflow flags,
    `==` / `!=` on bit vectors and Bool variables are atoms. -/
private def isBoolAtom (t : Expr) : MetaM Bool := do
  if !t.hasFVar || t.hasLooseBVars || t.hasMVar then return false
  if t.isConstOf ``true || t.isConstOf ``false then return false
  if t.isAppOf ``and || t.isAppOf ``or || t.isAppOf ``not || t.isAppOf ``Bool.xor then
    return false
  try return (← whnfR (← inferType t)).isConstOf ``Bool catch _ => return false

/-- Up to `max` distinct Bool atoms of the main goal's target and Prop hypotheses. -/
private def boolAtoms (max : Nat) : TacticM (Array Expr) := withMainContext do
  let mut exprs := #[← instantiateMVars (← getMainTarget)]
  for d in ← getLCtx do
    if !d.isImplementationDetail && (← isProp d.type) then
      exprs := exprs.push (← instantiateMVars d.type)
  let atoms ← IO.mkRef (#[] : Array Expr)
  for e in exprs do
    forEachExpr e fun t => do
      let cur ← atoms.get
      if cur.size < max && !cur.contains t && (← isBoolAtom t) then atoms.set (cur.push t)
  atoms.get

/-- Parse tactic source text. Positions in the parsed text are relative to `src`; they are
    replaced with synthetic positions at the current tactic, so that messages (e.g. linter
    warnings) are not misplaced. -/
private def parseTactic (src : String) : TacticM (TSyntax `tactic) := do
  let info := SourceInfo.fromRef (← getRef)
  let parsed ← ofExcept (Parser.runParserCategory (← getEnv) `tactic src)
  return ⟨parsed.rewriteBottomUp (·.setInfo info)⟩

/-- The closers `llvm_bool_cases` tries on each case, in order. -/
private def boolCaseClosers : Array String := #[
  "(simp_all; done)",
  "(simp_all <;> grind; done)",
  "(simp_all <;> bv_omega; done)",
  "set_option linter.unusedSimpArgs false in (simp_all [BitVec.slt, BitVec.sle, BitVec.lt_def, \
    BitVec.le_def, BitVec.toInt_eq_toNat_cond] <;> bv_omega; done)"]

/-- `llvm_bool_cases` case-splits the main goal on up to three Bool atoms (see `isBoolAtom`),
    with the case as a hypothesis `hb : atom = true/false`, and tries to close every case with
    `simp_all`, `grind`, `bv_omega`, or `toInt` arithmetic. It fails unless all cases close. -/
elab "llvm_bool_cases" : tactic => do
  let atoms ← boolAtoms 3
  if atoms.isEmpty then throwError "llvm_bool_cases: no Bool atoms"
  for a in atoms do
    let mut next := #[]
    for g in ← getGoals do
      let nm := (← g.getDecl).lctx.getUnusedName `hb
      let (fvs, g') ← g.generalize #[{ expr := a, xName? := `b, hName? := nm }]
      let subs ← g'.cases fvs[0]!
      recordStep g (subs.toList.map (·.mvarId)) s!"cases {nm} : {← g.withContext (ppExpr a)}"
      for sg in subs do next := next.push sg.mvarId
    setGoals next.toList
  for g in ← getGoals do
    setGoals [g]
    let mut closed := false
    for src in boolCaseClosers do
      let c ← parseTactic src
      try
        evalStep (← `(tactic| llvm_guard $c:tactic)) (display? := some src)
        closed := true
        break
      catch _ => pure ()
    if !closed then throwError "llvm_bool_cases: a case is left open"
  setGoals []

/-- The number of errors in the message log. -/
private def errorCount : CoreM Nat :=
  return (← Core.getMessageLog).toList.filter (·.severity == .error) |>.length

/-- Close `g` with the proof `pf` through an auxiliary lemma that the kernel checks right away.
    Closers such as `bv_omega` can build terms that elaborate but that the kernel then rejects
    (e.g. `deep recursion` on large literals). Checking each leaf here turns that into an
    ordinary, catchable failure instead of an error once the whole theorem is checked. -/
private def closeViaAuxLemma (g : MVarId) (pf : Expr) : TacticM Unit := g.withContext do
  let pf ← instantiateMVars pf
  let ty ← instantiateMVars (← g.getType)
  if pf.hasMVar || ty.hasMVar then throwError "closeViaAuxLemma: unassigned metavariables"
  let nMsgs := (← errorCount)
  let e ← withOptions (fun o => o.setBool `Elab.async false) (mkAuxTheorem ty pf (zetaDelta := true))
  -- A synchronous kernel failure is logged (and the lemma added as an axiom), not thrown.
  if (← errorCount) != nMsgs then
    throwError "closeViaAuxLemma: the kernel rejected the proof"
  g.assign e

/-- The closers `llvm_refine` tries on each leaf, in order (see the module documentation). They
    are kept as source text so that `llvm_refine?` can print them exactly as written. -/
private def closers : Array String := #[
  "grind",
  "bv_omega",
  "(ext _ _; simp; (try grind))",
  "((repeat' split) <;> first | (grind; done) | (bv_omega; done) | (simp_all; done))",
  "set_option linter.unusedSimpArgs false in (simp [BitVec.slt, BitVec.sle, BitVec.lt_def, \
    BitVec.le_def, BitVec.toInt_eq_toNat_cond] at *; bv_omega)",
  "llvm_bool_cases"]

/-- Try the closers on the main goal. Return the first one that proves it, or `none` (with the
    goal left unchanged) if none does. -/
private def tryClosers : TacticM (Option String) := do
  let g ← getMainGoal
  for src in closers do
    let c ← parseTactic src
    let s ← saveState
    let nMsgs := (← errorCount)
    try
      let g2 ← g.withContext (mkFreshExprSyntheticOpaqueMVar (← g.getType))
      setGoals [g2.mvarId!]
      -- Run the closer with synchronous kernel checking, so that a kernel failure inside it
      -- (e.g. `deep recursion` in an `omega` auxiliary lemma) is reported here, not later.
      withOptions (fun o => o.setBool `Elab.async false) <|
        evalTactic (← `(tactic| llvm_guard ($c:tactic; done)))
      if (← errorCount) != nMsgs then
        throwError "tryClosers: a closer logged an error (e.g. from the kernel)"
      -- For `llvm_refine??`: `llvm_bool_cases` records its own steps on `g2`; record any other
      -- closer as one step. `g` itself is replaced by `g2` without a visible step.
      if src != "llvm_bool_cases" then recordStep g2.mvarId! [] src
      recordStep g [g2.mvarId!] ""
      closeViaAuxLemma g g2
      setGoals []
      return some src
    catch _ =>
      restoreState s
  return none

/-- Run `llvm_bv`, then the closers on every leaf. Return, for each leaf `llvm_bv` produced (in
    order), the closer that proved it, or `none` if the leaf is left open. -/
private def runRefine : TacticM (Array (Option String)) := do
  evalTactic (← `(tactic| llvm_bv))
  let mut out := #[]
  let mut used := #[]
  for g in ← getGoals do
    setGoals [g]
    used := used.push (← tryClosers)
    out := out ++ (← getGoals)
  setGoals out.toList
  return used

/-- `llvm_refine` proves a refinement goal (`x ⊒ y`, `x ⊒[cfg] y`, `x ⊒⟨env⟩ y`) or a
    `Config.IsRefinedBy` / `RegisterValue.IsRefinedBy` goal left by `llvm_symexec`. It runs
    `llvm_intro` and `llvm_symexec` when needed, then `llvm_bv`, then tries the closers listed in
    the module documentation on every remaining leaf. Leaves it cannot prove are exactly the
    pure `BitVec` goals `llvm_bv` produces, with named poison guards. -/
elab "llvm_refine" : tactic => do
  discard runRefine

/-- `llvm_refine?` behaves like `llvm_refine` and also emits a `Try this:` suggestion (like
    `simp?`) with the proof it found: `llvm_bv` followed by one bullet per leaf, naming the
    closer that proved it. A leaf no closer proves gets `· sorry`, to be replaced by a manual
    proof. The suggested script skips the closer search, so it elaborates faster. -/
elab tk:"llvm_refine?" : tactic => do
  let used ← runRefine
  let mut lines := #["llvm_bv"]
  for c? in used do
    match c? with
    | some c => lines := lines.push s!"· {c}"
    | none => lines := lines.push "· sorry"
  let nOpen := (used.filter Option.isNone).size
  let header := if nOpen == 0 then "Try this:" else
    s!"{nOpen} leaf goal(s) left open, marked `sorry`.\nTry this:"
  let sugg := if used.isEmpty then "llvm_bv" else "\n".intercalate lines.toList
  Lean.Meta.Tactic.TryThis.addSuggestion tk { suggestion := .string sugg }
    (origSpan? := some (← getRef)) (header := header)

/-- One recorded step (see `recordStep`): `text` turned goal `goal` into the goals `outs`. -/
private structure StepRecord where
  goal : Name
  outs : List Name
  text : String

/-- Remove the step records from the message log and return them, in order. -/
private def takeStepRecords : CoreM (Array StepRecord) := do
  let log ← Core.getMessageLog
  let isRec (m : Message) := m.data.hasTag (· == scriptTag)
  let mut recs := #[]
  for m in log.unreported.toArray do
    if isRec m then
      match (← m.data.toString).splitOn "\x1f" with
      | [g, outs, text] =>
        let outs := if outs.isEmpty then [] else (outs.splitOn ",").map String.toName
        recs := recs.push { goal := g.toName, outs, text }
      | _ => pure ()
  Core.setMessageLog
    { log with unreported := (log.unreported.toArray.filter (!isRec ·)).toPArray' }
  return recs

/-- Indent the continuation lines of a (possibly multi-line) tactic. -/
private def indentText (text ind : String) : String :=
  ("\n" ++ ind ++ "    ").intercalate (text.splitOn "\n")

/-- Render the script for goal `g`, starting at its `i`-th record, at indentation `ind`.
    A goal with no further records is a leaf left open, rendered as `sorry`. `seen` collects the
    goals rendered, so that unreachable records can be reported. -/
private def renderGoal (m : Std.HashMap Name (Array StepRecord)) (skip : NameSet) :
    Nat → Name → Nat → String → StateM (Array Name) (Array String)
  | 0, _, _, ind => return #[ind ++ "sorry"]
  | fuel + 1, g, i, ind => do
    if i == 0 then modify (·.push g)
    let rs := m.getD g #[]
    let some r := rs[i]? | return #[ind ++ "sorry"]
    let pre := if r.text.isEmpty then #[] else #[ind ++ indentText r.text ind]
    -- Goals solved by unification while proving another goal get no case of their own.
    match r.outs.filter (!skip.contains ·) with
    | [] => return pre
    | [o] =>
      if o == g then return pre ++ (← renderGoal m skip fuel g (i + 1) ind)
      else return pre ++ (← renderGoal m skip fuel o 0 ind)
    | os => do
      let mut acc := pre
      for o in os do
        let sub ← renderGoal m skip fuel o 0 (ind ++ "  ")
        -- Turn the first line of the case into a bullet.
        match sub.toList with
        | [] => acc := acc.push (ind ++ "· skip")
        | l :: ls => acc := acc.push (ind ++ "· " ++ l.drop (ind.length + 2)) ++ ls.toArray
      return acc

/-- `llvm_refine??` behaves like `llvm_refine` and emits a `Try this:` suggestion with the
    complete proof it found, with `llvm_intro`, `llvm_symexec`, `llvm_bv` and `llvm_bool_cases`
    expanded into the individual steps they took: the symbolic-execution steps, the
    `PoisonOr` and branch case splits, the guard splits, the `simp` calls, and the closer of
    every leaf. Every case split becomes a group of bullets. A leaf left open is `sorry`. -/
elab tk:"llvm_refine??" : tactic => do
  let root ← getMainGoal
  let s ← saveState
  try
    withOptions (fun o => o.setBool `llvm.recordScript true) (discard runRefine)
  catch e =>
    restoreState s
    throw e
  let recs ← takeStepRecords
  let mut m : Std.HashMap Name (Array StepRecord) := {}
  for r in recs do
    m := m.insert r.goal ((m.getD r.goal #[]).push r)
  -- A produced goal that has no step of its own but is assigned was solved by unification.
  let mut skip : NameSet := {}
  for r in recs do
    for o in r.outs do
      if !m.contains o && (← MVarId.isAssigned ⟨o⟩) then skip := skip.insert o
  let (lines, seen) := (renderGoal m skip (recs.size + 1) root.name 0 "").run #[]
  let unreached := (recs.filter (!seen.contains ·.goal)).size
  let nOpen := (lines.filter (·.trimLeft.endsWith "sorry")).size
  let mut header := ""
  if nOpen > 0 then header := header ++ s!"{nOpen} leaf goal(s) left open, marked `sorry`.\n"
  if unreached > 0 then
    header := header ++ s!"Warning: {unreached} recorded step(s) could not be placed in the \
      script; it may not replay.\n"
  -- The recorded `simp` calls use fixed lemma lists, so the unused-argument linter would flag
  -- many of them in the pasted script.
  let script := "set_option linter.unusedSimpArgs false in\n" ++
    "\n".intercalate (lines.toList.map ("  " ++ ·))
  Lean.Meta.Tactic.TryThis.addSuggestion tk { suggestion := .string script }
    (origSpan? := some (← getRef)) (header := header ++ "Try this:")

end Tactic

end LeanNanoLlvm.Refinement
