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
      for sg in subs do next := next.push sg.mvarId
    setGoals next.toList
  evalTactic (← `(tactic| all_goals (llvm_guard
    first
    | (simp_all; done)
    | (simp_all <;> grind; done)
    | (simp_all <;> bv_omega; done)
    | (simp_all [BitVec.slt, BitVec.sle, BitVec.lt_def, BitVec.le_def,
        BitVec.toInt_eq_toNat_cond] <;> bv_omega; done))))

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

/-- Try the standard closers on the main goal; keep the goal unchanged if none proves it. -/
private def tryClosers : TacticM Unit := do
  let s ← saveState
  let g ← getMainGoal
  let nMsgs := (← errorCount)
  try
    let g2 ← g.withContext (mkFreshExprSyntheticOpaqueMVar (← g.getType))
    setGoals [g2.mvarId!]
    -- Run the closers with synchronous kernel checking, so that a kernel failure inside one
    -- (e.g. `deep recursion` in an `omega` auxiliary lemma) is reported here, not later.
    withOptions (fun o => o.setBool `Elab.async false) <| evalTactic (← `(tactic|
      first
      | (llvm_guard grind; done)
      | (llvm_guard bv_omega; done)
      | (llvm_guard (ext _ _; simp; (try grind)); done)
      | (llvm_guard ((repeat' split) <;>
          first | (grind; done) | (bv_omega; done) | (simp_all; done)); done)
      | (llvm_guard (simp [BitVec.slt, BitVec.sle, BitVec.lt_def, BitVec.le_def,
          BitVec.toInt_eq_toNat_cond] at *; bv_omega); done)
      | (llvm_bool_cases; done)))
    if (← errorCount) != nMsgs then
      throwError "tryClosers: a closer logged an error (e.g. from the kernel)"
    closeViaAuxLemma g g2
    setGoals []
  catch _ =>
    restoreState s

/-- `llvm_refine` proves a refinement goal (`x ⊒ y`, `x ⊒[cfg] y`, `x ⊒⟨env⟩ y`) or a
    `Config.IsRefinedBy` / `RegisterValue.IsRefinedBy` goal left by `llvm_symexec`. It runs
    `llvm_intro` and `llvm_symexec` when needed, then `llvm_bv`, then tries the closers listed in
    the module documentation on every remaining leaf. Leaves it cannot prove are exactly the
    pure `BitVec` goals `llvm_bv` produces, with named poison guards. -/
elab "llvm_refine" : tactic => do
  evalTactic (← `(tactic| llvm_bv))
  let mut out := #[]
  for g in ← getGoals do
    setGoals [g]
    tryClosers
    out := out ++ (← getGoals)
  setGoals out.toList

end Tactic

end LeanNanoLlvm.Refinement
