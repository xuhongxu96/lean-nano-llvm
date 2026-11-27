import Lean
import LeanNanoLlvm.Refinement.Symexec

/-!
# Poison Elimination (`llvm_bv`)

The third layer of the refinement pipeline; see `LeanNanoLlvm.Refinement.Tactic`.

`llvm_bv` turns the value-refinement goals left by `llvm_symexec` into plain `BitVec` (and
`Bool` / `IEEEFloat`) goals, so that a proof only has to deal with bit-vector reasoning.

## Why plain `simp_llvm` is not enough

After symbolic execution, a returned integer is a `PoisonOr (BitVec w)` built from nested
`if guard then .poison else ...` terms (flags such as `nsw`, `nuw`, `disjoint`, `exact`) and
from `if cond then t else f` terms (`select`).

* `PoisonOr.IsRefinedBy` is deliberately not unfolded by `simp`, and `simp_llvm` only rewrites
  it when one branch of a source-side `if` is literally `.poison`. A `select` whose arms are
  both (guarded) values needs the general rule `isRefinedBy_ite_left` below.
* That `if` is often built at type `IntW w`, a plain `def` for `PoisonOr (BitVec w)`. `simp`
  matches at reducible transparency, so rules stated for `PoisonOr` do not fire on it; the
  `_intW` variants below cover it.
* Closing leaves with default-transparency `rfl` / `trivial` can raise `maximum recursion depth`
  on `BitVec` goals with large literals (e.g. `x + 4294967232#32 = x ^^^ 64#32`). That runtime
  exception escapes `try` / `first`, so this module only uses reducible closers and `llvm_guard`.

## What `llvm_bv` does

1. On a top-level refinement goal (`x ⊒ y`, `x ⊒[cfg] y`, `x ⊒⟨env⟩ y`) it first runs
   `llvm_intro; llvm_symexec`, and on a `Config.IsRefinedBy` goal it first runs `llvm_symexec`.
2. On each `RegisterValue.IsRefinedBy _ (.bv w x) (.bv w y)` (or `.float`) goal it moves to
   `PoisonOr.IsRefinedBy x y` (an equivalence, so no information is lost) and case-splits every
   `PoisonOr` argument into `.poison` and `.value argN`. The value keeps the argument's name.
3. It rewrites with `simp_llvm` plus the rules above, which turns the goal into a formula over
   `∧`, `→`, `¬` and `BitVec` (in)equalities: a source-side poison guard becomes a hypothesis
   (`¬ x.saddOverflow c = true → ...`), and a target-side poison guard becomes an obligation.
4. It introduces implications as named hypotheses (`h`, `h_1`, ...) and splits conjunctions.
   While a goal still mentions `PoisonOr.IsRefinedBy`, it case-splits the first remaining `if`
   condition into a named hypothesis (or, failing that, splits a `match`) and simplifies again.
   An `if` inside an already pure `BitVec` goal is left in place.
5. It closes leaves that are immediate (`True`, reducible `rfl`, contradictory hypotheses) and
   leaves every other leaf, which no longer mentions `PoisonOr`, to the user.

Every step is a kernel-checked rewrite or case split; no `bv_decide`, `native_decide`, or
`Lean.ofReduceBool` is used. All closers run at reducible transparency, and runtime exceptions
such as `maximum recursion depth` are caught, so `llvm_bv` never fails on a hard leaf: it leaves
the leaf open instead.
-/

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

/-! ### Rewrite rules used by `llvm_bv` (kept out of `simp_llvm`, which other tactics also use) -/

/-- A source-side `if` (e.g. from `select`) refines `y` iff each branch does under its guard. -/
theorem PoisonOr.isRefinedBy_ite_left {α : Type} {c : Prop} [Decidable c]
    {x₁ x₂ y : PoisonOr α} :
    PoisonOr.IsRefinedBy (if c then x₁ else x₂) y ↔
      (c → PoisonOr.IsRefinedBy x₁ y) ∧ (¬ c → PoisonOr.IsRefinedBy x₂ y) := by
  by_cases hc : c <;> simp [hc]

/-- `PoisonOr.isRefinedBy_ite_left` at type `IntW w`. `IntW` is a plain `def`, so `simp`
    cannot match an `if` built at `IntW w` (e.g. by `select`) against a `PoisonOr` pattern. -/
theorem PoisonOr.isRefinedBy_ite_left_intW {w : Nat} {c : Prop} [Decidable c]
    {x₁ x₂ : IntW w} {y : PoisonOr (BitVec w)} :
    PoisonOr.IsRefinedBy (α := BitVec w) (if c then x₁ else x₂ : IntW w) y ↔
      (c → PoisonOr.IsRefinedBy x₁ y) ∧ (¬ c → PoisonOr.IsRefinedBy x₂ y) :=
  PoisonOr.isRefinedBy_ite_left

/-- `PoisonOr.isRefinedBy_ite_right` at type `IntW w` (see `isRefinedBy_ite_left_intW`). -/
theorem PoisonOr.isRefinedBy_ite_right_intW {w : Nat} {c : Prop} [Decidable c]
    {x : PoisonOr (BitVec w)} {y₁ y₂ : IntW w} :
    PoisonOr.IsRefinedBy (α := BitVec w) x (if c then y₁ else y₂ : IntW w) ↔
      (c → PoisonOr.IsRefinedBy x y₁) ∧ (¬ c → PoisonOr.IsRefinedBy x y₂) :=
  PoisonOr.isRefinedBy_ite_right

/-- A defined value is never refined by poison. -/
theorem PoisonOr.isRefinedBy_value_poison {α : Type} {a : α} :
    PoisonOr.IsRefinedBy (.value a) (.poison : PoisonOr α) ↔ False := Iff.rfl

/-- `RegisterValue` refinement of integers is exactly `PoisonOr` refinement. -/
theorem RegisterValue.isRefinedBy_bv_iff_poisonOr {inj : MemoryInjection} {w : Nat}
    {x y : PoisonOr (BitVec w)} :
    RegisterValue.IsRefinedBy inj (.bv w x) (.bv w y) ↔ PoisonOr.IsRefinedBy x y := by
  refine ⟨fun h => ?_, RegisterValue.isRefinedBy_bv_of_poisonOr⟩
  cases x using PoisonOr.casesOn' <;> cases y using PoisonOr.casesOn'
  · exact trivial
  · exact trivial
  · exact h
  · exact h.2

/-- `RegisterValue` refinement of floats is exactly `PoisonOr` refinement. -/
theorem RegisterValue.isRefinedBy_float_iff_poisonOr {inj : MemoryInjection} {ft : AST.FloatType}
    {x y : FloatW ft} :
    RegisterValue.IsRefinedBy inj (.float ft x) (.float ft y) ↔ PoisonOr.IsRefinedBy x y := by
  refine ⟨fun h => ?_, RegisterValue.isRefinedBy_float_of_poisonOr⟩
  cases x using PoisonOr.casesOn' <;> cases y using PoisonOr.casesOn'
  · exact trivial
  · exact trivial
  · exact h
  · exact h.2

section Tactic

open Lean Meta Elab Tactic

/-- Run `x`; on any failure, including runtime exceptions such as `maximum recursion depth`,
    restore the state and return `false`. -/
private def tryRt (x : TacticM Unit) : TacticM Bool := do
  let s ← saveState
  tryCatchRuntimeEx (do x; pure true) (fun _ => do restoreState s; pure false)

/-- Run a tactic on the main goal; report whether it closed it. -/
private def closesWith (stx : TacticM Syntax) : TacticM Bool := do
  let s ← saveState
  let ok ← tryRt (do evalStep (← stx); if !(← getGoals).isEmpty then throwError "open")
  if !ok then restoreState s
  return ok

/-- Is the target a top-level definition refinement goal? -/
private def isDefinitionRefinement (tgt : Expr) : Bool :=
  tgt.isAppOf ``HRefinement.IsRefinedBy || tgt.isAppOf ``Definition.IsRefinedBy ||
    tgt.isAppOf ``Definition.IsRefinedByWith || tgt.isAppOf ``Definition.IsRefinedByIn

/-- Name of the first local whose type is `PoisonOr _`, `IntW _`, or `FloatW _`. -/
private def findPoisonOrLocal : TacticM (Option Name) := withMainContext do
  for decl in ← getLCtx do
    if !decl.isImplementationDetail then
      let ty ← instantiateMVars decl.type
      if ty.isAppOf ``PoisonOr || ty.isAppOf ``IntW || ty.isAppOf ``FloatW then
        return some decl.userName
  return none

/-- Case-split every `PoisonOr` local into `.poison` / `.value`, keeping the local's name for
    the value. -/
private def splitPoisonLocals : Nat → TacticM Unit
  | 0 => return
  | fuel + 1 => do
  let some nm ← findPoisonOrLocal | return
  let id := mkIdent nm
  evalStep (← `(tactic| cases $id:ident using PoisonOr.casesOn'))
  let mut gs ← getGoals
  -- `casesOn'` yields `[poison, value]`; give the value the argument's name.
  if let [gp, gv] := gs then
    setGoals [gv]
    discard <| tryRt (evalStep (← `(tactic| rename_i $id:ident)))
    gs := gp :: (← getGoals)
  let mut out := #[]
  for g in gs do
    setGoals [g]
    splitPoisonLocals fuel
    out := out ++ (← getGoals)
  setGoals out.toList

/-- `llvm_poison_simp` is one `simp` pass with `simp_llvm` and the poison-elimination rules. -/
macro "llvm_poison_simp" : tactic => `(tactic|
    simp (config := { contextual := true })
      [simp_llvm, PoisonOr.isRefinedBy_ite_left, PoisonOr.isRefinedBy_ite_left_intW,
       PoisonOr.isRefinedBy_ite_right_intW, PoisonOr.isRefinedBy_value_poison, handleFMF])

/-- One `simp` pass with `simp_llvm` and the poison-elimination rules. -/
private def poisonSimp : TacticM Unit := do
  discard <| tryRt (evalStep (← `(tactic| llvm_poison_simp)))

/-- Close the main goal if it is immediate, using only cheap, reducible-transparency closers. -/
private def closeImmediate : TacticM Bool := do
  closesWith `(tactic|
    first
    | exact trivial
    | with_reducible rfl
    | with_reducible contradiction
    | with_reducible assumption)

/-- Does `e` still mention `PoisonOr.IsRefinedBy`? Pure leaves (which may contain ordinary
    `BitVec` `if`s) are left alone. -/
private def hasPoisonStructure (e : Expr) : Bool :=
  (e.find? (·.isAppOf ``PoisonOr.IsRefinedBy)).isSome

/-- The condition of the first `if` / `dite` in `e` whose condition does not mention bound
    variables (so it can be case-split in the current context). -/
private def findClosedIteCond (e : Expr) : Option Expr :=
  (e.find? fun t =>
    (t.isAppOfArity ``ite 5 || t.isAppOfArity ``dite 5) && !(t.getArg! 1).hasLooseBVars)
    |>.map (·.getArg! 1)

/-- Introduce one hypothesis with a fresh `h`-name, or split one conjunction. -/
private def decomposeStep : TacticM Bool := withMainContext do
  let tgt ← whnfR (← instantiateMVars (← getMainTarget))
  if tgt.isAppOf ``And then
    evalStep (← `(tactic| apply And.intro))
    return true
  if tgt.isArrow && !tgt.isAppOf ``Not then
    let nm := (← getLCtx).getUnusedName `h
    let id := mkIdent nm
    evalStep (← `(tactic| intro $id:ident))
    return true
  return false

/-- Decompose, split, and simplify one goal until only pure leaves remain. -/
private def reduceGoal : Nat → TacticM (List MVarId)
  | 0 => getGoals
  | fuel + 1 => do
  if ← closeImmediate then return []
  if ← decomposeStep then
    let gs ← getGoals
    let mut out := #[]
    for g in gs do
      setGoals [g]
      out := out ++ (← reduceGoal fuel)
    return out.toList
  let tgt ← instantiateMVars (← getMainTarget)
  if !hasPoisonStructure tgt then return [← getMainGoal]
  -- Prefer splitting an `if` (a flag guard or a `select` condition): once its condition is a
  -- hypothesis, `simp` reduces any `match` whose scrutinee depended on it.
  if let some c := findClosedIteCond tgt then
    let s ← saveState
    let g ← getMainGoal
    let nm := (← g.getDecl).lctx.getUnusedName `h
    let hId := mkIdent nm
    let ok ← tryRt do
      let (gt, gf) ← g.byCases c nm
      recordStep g [gt.mvarId, gf.mvarId] s!"by_cases {nm} : {← g.withContext (ppExpr c)}"
      setGoals [gt.mvarId, gf.mvarId]
    if ok then
      let gs ← getGoals
      let mut out := #[]
      for g in gs do
        setGoals [g]
        discard <| tryRt (evalStep (← `(tactic| simp only [$hId:ident, ↓reduceIte, ↓reduceDIte])))
        if (← getGoals).isEmpty then continue
        poisonSimp
        if (← getGoals).isEmpty then continue
        out := out ++ (← reduceGoal fuel)
      return out.toList
    restoreState s
  -- Otherwise split a remaining `match`.
  let s ← saveState
  if ← tryRt (evalStep (← `(tactic| split))) then
    let gs ← getGoals
    let mut out := #[]
    for g in gs do
      setGoals [g]
      poisonSimp
      if (← getGoals).isEmpty then continue
      out := out ++ (← reduceGoal fuel)
    return out.toList
  restoreState s
  return [← getMainGoal]

/-- Reduce one value-refinement goal to pure leaves. -/
private def reduceValueGoal : TacticM (List MVarId) := do
  -- Fast path: source and target already agree (also covers `ptr`, `void` and vector values).
  if ← closesWith `(tactic|
      first
      | exact RegisterValue.IsRefinedBy.refl _
      | (llvm_simp; exact RegisterValue.IsRefinedBy.refl _)) then
    return []
  discard <| tryRt (evalStep (← `(tactic|
    first
    | rw [RegisterValue.isRefinedBy_bv_iff_poisonOr]
    | rw [RegisterValue.isRefinedBy_float_iff_poisonOr])))
  splitPoisonLocals 32
  let gs ← getGoals
  let mut out := #[]
  for g in gs do
    setGoals [g]
    poisonSimp
    if (← getGoals).isEmpty then continue
    out := out ++ (← reduceGoal 256)
  return out.toList

/-- `llvm_bv` eliminates poison and `select` case structure from refinement goals and leaves
    only pure `BitVec` / `Bool` / `IEEEFloat` goals. On a top-level refinement goal it first runs
    `llvm_intro; llvm_symexec` (on a `Config.IsRefinedBy` goal, `llvm_symexec`). Leaves that are immediate are closed; every other leaf is left
    open, with the poison guards it depends on as named hypotheses (`h`, `h_1`, ...). Goals that
    symbolic execution could not finish (`Config.IsRefinedBy`) are left unchanged. -/
elab "llvm_bv" : tactic => do
  let mut out := #[]
  for g in ← getGoals do
    setGoals [g]
    let tgt ← instantiateMVars (← getMainTarget)
    if isDefinitionRefinement tgt.cleanupAnnotations then
      evalTactic (← `(tactic| llvm_intro; llvm_symexec))
    else if tgt.isAppOf ``Config.IsRefinedBy then
      evalTactic (← `(tactic| llvm_symexec))
    for g' in ← getGoals do
      setGoals [g']
      if (← instantiateMVars (← getMainTarget)).isAppOf ``Config.IsRefinedBy then
        out := out.push g'
      else
        out := out ++ (← reduceValueGoal)
  setGoals out.toList

end Tactic

end LeanNanoLlvm.Refinement
