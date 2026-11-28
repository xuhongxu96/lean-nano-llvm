import Lean
import LeanNanoLlvm.Refinement.Disprove.Search
import LeanNanoLlvm.Refinement.Disprove.Stepper

/-!
# Kernel-Pure Refinement Disproof Tactic (`llvm_disprove`)

Proves negations of LLVM IR refinement (`¬ (src ⊒ tgt)`) with **100% kernel purity**
(ONLY `{propext, Classical.choice, Quot.sound}`).

Supports two modes:
- `llvm_disprove [arg1, arg2, ...]` — certify a specific concrete counterexample `List RegisterValue`.
- `llvm_disprove` / `llvm_disprove (heartbeats := 400000)` — run a heartbeat-budgeted (deterministic)
  meta-level heuristic witness search (no bitwidth cap; works for `i1`..`i128`+) prioritizing
  `poison`, AST-extracted constants (`c`, `c ± 1`, `-c`, `~c`), bitwidth boundaries
  (`0, 1, -1, INT_MIN, INT_MAX, w, w-1`), powers of two, and PRNG bit patterns, then
  synthesize a kernel-pure refutation proof from the discovered witness.

This module is only the tactic front end. The implementation is split so that each part
rebuilds independently:
- `Disprove.Lemmas`  — kernel-pure refutation lemmas (no meta code).
- `Disprove.Search`  — heuristic witness search (depends on the executable interpreter).
- `Disprove.Stepper` — concrete stepper that certifies a witness.

Proof files that only use `llvm_refine` must not import this module; import
`LeanNanoLlvm.Refinement.Tactic` instead.
-/

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm AST Semantics
open Lean Elab Tactic Meta

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

/-- A setting of `llvm_disprove`'s search: `(heartbeats := N)` (thousands; deterministic) or
`(timeout := ms)` (wall clock; a safety net, not deterministic). -/
syntax disproveCfg := "(" (&"heartbeats" <|> &"timeout") " := " num ")"

/-- Disprove an unsound LLVM IR refinement `¬ (src ⊒ tgt)` via a heuristic counterexample
    search + kernel-pure certification. The search is bounded by `heartbeats` (thousands, as in
    `maxHeartbeats`; default `defaultSearchHeartbeats`), so its outcome is deterministic.
    `timeout := ms` adds a wall-clock limit as a safety net (not deterministic; off by default). -/
syntax "llvm_disprove" (ppSpace disproveCfg)* : tactic

/-- Like `llvm_disprove`, but also displays the found counterexample and emits a clickable
    `Try this: llvm_disprove [...]` suggestion (like `simp?`). -/
syntax "llvm_disprove?" (ppSpace disproveCfg)* : tactic

private def parseDisproveCfgs (cfgs : Array (TSyntax ``disproveCfg)) : Nat × Option Nat := Id.run do
  let mut hb := defaultSearchHeartbeats
  let mut to? : Option Nat := none
  for c in cfgs do
    let isHb := (c.raw.find? fun t => t.isAtom && t.getAtomVal == "heartbeats").isSome
    let n := ((c.raw.find? fun t => t.isNatLit?.isSome).bind (·.isNatLit?)).getD 0
    if isHb then hb := n else to? := some n
  return (hb, to?)

private def runDisproveSearch (stx : Syntax) (hbBudget : Nat) (timeoutMs? : Option Nat)
    (suggest : Bool) : TacticM Unit := do
  let (srcExpr, tgtExpr) ← extractNotDefRefines
  let srcDef ← evalDef srcExpr
  let tgtDef ← evalDef tgtExpr
  let deadline? ← timeoutMs?.mapM fun ms => return (← IO.monoMsNow) + ms
  match ← findCounterexample srcDef tgtDef ⟨hbBudget, deadline?⟩ with
  | .error .exhausted =>
    throwError "llvm_disprove: no counterexample among the candidates searched"
  | .error .heartbeats =>
    throwError "llvm_disprove: no counterexample found within {hbBudget} heartbeats (×1000)"
  | .error .wallClock =>
    throwError "llvm_disprove: no counterexample found within {timeoutMs?.getD 0}ms (wall clock)"
  | .ok witness =>
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
  | `(tactic| llvm_disprove $cfgs:disproveCfg*) => do
    let (hb, to?) := parseDisproveCfgs cfgs
    runDisproveSearch (← getRef) hb to? false
  | `(tactic| llvm_disprove? $cfgs:disproveCfg*) => do
    let (hb, to?) := parseDisproveCfgs cfgs
    runDisproveSearch (← getRef) hb to? true

end LeanNanoLlvm.Refinement

