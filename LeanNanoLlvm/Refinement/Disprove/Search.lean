import Lean
import LeanNanoLlvm.Refinement.Refinement
import LeanNanoLlvm.Semantics.Module

/-! # Counterexample Search for `llvm_disprove`

Meta-level witness search that runs the executable interpreter
(`LeanNanoLlvm.Semantics.Module`). Only the disproof front end depends on this module.

The search is bounded by a budget of heartbeats (Lean's allocation counter, the unit of
`maxHeartbeats`) spent on all candidate runs, not by wall-clock time, so whether it finds a
witness, and which one, depends only on the program and the budget: the result is the same under
any load and on any machine running the same build. (A budget of interpreter steps would be
deterministic too, but the cost of a step varies by orders of magnitude: one step can copy a
large memory object.) An optional wall-clock
limit can be added as a safety net; when it is hit the result is reported as such. -/

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm AST Semantics

/-! ## Section 2: Meta-Level Heuristic Witness Search (Step-Budgeted) -/

/-- The search's limits: `heartbeats` (in thousands, like `maxHeartbeats`) in total
(deterministic), and optionally a wall-clock deadline (`IO.monoMsNow` value; not deterministic,
off by default). -/
structure SearchBudget where
  heartbeats : Nat
  deadlineMs? : Option Nat := none

/-- Why a search stopped without a witness. -/
inductive SearchStop where
  | exhausted   -- every candidate tried
  | heartbeats  -- the heartbeat budget ran out
  | wallClock   -- the optional wall-clock limit was reached
deriving Inhabited, BEq

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

/-- Run `fuel` steps from `c` and return the final configuration. Unlike `runSteps` (written with
`Nat.rec` so that the kernel can reduce it, and which builds the trace), this is tail-recursive, so
the search uses constant stack however many steps a candidate runs: interpreting `runSteps` on a
long loop exhausted Lean's interpreter stack and aborted the process ("deep recursion"). -/
private def runToFinal (fuel : Nat) (used : Nat) (o : OracleState) (c : Config) :
    Config × Nat × OracleState :=
  match fuel with
  | 0 => (c, used, o)
  | n + 1 =>
    match c with
    | .running _ =>
      let (_, c1, o1) := execStep o c
      runToFinal n (used + 1) o1 c1
    | _ => (c, used, o)

/-- The search state: the heartbeat count at which the budget ends, and why the search stopped
(if it did). -/
private structure SearchState where
  hbEnd : Nat
  stopped : Option SearchStop := none

private abbrev SearchM := StateT SearchState IO

private def outOfBudget (b : SearchBudget) : SearchM Bool := do
  let st ← get
  if st.stopped.isSome then return true
  if (← IO.getNumHeartbeats) >= st.hbEnd then
    set { st with stopped := some .heartbeats }; return true
  if let some d := b.deadlineMs? then
    if (← IO.monoMsNow) >= d then
      set { st with stopped := some .wallClock }; return true
  return false

/-- Steps run between two budget checks. -/
private def chunkSteps : Nat := 64

/-- Run a candidate (at most `cfg.maxSteps` steps), checking the budget every `chunkSteps`
steps; `none` if the budget ran out first. -/
private def runForSearch (b : SearchBudget) (defn : AST.Definition) (args : List RegisterValue) :
    SearchM (Option Config) := do
  let cfg : SemanticsConfig := .modern
  let mut c := initCallConfig cfg .default64LE {} ∅ ∅ defn args
  let mut done := 0
  let mut o : OracleState := default
  for _ in [:cfg.maxSteps / chunkSteps + 1] do
    if done >= cfg.maxSteps then break
    match c with
    | .running _ =>
      if ← outOfBudget b then return none
      let (c', n, o') := runToFinal (min chunkSteps (cfg.maxSteps - done)) 0 o c
      c := c'; done := done + n; o := o'
    | _ => break
  return some c

/-- Run `src` and `tgt` on `args` within the remaining budget. A candidate whose run is cut off
by the budget is not a witness (and the search then stops). -/
private def testWitness (b : SearchBudget) (src tgt : AST.Definition) (args : List RegisterValue) :
    SearchM Bool := do
  let some cSrc ← runForSearch b src args | return false
  match cSrc with
  | .halted _ _ =>
    let some cTgt ← runForSearch b tgt args | return false
    return isCounterexampleConfig cSrc cTgt
  | _ => return false

/-- Enumerate index tuples into `pools` whose index sum equals `targetSum`, within the budget.
    Total (no `partial`). -/
private def searchByPrioritySum (src tgt : AST.Definition) (pools : List (Array RegisterValue))
    (b : SearchBudget) (maxSum : Nat) : SearchM (Option (List RegisterValue)) := do
  -- Recursive helper over remaining pools (structurally recursive on `pools`)
  let rec go (rem : List (Array RegisterValue)) (budget : Nat) (acc : List RegisterValue) :
      SearchM (Option (List RegisterValue)) := do
    match rem with
    | [] =>
      if budget != 0 then return none
      if ← outOfBudget b then return none
      let args := acc.reverse
      if ← testWitness b src tgt args then return some args else return none
    | pool :: rest =>
      let limit := min (budget + 1) pool.size
      for i in [:limit] do
        if ← outOfBudget b then return none
        match ← go rest (budget - i) (pool[i]! :: acc) with
        | some w => return some w
        | none => pure ()
      return none
  for s in [:maxSum + 1] do
    if ← outOfBudget b then return none
    match ← go pools s [] with
    | some w => return some w
    | none => pure ()
  return none

/-- Default budget of `llvm_disprove`'s search, in thousands of heartbeats over all candidates
(a tenth of the default `maxHeartbeats`). Calibrated on the phase-2 corpus: every witness found
there costs under 40 (×1000); 2 s of search under the old wall-clock budget cost 2,000–43,000. -/
def defaultSearchHeartbeats : Nat := 20_000

/-- Heuristic counterexample search for `src ⊒ tgt`, bounded by `b`. Returns the witness, or
why the search stopped without one. -/
def findCounterexample (src tgt : AST.Definition) (b : SearchBudget) :
    IO (Except SearchStop (List RegisterValue)) := do
  let paramTypes :=
    match src.prototype.type with
    | .function _ pts => pts
    | _ => []
  let astConsts := collectDefInts src ++ collectDefInts tgt
  let mut pools : List (Array RegisterValue) := []
  for ty in paramTypes do
    match ty with
    | .int w => pools := pools ++ [buildCandidatesForWidth w astConsts]
    | _ => return .error .exhausted
  let maxSum := pools.foldl (fun acc p => acc + p.size) 0
  let search : SearchM (Option (List RegisterValue)) := do
    match ← searchByPrioritySum src tgt pools b maxSum with
    | some w => return some w
    | none =>
      if (← get).stopped.isSome then return none
      -- Fallback: deterministic PRNG sampling over the full pools
      let mut state : UInt64 := 0x243f6a8885a308d3
      for _ in [:20000] do
        if ← outOfBudget b then return none
        let mut args : List RegisterValue := []
        for pool in pools do
          state := state * 6364136223846793005 + 1442695040888963407
          let idx := (state.toNat) % pool.size
          args := args ++ [pool[idx]!]
        if ← testWitness b src tgt args then
          return some args
      return none
  let hb0 ← IO.getNumHeartbeats
  let (r, st) ← search.run { hbEnd := hb0 + b.heartbeats * 1000 }
  if (← IO.getEnv "LNL_DISPROVE_STATS").isSome then
    IO.eprintln s!"llvm_disprove search: {((← IO.getNumHeartbeats) - hb0) / 1000} heartbeats (×1000)"
  match r with
  | some w => return .ok w
  | none => return .error (st.stopped.getD .exhausted)

open Lean Elab Tactic Meta

unsafe def evalDefImpl (e : Expr) : MetaM AST.Definition :=
  Lean.Meta.evalExpr AST.Definition (mkConst ``AST.Definition) e

@[implemented_by evalDefImpl]
def evalDef (_ : Expr) : MetaM AST.Definition :=
  throwError "evalDef requires compiled VM"

end LeanNanoLlvm.Refinement
