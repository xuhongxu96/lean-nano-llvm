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
`grind`, `bv_omega`, `ext _ _; simp; grind`, and splitting every remaining `if` before trying
`grind` / `bv_omega` / `simp_all` again. A leaf none of them proves is left open, unchanged.
-/

namespace LeanNanoLlvm.Refinement

section Tactic

open Lean Meta Elab Tactic

/-- Try the standard closers on the main goal; keep the goal unchanged if none proves it. -/
private def tryClosers : TacticM Unit := do
  let s ← saveState
  try
    evalTactic (← `(tactic|
      first
      | (llvm_guard grind; done)
      | (llvm_guard bv_omega; done)
      | (llvm_guard (ext _ _; simp; (try grind)); done)
      | (llvm_guard ((repeat' split) <;>
          first | (grind; done) | (bv_omega; done) | (simp_all; done)); done)))
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
