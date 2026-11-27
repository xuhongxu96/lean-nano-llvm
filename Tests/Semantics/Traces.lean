import LeanNanoLlvm.AST
import LeanNanoLlvm.Tactic
import LeanNanoLlvm.Semantics
import Tests.Semantics.Helpers
import Tests.Semantics.ControlFlow

/-! Semantics tests: small-step traces, parameter attributes, varargs and `runSteps_sound`. -/

open LeanNanoLlvm
open AST.Syntax
open Semantics

section

open scoped LeanNanoLlvm.AST.Syntax

/-! ### Small-Step Traces, Single-Block Param Attrs, Varargs & `runSteps_sound` -/

/-- Volatile loads and stores emit observable `TraceEvent`s in program order. -/
def volatileMemDef : AST.Definition :=
  [llvm-definition|
    define i8 @vol() {
    entry:
      %p = alloca i8, align 1
      store volatile i8 42, ptr %p, align 1
      %v = load volatile i8, ptr %p, align 1
      ret i8 %v
    }
  ]

theorem volatile_store_and_load_emit_trace_events :
    let (tr, cfg, _) := runDefinitionWithTrace volatileMemDef []
    tr.length = 2 ∧
    (match tr with
     | [.volatileStore 0 _ bs1, .volatileLoad 0 _ bs2] => bs1.size == 1 && bs2.size == 1
     | _ => false) = true ∧
    cfg.toExcept = .ok (.bv 8 (.value (42 : BitVec 8))) := by
  decide +kernel

/-- Single-block functions enforce callee parameter attributes (`noundef` on `poison` → Immediate UB). -/
def singleBlockNoundefDef : AST.Definition :=
  [llvm-definition|
    define i8 @f(i8 noundef %x) {
    entry:
      ret i8 %x
    }
  ]

theorem single_block_noundef_param_poison_is_ub :
    isImmediateUB (runDefinitionRet singleBlockNoundefDef [.bv 8 .poison]) = true := by
  decide +kernel

theorem single_block_noundef_param_value_ok :
    runDefinitionRet singleBlockNoundefDef [.bv 8 (.value (9 : BitVec 8))] =
      .ok (.bv 8 (.value (9 : BitVec 8))) := by
  decide +kernel

/-- Varargs function accepts extra arguments beyond fixed parameters. -/
def varargsModule : AST.TopLevel := [llvm|
  define i32 @first_arg(i32 %x, ...) {
  entry:
    ret i32 %x
  }

  define i32 @main() {
  entry:
    %r = call i32 @first_arg(i32 42, i32 99, i8 7)
    ret i32 %r
  }
]

theorem varargs_call_returns_first_arg :
    runModuleFunction varargsModule (.name "main") =
      .ok (.bv 32 (.value (42 : BitVec 32))) := by
  decide +kernel

private theorem exists_halted_of_toExcept_ok {c : Config} {v : RegisterValue}
    (h : c.toExcept = .ok v) : ∃ m, c = .halted v m := by
  cases c with
  | halted v' m => simp [Config.toExcept] at h; subst h; exact ⟨m, rfl⟩
  | running _ | ub _ | staticError _ | resourceError _ => simp [Config.toExcept] at h

/-- End-to-end soundness bridge: `runSteps_sound` turns a kernel-evaluated execution
    into a genuine relational `Terminates` (`StarStep`) derivation of `fib(10) = 55`. -/
theorem fib10_terminates_in_step_semantics :
    ∃ finalMem,
      Terminates
        (initCallConfig .modern .default64LE {} ∅ ∅ fibDef [.bv 32 (.value (10 : BitVec 32))])
        [] (.bv 32 (.value (55 : BitVec 32))) finalMem := by
  let c0 := initCallConfig .modern .default64LE {} ∅ ∅ fibDef [.bv 32 (.value (10 : BitVec 32))]
  have hwf0 : Config.WellFormed c0 := by
    dsimp only [c0, initCallConfig, mkEntryFrame, bindFrameArgs, Config.WellFormed]
    exact MemoryState.empty_wf
  have hsound := runSteps_sound 100 default c0 hwf0
  have htr : (runSteps 100 default c0).1 = [] := by decide +kernel
  have hval : (runSteps 100 default c0).2.1.toExcept = .ok (.bv 32 (.value (55 : BitVec 32))) := by
    decide +kernel
  obtain ⟨finalMem, hcfg⟩ := exists_halted_of_toExcept_ok hval
  rw [htr, hcfg] at hsound
  exact ⟨finalMem, hsound⟩

end
