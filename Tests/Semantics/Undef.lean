import LeanNanoLlvm.AST
import LeanNanoLlvm.Tactic
import LeanNanoLlvm.Semantics
import Tests.Semantics.Helpers

/-! Semantics tests: optional `undef` switch (`disabled` / `nondet` / `zero`). -/

open LeanNanoLlvm
open AST.Syntax
open Semantics

section

open scoped LeanNanoLlvm.AST.Syntax

/-! ### Optional `undef` Switch (`disabled` vs `nondet` vs `zero`) -/

def undefUseDef : AST.Definition :=
  [llvm-definition|
    define i8 @f() {
    entry:
      %x = add i8 undef, 1
      ret i8 %x
    }
  ]

theorem undef_rejected_when_disabled_wf : ¬ undefUseDef.WellFormed := by
  rw [AST.definition_wellFormed_iff, AST.definition_wellFormedWith_iff]
  simp [undefUseDef, simp_wellform, SemanticsConfig.modern]

theorem undef_allowed_when_enabled_wf : undefUseDef.WellFormedWith .withUndef := by
  rw [AST.definition_wellFormedWith_iff]
  refine ⟨_, _, _, ?_, rfl, rfl, by simp [undefUseDef], by simp [undefUseDef], by simp [undefUseDef], ?_⟩
  · rw [AST.declaration_wellFormed_iff]
    simp [AST.Declaration.WellFormedType, undefUseDef]
  · simp [undefUseDef, simp_wellform, SemanticsConfig.withUndef]

theorem undef_rejected_at_runtime_modern :
    isStaticError (runDefinitionRet undefUseDef [] .modern) = true := by
  decide +kernel

theorem undef_nondet_draws_from_oracle :
    runDefinitionRet undefUseDef [] .withUndef .default64LE { oracle := NondetOracle.ofList [41] } =
      .ok (.bv 8 (.value (42 : BitVec 8))) := by
  decide +kernel

theorem undef_deterministic_returns_zero :
    runDefinitionRet undefUseDef [] .deterministic =
      .ok (.bv 8 (.value (1 : BitVec 8))) := by
  decide +kernel

def uninitAllocaLoadDef : AST.Definition :=
  [llvm-definition|
    define i8 @f() {
    entry:
      %p = alloca i8, align 1
      %v = load i8, ptr %p, align 1
      ret i8 %v
    }
  ]

theorem uninit_alloca_is_poison_when_undef_disabled :
    runDefinitionRet uninitAllocaLoadDef [] .modern =
      .ok (.bv 8 .poison) := by
  decide +kernel

/-- Uninitialized memory draws one oracle value per byte containing undef bits (its low 8 bits
supply the bits, as `llubi` does with `Rng()`); here `0x15A` yields `0x5A`. -/
theorem uninit_alloca_is_oracle_value_when_undef_enabled :
    runDefinitionRet uninitAllocaLoadDef [] .withUndef .default64LE
        { oracle := NondetOracle.ofList [0x15A] } =
      .ok (.bv 8 (.value (0x5A : BitVec 8))) := by
  decide +kernel

end
