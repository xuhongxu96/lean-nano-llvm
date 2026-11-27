import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import LeanNanoLlvm.AST.Unexpander
import Tests.Refinement.Helpers
import Tests.Refinement.Poison

/-! Refinement tests: nondeterministic `freeze` refinement. -/

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

/-! ### True Nondeterministic `freeze` Refinement -/

open scoped LeanNanoLlvm.AST.Syntax in
def freezePoisonDef : AST.Definition := [llvm-definition|
  define i8 @f() {
  entry:
    %r = freeze i8 poison
    ret i8 %r
  }
]

theorem zero_refines_freeze_poison : freezePoisonDef ⊒ zeroDef := by
  llvm_refine

theorem freeze_poison_refines_poison : poisonDef ⊒ freezePoisonDef := by
  llvm_refine

theorem freeze_poison_not_refines_zero : ¬ (zeroDef ⊒ freezePoisonDef) := by
  rintro ⟨_, hbeh⟩
  have hinst := hbeh {} [] MemoryState.empty_wf
    (by llvm_wf [zeroDef])
  have hZ := det_step_to_halted (zeroDef_det .modern {})
  rcases hinst with habort | ⟨_, hterm, _⟩
  · exact hZ.1 habort
  · have hTermY : Terminates (initCallConfig .modern .default64LE {} ∅ ∅ freezePoisonDef [])
        [] (.bv 8 (.value (1 : BitVec 8))) {} := by
      rw [initCallConfig_0 .modern .default64LE {} freezePoisonDef rfl rfl rfl rfl]
      exact StarStep.step (ev := none)
        (Step.instr rfl rfl
          (StepInstr.freeze_ok
            (EvalExp.leaf_ok (by simp [evalPureLeafExp?, RegisterValue.poisonOf]))
            (FreezeRel.bv_poison 8 (1 : BitVec 8) (by intro h; cases h))))
        (StarStep.step (ev := none)
          (Step.term rfl rfl rfl
            (StepTerm.ret_ok rfl
              (EvalExp.leaf_ok (by llvm_step; rfl))
              (StepRet.top_ok rfl (by llvm_step [freezePoisonDef]))))
          (StarStep.refl _))
    obtain ⟨trX, retX, memX, inj, _, hTermX, _, hvalRef, _⟩ := hterm [] _ {} hTermY
    obtain ⟨rfl, rfl, rfl⟩ := hZ.2.2 _ _ _ hTermX
    simp [RegisterValue.IsRefinedBy] at hvalRef

end LeanNanoLlvm.Refinement
