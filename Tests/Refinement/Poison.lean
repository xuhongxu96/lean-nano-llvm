import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import LeanNanoLlvm.AST.Unexpander
import Tests.Refinement.Helpers

/-! Refinement tests: poison refinement. -/

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

/-! ### Poison Refinement -/

open scoped LeanNanoLlvm.AST.Syntax in
def poisonDef : AST.Definition := [llvm-definition|
  define i8 @f() {
  entry:
    ret i8 poison
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
def zeroDef : AST.Definition := [llvm-definition|
  define i8 @f() {
  entry:
    ret i8 0
  }
]

theorem zeroDef_det (cfg : SemanticsConfig) (initMem : MemoryState) :
    ∀ ev c', Step (initCallConfig cfg .default64LE initMem ∅ ∅ zeroDef []) ev c' ↔
      ev = none ∧ c' = .halted (.bv 8 (.value (0 : BitVec 8))) initMem := by
  intro ev c'
  rw [initCallConfig_0 cfg .default64LE initMem zeroDef rfl rfl rfl rfl]
  rw [Step.ret_top_leaf_iff rfl rfl rfl rfl (v := .bv 8 (.value (0 : BitVec 8))) (by simp [evalPureLeafExp?])]
  rfl

theorem poisonDef_det (cfg : SemanticsConfig) (initMem : MemoryState) :
    ∀ ev c', Step (initCallConfig cfg .default64LE initMem ∅ ∅ poisonDef []) ev c' ↔
      ev = none ∧ c' = .halted (.bv 8 .poison) initMem := by
  intro ev c'
  rw [initCallConfig_0 cfg .default64LE initMem poisonDef rfl rfl rfl rfl]
  rw [Step.ret_top_leaf_iff rfl rfl rfl rfl (v := .bv 8 .poison) (by simp [evalPureLeafExp?, RegisterValue.poisonOf])]
  rfl

theorem poison_is_refined_by_zero : poisonDef ⊒ zeroDef := by
  llvm_refine

theorem zero_is_not_refined_by_poison : ¬ (zeroDef ⊒ poisonDef) := by
  rintro ⟨_, hbeh⟩
  have hinst := hbeh {} [] MemoryState.empty_wf
    (by llvm_wf [zeroDef])
  have hZ := det_step_to_halted (zeroDef_det .modern {})
  rcases hinst with habort | ⟨_, hterm, _⟩
  · exact hZ.1 habort
  · have hP : Terminates (initCallConfig .modern .default64LE {} ∅ ∅ poisonDef [])
        [] (.bv 8 .poison) {} :=
      StarStep.step ((poisonDef_det .modern {} _ _).mpr ⟨rfl, rfl⟩) (StarStep.refl _)
    obtain ⟨trX, retX, memX, inj, _, hTermX, _, hvalRef, _⟩ := hterm [] _ {} hP
    obtain ⟨rfl, rfl, rfl⟩ := hZ.2.2 _ _ _ hTermX
    simp [RegisterValue.IsRefinedBy] at hvalRef

end LeanNanoLlvm.Refinement
