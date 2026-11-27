import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import LeanNanoLlvm.AST.Unexpander
import Tests.Refinement.Helpers
import Tests.Refinement.Undef
import Tests.Refinement.Poison
import Tests.Refinement.Freeze

/-! Refinement tests: transitivity chaining via `Trans` (`calc`). -/

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

/-! ### Transitivity Chaining via Lean Core `Trans` (`calc`) -/

/-- Chaining `poisonDef ⊒ freezePoisonDef ⊒ zeroDef` using a native Lean `calc` block. -/
theorem zero_refines_poison_via_calc : poisonDef ⊒ zeroDef :=
  calc
    poisonDef ⊒ freezePoisonDef := freeze_poison_refines_poison
    _         ⊒ zeroDef         := zero_refines_freeze_poison

/-- Config-explicit transitivity chaining under `SemanticsConfig.withUndef`. -/
theorem undef_mul2_refines_poison_via_trans :
    poisonDef ⊒[SemanticsConfig.withUndef] undefMul2Def8 := by
  have hAddRefPoison : poisonDef ⊒[SemanticsConfig.withUndef] undefAddDef8 := by
    refine ⟨rfl, ?_⟩
    intro initMem args _ hargs
    cases args with
    | cons _ _ => llvm_wf [poisonDef] at hargs
    | nil =>
      right
      have hstep1 : ∀ ev c',
          Step (initCallConfig .withUndef .default64LE initMem ∅ ∅ undefAddDef8 []) ev c' →
          ev = none ∧ ∃ b1 b2 : BitVec 8,
            c' = .running {
              frames := [{
                defn := undefAddDef8
                curBlock := .name "entry"
                remainingCode := []
                terminator := entryTerm undefAddDef8
                registers := (∅ : AssocMap AST.Identifier RegisterValue).insert
                  (.local_id (.name "x")) (.bv 8 (.value (b1 + b2)))
              }]
              memory := initMem
              config := .withUndef
              dataLayout := .default64LE
            } := by
        intro ev c' hs
        rw [initCallConfig_0 .withUndef .default64LE initMem undefAddDef8 rfl rfl rfl rfl] at hs
        rw [Step.instr_iff rfl rfl] at hs
        cases hs with
        | intBinaryOp_e1_err he1 =>
          rw [EvalExp.undef_iff (by rfl) (by rfl)] at he1; obtain ⟨_, h, _⟩ := he1; cases h
        | intBinaryOp_e2_err he1 he2 =>
          rw [EvalExp.undef_iff (by rfl) (by rfl)] at he1; obtain ⟨_, h1, _⟩ := he1; cases h1
          rw [EvalExp.undef_iff (by rfl) (by rfl)] at he2; obtain ⟨_, h2, _⟩ := he2; cases h2
        | intBinaryOp_eval_err he1 he2 hbin =>
          rw [EvalExp.undef_iff (by rfl) (by rfl)] at he1; obtain ⟨_, h1, hu1⟩ := he1; cases h1
          rw [EvalExp.undef_iff (by rfl) (by rfl)] at he2; obtain ⟨_, h2, hu2⟩ := he2; cases h2
          obtain ⟨b1, rfl, _⟩ := undefValRel_int_iff.mp hu1
          obtain ⟨b2, rfl, _⟩ := undefValRel_int_iff.mp hu2
          llvm_simp at hbin
        | intBinaryOp_ok he1 he2 hbin =>
          rw [EvalExp.undef_iff (by rfl) (by rfl)] at he1; obtain ⟨_, h1, hu1⟩ := he1; cases h1
          rw [EvalExp.undef_iff (by rfl) (by rfl)] at he2; obtain ⟨_, h2, hu2⟩ := he2; cases h2
          obtain ⟨b1, rfl, _⟩ := undefValRel_int_iff.mp hu1
          obtain ⟨b2, rfl, _⟩ := undefValRel_int_iff.mp hu2
          llvm_simp at hbin
          subst hbin
          exact ⟨rfl, b1, b2, rfl⟩
      have hstep2 : ∀ (b1 b2 : BitVec 8) ev c',
          Step (.running {
            frames := [{
              defn := undefAddDef8
              curBlock := .name "entry"
              remainingCode := []
              terminator := entryTerm undefAddDef8
              registers := (∅ : AssocMap AST.Identifier RegisterValue).insert
                (.local_id (.name "x")) (.bv 8 (.value (b1 + b2)))
            }]
            memory := initMem
            config := .withUndef
            dataLayout := .default64LE
          }) ev c' ↔
          ev = none ∧ c' = .halted (.bv 8 (.value (b1 + b2))) initMem := by
        intro b1 b2 ev c'
        rw [Step.ret_top_leaf_iff rfl rfl rfl rfl
              (v := .bv 8 (.value (b1 + b2))) (by llvm_step)]
        simp only [freeAllocaList, applyRetFMFAndAttrsPure, undefAddDef8]
        rfl
      refine ⟨?_, ?_, ?_⟩
      · rintro (⟨tr, msg, hstar⟩ | ⟨tr, err, hstar⟩)
        · cases hstar with
          | step hs hrest =>
            obtain ⟨rfl, b1, b2, rfl⟩ := hstep1 _ _ hs
            exact (det_step_to_halted (hstep2 b1 b2)).1 (Or.inl ⟨_, msg, hrest⟩)
        · cases hstar with
          | step hs hrest =>
            obtain ⟨rfl, b1, b2, rfl⟩ := hstep1 _ _ hs
            exact (det_step_to_halted (hstep2 b1 b2)).1 (Or.inr ⟨_, err, hrest⟩)
      · intro trY retY memY htY
        cases htY with
        | step hs hrest =>
          obtain ⟨rfl, b1, b2, rfl⟩ := hstep1 _ _ hs
          obtain ⟨rfl, rfl, hmemEq⟩ := (det_step_to_halted (hstep2 b1 b2)).2.2 _ _ _ hrest
          rw [hmemEq]
          have hP : Terminates (initCallConfig .withUndef .default64LE initMem ∅ ∅ poisonDef [])
              [] (.bv 8 .poison) initMem :=
            StarStep.step (ev := none) ((poisonDef_det .withUndef initMem _ _).mpr ⟨rfl, rfl⟩) (StarStep.refl _)
          exact ⟨[], .bv 8 .poison, initMem, .id,
            MemoryInjection.id_idOn _, hP,
            trivial, rfl, MemoryState.IsRefinedBy.refl _ _⟩
      · intro hdiv
        obtain ⟨ev, c1, hs, hdiv1⟩ := Diverges.step_inv hdiv
        obtain ⟨rfl, b1, b2, rfl⟩ := hstep1 ev c1 hs
        exact False.elim ((det_step_to_halted (hstep2 b1 b2)).2.1 hdiv1)
  exact Definition.IsRefinedByWith.trans hAddRefPoison undef_add_is_refined_by_undef_mul2_i8

end LeanNanoLlvm.Refinement
