import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import LeanNanoLlvm.AST.Unexpander
import Tests.Refinement.Helpers

/-! Refinement tests: IEEE-754 floating-point refinement. -/

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

/-! ### IEEE-754 Floating-Point Refinement (`fneg (fneg %x)` & Fast-Math Flags) -/

open scoped LeanNanoLlvm.AST.Syntax in
def idFloatDef : AST.Definition := [llvm-definition|
  define float @f(float %x) {
  entry:
    ret float %x
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
def fnegFnegDef : AST.Definition := [llvm-definition|
  define float @f(float %x) {
  entry:
    %y = fneg float %x
    %z = fneg float %y
    ret float %z
  }
]

theorem fneg_fneg_is_refined_by_id : fnegFnegDef ⊒ idFloatDef := by
  llvm_refine

private theorem handleDenormal_ieee (x : IEEEFloat FloatFormat.single) (b1 b2 : Bool) :
    handleDenormal .ieee b1 b2 x = x := by
  unfold handleDenormal
  by_cases h1 : (!x.isSubnormal) = true
  · rw [if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : (b1 && b2) = true
    · rw [if_pos h2]
    · rw [if_neg h2]

private theorem evalFloatBinary_fadd_refines_nnan (va vb : FloatW .float) (o : OracleState) :
    ∃ (rt rs : FloatW .float) (o1 o2 : OracleState),
      evalFloatBinaryExec .modern (.fadd {}) (.float .float) (.float .float va) (.float .float vb) o =
        .ok (.float .float rt, o1) ∧
      evalFloatBinaryExec .modern (.fadd { «nnan» := true }) (.float .float) (.float .float va) (.float .float vb) o =
        .ok (.float .float rs, o2) ∧
      RegisterValue.IsRefinedBy .id (.float .float rs) (.float .float rt) := by
  have hinV : ∀ (x : IEEEFloat FloatFormat.single) (o0 : OracleState), x.isNaN = false →
      fmfIn { «nnan» := true } x o0 = (.value x, o0) := by
    intro x o0 hx; unfold fmfIn; simp only [hx, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  have hinP : ∀ (x : IEEEFloat FloatFormat.single) (o0 : OracleState), x.isNaN = true →
      fmfIn { «nnan» := true } x o0 = (.poison, o0) := by
    intro x o0 hx; unfold fmfIn; simp only [hx, Bool.and_true, ↓reduceIte]
  have hpoisonL : ∀ (t : FloatW .float), RegisterValue.IsRefinedBy .id (.float .float .poison) (.float .float t) := by
    intro t; simp [RegisterValue.IsRefinedBy]
  unfold evalFloatBinaryExec
  dsimp only [↓reduceDIte]
  refine ⟨_, _, _, _, rfl, rfl, ?_⟩
  cases va using PoisonOr.casesOn' with
  | poison => exact hpoisonL _
  | value fa =>
    cases vb using PoisonOr.casesOn' with
    | poison => exact hpoisonL _
    | value fb =>
      by_cases ha : fa.isNaN = true
      · simp only [evalFloatBinaryOp, hinP fa o ha]; exact hpoisonL _
      · have ha' : fa.isNaN = false := Bool.eq_false_iff.mpr ha
        by_cases hb : fb.isNaN = true
        · simp only [evalFloatBinaryOp, hinV fa o ha', hinP fb o hb]; exact hpoisonL _
        · have hb' : fb.isNaN = false := Bool.eq_false_iff.mpr hb
          simp only [evalFloatBinaryOp, fmfIn_none, hinV fa o ha', hinV fb o hb',
            SemanticsConfig.modern, denormIn_ieee_fst, handleDenormal_ieee]
          by_cases hr : (IEEEFloat.add RoundingMode.RNE fa fb).isNaN = true
          · simp only [handleFMF, hr, Bool.and_true, ↓reduceIte]; exact hpoisonL _
          · have hr' := Bool.eq_false_iff.mpr hr
            simp only [handleFMF, hr', Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              nanPropagate_not_nan _ _ _ _ hr']
            exact RegisterValue.IsRefinedBy.refl _

open scoped LeanNanoLlvm.AST.Syntax in
def faddDef : AST.Definition := [llvm-definition|
  define float @f(float %a, float %b) {
  entry:
    %r = fadd float %a, %b
    ret float %r
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
def faddNnanDef : AST.Definition := [llvm-definition|
  define float @f(float %a, float %b) {
  entry:
    %r = fadd nnan float %a, %b
    ret float %r
  }
]

theorem fadd_refines_fadd_nnan : faddNnanDef ⊒ faddDef := by
  refine ⟨rfl, ?_⟩
  intro initMem args _ hargs
  rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · llvm_wf [faddNnanDef] at hargs
  · llvm_wf [faddNnanDef] at hargs
  · cases a <;> cases b <;>
      llvm_wf [faddNnanDef] at hargs
    rcases hargs with ⟨rfl, rfl⟩
    rename_i va vb
    have hba : (AST.Identifier.local_id (.name "b") == AST.Identifier.local_id (.name "a")) = false := rfl
    right
    have hstep1 : ∀ ev c',
        Step (initCallConfig .modern .default64LE initMem ∅ ∅ faddDef [.float .float va, .float .float vb]) ev c' →
        ev = none ∧ ∃ (o : OracleState) (rt rs : FloatW .float) (o2 : OracleState),
          evalFloatBinaryExec .modern (.fadd { «nnan» := true }) (.float .float)
            (.float .float va) (.float .float vb) o = .ok (.float .float rs, o2) ∧
          RegisterValue.IsRefinedBy .id (.float .float rs) (.float .float rt) ∧
          c' = .running {
            frames := [{
              defn := faddDef
              curBlock := .name "entry"
              remainingCode := []
              terminator := entryTerm faddDef
              registers := (((∅ : AssocMap AST.Identifier RegisterValue).insert
                (.local_id (.name "a")) (.float .float va)).insert
                (.local_id (.name "b")) (.float .float vb)).insert
                (.local_id (.name "r")) (.float .float rt)
            }]
            memory := initMem
            config := .modern
            dataLayout := .default64LE
          } := by
      intro ev c' hs
      rw [initCallConfig_2 .modern .default64LE initMem faddDef
            rfl (Or.inl rfl) rfl rfl rfl rfl rfl] at hs
      rw [Step.instr_iff rfl rfl] at hs
      have haLeaf : evalPureLeafExp? .default64LE .modern
          (((∅ : AssocMap AST.Identifier RegisterValue).insert
            (.local_id (.name "a")) (.float .float va)).insert
            (.local_id (.name "b")) (.float .float vb))
          initMem (.float .float) (.identifier (.local_id (.name "a"))) =
          some (.ok (.float .float va)) := by
        simp [evalPureLeafExp?, AssocMap.get?_insert, hba]
      have hbLeaf : evalPureLeafExp? .default64LE .modern
          (((∅ : AssocMap AST.Identifier RegisterValue).insert
            (.local_id (.name "a")) (.float .float va)).insert
            (.local_id (.name "b")) (.float .float vb))
          initMem (.float .float) (.identifier (.local_id (.name "b"))) =
          some (.ok (.float .float vb)) := by
        simp [evalPureLeafExp?, AssocMap.get?_insert]
      cases hs with
      | floatBinaryOp_e1_err he1 => rw [EvalExp.leaf_iff haLeaf] at he1; cases he1
      | floatBinaryOp_e2_err he1 he2 =>
        rw [EvalExp.leaf_iff haLeaf] at he1; cases he1
        rw [EvalExp.leaf_iff hbLeaf] at he2; cases he2
      | floatBinaryOp_eval_err he1 he2 hf =>
        rw [EvalExp.leaf_iff haLeaf] at he1; cases he1
        rw [EvalExp.leaf_iff hbLeaf] at he2; cases he2
        obtain ⟨o, ho⟩ := hf
        dsimp only [frameDenormalCfg, faddDef] at ho
        obtain ⟨rt, rs, o1, o2, hok, _, _⟩ := evalFloatBinary_fadd_refines_nnan va vb o
        rw [hok] at ho; cases ho
      | floatBinaryOp_ok he1 he2 hf =>
        rw [EvalExp.leaf_iff haLeaf] at he1; cases he1
        rw [EvalExp.leaf_iff hbLeaf] at he2; cases he2
        obtain ⟨o, o1', ho⟩ := hf
        dsimp only [frameDenormalCfg, faddDef] at ho
        obtain ⟨rt, rs, o1, o2, hok, hokS, href⟩ := evalFloatBinary_fadd_refines_nnan va vb o
        rw [hok] at ho; cases ho
        exact ⟨rfl, o, rt, rs, o2, hokS, href, rfl⟩
    have hstep2 : ∀ (rt : FloatW .float) ev c',
        Step (.running {
          frames := [{
            defn := faddDef
            curBlock := .name "entry"
            remainingCode := []
            terminator := entryTerm faddDef
            registers := (((∅ : AssocMap AST.Identifier RegisterValue).insert
              (.local_id (.name "a")) (.float .float va)).insert
              (.local_id (.name "b")) (.float .float vb)).insert
              (.local_id (.name "r")) (.float .float rt)
          }]
          memory := initMem
          config := .modern
          dataLayout := .default64LE
        }) ev c' ↔
        ev = none ∧ c' = .halted (.float .float rt) initMem := by
      intro rt ev c'
      rw [Step.ret_top_leaf_iff rfl rfl rfl rfl
        (v := .float .float rt) (by llvm_step)]
      rfl
    refine ⟨?_, ?_, ?_⟩
    · rintro (⟨tr, msg, hstar⟩ | ⟨tr, err, hstar⟩)
      · cases hstar with
        | step hs hrest =>
          obtain ⟨rfl, _, rt, _, _, _, _, rfl⟩ := hstep1 _ _ hs
          exact (det_step_to_halted (hstep2 rt)).1 (Or.inl ⟨_, msg, hrest⟩)
      · cases hstar with
        | step hs hrest =>
          obtain ⟨rfl, _, rt, _, _, _, _, rfl⟩ := hstep1 _ _ hs
          exact (det_step_to_halted (hstep2 rt)).1 (Or.inr ⟨_, err, hrest⟩)
    · intro trY retY memY htY
      cases htY with
      | step hs hrest =>
        obtain ⟨rfl, o, rt, rs, o2, hokS, href, rfl⟩ := hstep1 _ _ hs
        obtain ⟨rfl, rfl, hmemEq⟩ := (det_step_to_halted (hstep2 rt)).2.2 _ _ _ hrest
        rw [hmemEq]
        have hTermX : Terminates (initCallConfig .modern .default64LE initMem ∅ ∅ faddNnanDef [.float .float va, .float .float vb])
            [] (.float .float rs) initMem := by
          rw [initCallConfig_2 .modern .default64LE initMem faddNnanDef
                rfl (Or.inl rfl) rfl rfl rfl rfl rfl]
          exact StarStep.step (ev := none)
            (Step.instr rfl rfl (StepInstr.floatBinaryOp_ok
              (EvalExp.leaf_ok (by llvm_step [hba]))
              (EvalExp.leaf_ok (by llvm_step))
              ⟨o, o2, hokS⟩))
            (StarStep.step (ev := none)
              (Step.term rfl rfl rfl
                (StepTerm.ret_ok rfl
                  (EvalExp.leaf_ok (by llvm_step; rfl))
                  (StepRet.top_ok rfl (by llvm_step [faddNnanDef]))))
              (StarStep.refl _))
        exact ⟨[], .float .float rs, initMem, .id,
          MemoryInjection.id_idOn _, hTermX,
          trivial, href, MemoryState.IsRefinedBy.refl _ _⟩
    · intro hdiv
      obtain ⟨ev, c1, hs, hdiv1⟩ := Diverges.step_inv hdiv
      obtain ⟨rfl, _, rt, _, _, _, _, rfl⟩ := hstep1 ev c1 hs
      exact False.elim ((det_step_to_halted (hstep2 rt)).2.1 hdiv1)
  · llvm_wf [faddNnanDef] at hargs

end LeanNanoLlvm.Refinement
