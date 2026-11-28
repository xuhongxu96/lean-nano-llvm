import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import LeanNanoLlvm.AST.Unexpander
import Tests.Refinement.Helpers

/-! Refinement tests: module-aware refinement (`RefinementEnv`) with helper calls. -/

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

/-! ### Module-Aware Refinement (`RefinementEnv`) with Helper Function Calls -/

open scoped LeanNanoLlvm.AST.Syntax in
def helperId32Def : AST.Definition := [llvm-definition|
  define i32 @id32(i32 %v) {
  entry:
    ret i32 %v
  }
]

def helperId32Env : RefinementEnv :=
  RefinementEnv.ofTopLevel ⟨[.definition helperId32Def]⟩

open scoped LeanNanoLlvm.AST.Syntax in
def callerWithAdd0Def : AST.Definition := [llvm-definition|
  define i32 @caller(i32 %x) {
  entry:
    %y = add i32 %x, 0
    %r = call i32 @id32(i32 %y)
    ret i32 %r
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
def callerDirectDef : AST.Definition := [llvm-definition|
  define i32 @caller(i32 %x) {
  entry:
    %r = call i32 @id32(i32 %x)
    ret i32 %r
  }
]

/-- Module-aware refinement: simplifying an argument before calling module helper `@id32`. -/
theorem caller_add0_is_refined_by_direct_in_module :
    callerWithAdd0Def ⊒⟨helperId32Env⟩ callerDirectDef := by
  refine ⟨rfl, ?_⟩
  intro initMem args _ hargs
  rcases args with _ | ⟨arg, _ | _⟩
  · llvm_wf [callerWithAdd0Def] at hargs
  · cases arg <;> llvm_wf [callerWithAdd0Def] at hargs
    subst hargs
    rename_i v
    have hinitX : initCallConfig .modern .default64LE initMem helperId32Env.fns helperId32Env.decls
        callerWithAdd0Def [.bv 32 v] =
      .running {
        frames := [{ defn := callerWithAdd0Def, curBlock := .name "entry",
                     remainingCode := entryCode callerWithAdd0Def,
                     terminator := entryTerm callerWithAdd0Def,
                     registers := (∅ : AssocMap AST.Identifier RegisterValue).insert
                       (.local_id (.name "x")) (.bv 32 v) }]
        memory := initMem, config := .modern, dataLayout := .default64LE,
        functions := helperId32Env.fns, declarations := helperId32Env.decls } := rfl
    have hinitY : initCallConfig .modern .default64LE initMem helperId32Env.fns helperId32Env.decls
        callerDirectDef [.bv 32 v] =
      .running {
        frames := [{ defn := callerDirectDef, curBlock := .name "entry",
                     remainingCode := entryCode callerDirectDef,
                     terminator := entryTerm callerDirectDef,
                     registers := (∅ : AssocMap AST.Identifier RegisterValue).insert
                       (.local_id (.name "x")) (.bv 32 v) }]
        memory := initMem, config := .modern, dataLayout := .default64LE,
        functions := helperId32Env.fns, declarations := helperId32Env.decls } := rfl
    change Config.IsRefinedBy initMem.allocIds
      (initCallConfig .modern .default64LE initMem helperId32Env.fns helperId32Env.decls callerWithAdd0Def [.bv 32 v])
      (initCallConfig .modern .default64LE initMem helperId32Env.fns helperId32Env.decls callerDirectDef [.bv 32 v])
    rw [hinitX, hinitY]
    have haddVal : liftBinaryPure (.int 32) (.bv 32 v) (.bv 32 (.value 0#32))
        (evalIntBinaryScalarPure (.add false false)) = .ok (.bv 32 v) := by
      cases v using PoisonOr.casesOn' with
      | poison => llvm_simp
      | value bv => llvm_simp
    have hlookupId : helperId32Env.fns.get? (.name "id32") = some helperId32Def := rfl
    have hmkCallee : mkCallEntryFrameWithMem .default64LE .modern initMem (.ret (.int 32)) [[]] helperId32Def [.bv 32 v] =
      .ok ({ defn := helperId32Def, curBlock := .name "entry", remainingCode := [],
             terminator := entryTerm helperId32Def,
             registers := (∅ : AssocMap AST.Identifier RegisterValue).insert
               (.local_id (.name "v")) (.bv 32 v) }, initMem) := rfl
    -- Source execution: `add` → `call @id32` → callee `ret` → caller `ret`
    have hnoIntr : ∀ cfg mem o b a, evalNonAllocIntrinsicExec? .default64LE cfg mem
        (AST.RawId.name "id32").toString (.ret (.int 32)) {} [.bv 32 v] o b a = none :=
      fun _ _ _ b _ => by cases b <;> rfl
    have hX_term : Terminates (.running {
        frames := [{ defn := callerWithAdd0Def, curBlock := .name "entry",
                     remainingCode := entryCode callerWithAdd0Def,
                     terminator := entryTerm callerWithAdd0Def,
                     registers := (∅ : AssocMap AST.Identifier RegisterValue).insert
                       (.local_id (.name "x")) (.bv 32 v) }]
        memory := initMem, config := .modern, dataLayout := .default64LE,
        functions := helperId32Env.fns, declarations := helperId32Env.decls })
        [] (.bv 32 v) initMem :=
      StarStep.step (ev := none)
        (Step.instr rfl rfl
          (StepInstr.intBinaryOp_ok
            (EvalExp.leaf_ok (by llvm_step))
            (EvalExp.leaf_ok (by llvm_step))
            haddVal))
        (StarStep.step (ev := none)
          (Step.instr rfl rfl
            (StepInstr.call_user_ok
              (EvalCallArgs.cons_ok (EvalExp.leaf_ok (by llvm_step; rfl)) (by simp only [byvalDeferredAttrs_nil]; llvm_step) EvalCallArgs.nil)
              EvalCallee.direct rfl (fun o => hnoIntr _ _ o _ _) hlookupId (Or.inr (by simp [SemanticsConfig.modern])) hmkCallee))
          (StarStep.step (ev := none)
            (Step.term rfl rfl rfl
              (StepTerm.ret_ok rfl (EvalExp.leaf_ok (by llvm_step; rfl))
                (StepRet.call_ok (rd := { destId := .id (.name "r"), retTy := .ret (.int 32), fmf := {}, retAttrs := [] })
                  rfl (by llvm_step [helperId32Def]; rfl) rfl rfl (by llvm_step; rfl))))
            (StarStep.step (ev := none)
              (Step.term rfl rfl rfl
                (StepTerm.ret_ok rfl (EvalExp.leaf_ok (by llvm_step; rfl))
                  (StepRet.top_ok rfl (by llvm_step [callerWithAdd0Def]))))
              (StarStep.refl _))))
    -- Target deterministic 3-step execution: `call @id32` → callee `ret` → caller `ret`
    have hY3 := det_step_to_halted (st := {
        frames := [{ defn := callerDirectDef, curBlock := .name "entry", remainingCode := [],
                     terminator := entryTerm callerDirectDef,
                     registers := ((∅ : AssocMap AST.Identifier RegisterValue).insert
                       (.local_id (.name "x")) (.bv 32 v)).insert
                       (.local_id (.name "r")) (.bv 32 v) }]
        memory := initMem, config := .modern, dataLayout := .default64LE,
        functions := helperId32Env.fns, declarations := helperId32Env.decls })
      (v := .bv 32 v) (m := initMem) fun ev c' => by
        rw [Step.ret_top_leaf_iff rfl rfl rfl rfl (v := .bv 32 v) (by llvm_step)]
        llvm_step [callerDirectDef]
    have hY2 := det_step_chain (st := {
        frames := [
          { defn := helperId32Def, curBlock := .name "entry", remainingCode := [],
            terminator := entryTerm helperId32Def,
            registers := (∅ : AssocMap AST.Identifier RegisterValue).insert
              (.local_id (.name "v")) (.bv 32 v) },
          { defn := callerDirectDef, curBlock := .name "entry", remainingCode := [],
            terminator := entryTerm callerDirectDef,
            registers := (∅ : AssocMap AST.Identifier RegisterValue).insert
              (.local_id (.name "x")) (.bv 32 v),
            returnDest? := some { destId := .id (.name "r"), retTy := .ret (.int 32), fmf := {}, retAttrs := [] } }]
        memory := initMem, config := .modern, dataLayout := .default64LE,
        functions := helperId32Env.fns, declarations := helperId32Env.decls })
      (fun ev c' => by
        constructor
        · intro hs
          rw [Step.term_iff rfl rfl rfl] at hs
          obtain ⟨rfl, hs⟩ := hs
          cases hs with
          | ret_ok hrt he hsr =>
            rw [EvalExp.leaf_iff (by llvm_step; rfl)] at he
            injection he with hpair; cases hpair
            cases hsr with
            | top_ok hnil => cases hnil
            | call_ok hcons h1 hrd _ h2 =>
              cases hcons
              simp only [freeAllocaList, applyRetFMFAndAttrsPure, applyValueAttrsPure, applyValueAttrsSeq, reduceOrderValueAttrs, helperId32Def] at h1
              injection h1 with hv1; subst hv1
              injection hrd with hrd'; subst hrd'
              simp only [finishCallerReturn, applyRetFMFAndAttrsPure, applyValueAttrsPure, applyValueAttrsSeq, reduceOrderValueAttrs] at h2
              injection h2 with hv2; subst hv2
              exact ⟨rfl, rfl⟩
            | noreturn_ub hcons _ hrd hnr =>
              cases hcons; injection hrd with hrd'; subst hrd'
              simp [helperId32Def] at hnr
            | callee_attr_err h1 =>
              simp only [freeAllocaList, applyRetFMFAndAttrsPure, applyValueAttrsPure, applyValueAttrsSeq, reduceOrderValueAttrs, helperId32Def] at h1
              cases h1
            | caller_attr_err hcons h1 hrd _ h2 =>
              cases hcons
              simp only [freeAllocaList, applyRetFMFAndAttrsPure, applyValueAttrsPure, applyValueAttrsSeq, reduceOrderValueAttrs, helperId32Def] at h1
              injection h1 with hv1; subst hv1
              injection hrd with hrd'; subst hrd'
              simp only [finishCallerReturn, applyRetFMFAndAttrsPure, applyValueAttrsPure, applyValueAttrsSeq, reduceOrderValueAttrs] at h2
              cases h2
            | missing_dest hcons _ hrd =>
              cases hcons; cases hrd
          | ret_exp_err _ he =>
            rw [EvalExp.leaf_iff (by llvm_step; rfl)] at he; cases he
          | ret_ty_err hty => exact absurd rfl hty
        · rintro ⟨rfl, rfl⟩
          exact Step.term rfl rfl rfl
            (StepTerm.ret_ok rfl (EvalExp.leaf_ok (by llvm_step; rfl))
              (StepRet.call_ok (rd := { destId := .id (.name "r"), retTy := .ret (.int 32), fmf := {}, retAttrs := [] })
                rfl (by llvm_step [helperId32Def]; rfl) rfl rfl (by simp [finishCallerReturn, applyRetFMFAndAttrsPure, applyValueAttrsPure, applyValueAttrsSeq, reduceOrderValueAttrs]))))
      hY3
    have hY1 := det_step_chain (st := {
        frames := [{ defn := callerDirectDef, curBlock := .name "entry",
                     remainingCode := entryCode callerDirectDef,
                     terminator := entryTerm callerDirectDef,
                     registers := (∅ : AssocMap AST.Identifier RegisterValue).insert
                       (.local_id (.name "x")) (.bv 32 v) }]
        memory := initMem, config := .modern, dataLayout := .default64LE,
        functions := helperId32Env.fns, declarations := helperId32Env.decls })
      (fun ev c' => by
        constructor
        · intro hs
          rw [Step.instr_iff rfl rfl] at hs
          cases hs with
          | call_args_err hargsEv =>
            cases hargsEv with
            | cons_exp_err he => rw [EvalExp.leaf_iff (by llvm_step; rfl)] at he; cases he
            | cons_attr_err he ha =>
              rw [EvalExp.leaf_iff (by llvm_step; rfl)] at he
              injection he with hpair; cases hpair
              simp only [byvalDeferredAttrs_nil, applyValueAttrsPure, applyValueAttrsSeq, reduceOrderValueAttrs] at ha; cases ha
            | cons_tail_err he ha hrest =>
              rw [EvalExp.leaf_iff (by llvm_step; rfl)] at he
              injection he with hpair; cases hpair
              cases hrest
          | call_callee_err _ hcallee =>
            cases hcallee with
            | indirect_exp_err hne _ | indirect_poison hne _
            | indirect_bad_addr hne _ _ | indirect_nonptr hne _ _ =>
              exact absurd rfl (hne (.name "id32"))
          | call_alloc_ok _ hcallee halloc _ _ | call_alloc_retattr_err _ hcallee halloc _ _
          | call_alloc_err _ hcallee halloc _ =>
            cases hcallee with
            | direct => cases halloc
            | indirect_ok hne _ _ => exact absurd rfl (hne (.name "id32"))
          | call_spec_oracle_ok _ hcallee _ hspec _ _ | call_spec_oracle_entry_err _ hcallee _ hspec _ _
          | call_spec_oracle_overflow _ hcallee _ hspec _ _ =>
            cases hcallee with
            | direct =>
              have hf : strHasPrefix "id32" "llvm.speculative.load" = false := rfl
              simp [specLoadOracleCall?, AST.RawId.toString, hf] at hspec
            | indirect_ok hne _ _ => exact absurd rfl (hne (.name "id32"))
          | call_intrinsic_ok hargsEv hcallee _ hintr _ _ | call_intrinsic_bundle_err hargsEv hcallee _ hintr _
          | call_intrinsic_retattr_err hargsEv hcallee _ hintr _ _ =>
            cases hcallee with
            | direct =>
              cases hargsEv with
              | cons_ok he ha hrest =>
                rw [EvalExp.leaf_iff (by llvm_step; rfl)] at he
                injection he with hpair; cases hpair
                simp only [byvalDeferredAttrs_nil, applyValueAttrsPure, applyValueAttrsSeq, reduceOrderValueAttrs] at ha; injection ha with hv; subst hv
                cases hrest
                obtain ⟨o, _, h⟩ := hintr; rw [hnoIntr _ _ o _ _] at h; cases h
            | indirect_ok hne _ _ => exact absurd rfl (hne (.name "id32"))
          | call_intrinsic_err hargsEv hcallee _ hintr =>
            cases hcallee with
            | direct =>
              cases hargsEv with
              | cons_ok he ha hrest =>
                rw [EvalExp.leaf_iff (by llvm_step; rfl)] at he
                injection he with hpair; cases hpair
                simp only [byvalDeferredAttrs_nil, applyValueAttrsPure, applyValueAttrsSeq, reduceOrderValueAttrs] at ha; injection ha with hv; subst hv
                cases hrest
                obtain ⟨o, h⟩ := hintr; rw [hnoIntr _ _ o _ _] at h; cases h
            | indirect_ok hne _ _ => exact absurd rfl (hne (.name "id32"))
          | call_user_ok hargsEv hcallee _ _ hfn _ hmk =>
            cases hcallee with
            | direct =>
              cases hargsEv with
              | cons_ok he ha hrest =>
                rw [EvalExp.leaf_iff (by llvm_step; rfl)] at he
                injection he with hpair; cases hpair
                simp only [byvalDeferredAttrs_nil, applyValueAttrsPure, applyValueAttrsSeq, reduceOrderValueAttrs] at ha; injection ha with hv; subst hv
                cases hrest
                rw [hlookupId] at hfn; injection hfn with hdef; subst hdef
                dsimp only [List.map, tailHidden, MemoryState.hide, AST.CallSiteInfo.default] at hmk
                rw [hmkCallee] at hmk; injection hmk with hpair; cases hpair
                exact ⟨rfl, rfl⟩
            | indirect_ok hne _ _ => exact absurd rfl (hne (.name "id32"))
          | call_user_entry_err hargsEv hcallee _ _ hfn _ hmk =>
            cases hcallee with
            | direct =>
              cases hargsEv with
              | cons_ok he ha hrest =>
                rw [EvalExp.leaf_iff (by llvm_step; rfl)] at he
                injection he with hpair; cases hpair
                simp only [byvalDeferredAttrs_nil, applyValueAttrsPure, applyValueAttrsSeq, reduceOrderValueAttrs] at ha; injection ha with hv; subst hv
                cases hrest
                rw [hlookupId] at hfn; injection hfn with hdef; subst hdef
                dsimp only [List.map, tailHidden, MemoryState.hide, AST.CallSiteInfo.default] at hmk
                rw [hmkCallee] at hmk; cases hmk
            | indirect_ok hne _ _ => exact absurd rfl (hne (.name "id32"))
          | call_user_overflow _ _ _ _ _ _ hge => simp [SemanticsConfig.modern] at hge
          | call_external_err _ hcallee _ _ hfn =>
            cases hcallee with
            | direct => rw [hlookupId] at hfn; cases hfn
            | indirect_ok hne _ _ => exact absurd rfl (hne (.name "id32"))
        · rintro ⟨rfl, rfl⟩
          exact Step.instr rfl rfl
            (StepInstr.call_user_ok
              (EvalCallArgs.cons_ok (EvalExp.leaf_ok (by llvm_step; rfl)) (by simp only [byvalDeferredAttrs_nil]; llvm_step) EvalCallArgs.nil)
              EvalCallee.direct rfl (fun o => hnoIntr _ _ o _ _) hlookupId (Or.inr (by simp [SemanticsConfig.modern])) hmkCallee))
      hY2
    exact Config.IsRefinedBy.of_det_halted hY1 hX_term
      (RegisterValue.IsRefinedBy.refl _)
      (MemoryState.IsRefinedBy.refl _ _)
  · llvm_wf [callerWithAdd0Def] at hargs

end LeanNanoLlvm.Refinement
