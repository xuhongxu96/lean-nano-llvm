import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import LeanNanoLlvm.AST.Unexpander
import Tests.Refinement.Helpers

/-! Refinement tests: optional `undef` refinement (`SemanticsConfig.withUndef`). -/

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

/-! ### Optional `undef` Refinement (Explicitly Enabled via `SemanticsConfig.withUndef`) -/

private theorem bitvec_double_eq_mul_two_generic {w : Nat} (b : BitVec w) :
    b + b = b * (2 : BitVec w) := by
  apply BitVec.eq_of_toFin_eq
  apply Fin.ext
  simp [Fin.val_add, Fin.val_mul, BitVec.toFin_ofNat]
  rw [← Nat.two_mul b.toNat, Nat.mul_comm]

private theorem bitvec_mul_two_ne_one_generic {w : Nat} (hpos : 0 < w) (b : BitVec w) :
    b * (2#w) ≠ 1#w := by
  intro h
  have hval :
      (((b * (2#w)).toFin : Fin (2 ^ w)) : Nat) =
        (((1#w).toFin : Fin (2 ^ w)) : Nat) := by
    simp_all
  simp [Fin.val_mul, BitVec.toFin_ofNat] at hval
  have hmod := congrArg (fun n => n % 2) hval
  have hright : (1 % 2 ^ w) % 2 = 1 := by
    cases w with
    | zero => cases Nat.not_lt_zero _ hpos
    | succ n => simp
  simp [hright] at hmod

theorem undefValRel_int_iff {dl cfg w v} :
    UndefValRel dl cfg (.int w) v ↔
      ∃ bv : BitVec w, v = .bv w (.value bv) ∧ (cfg.undefMode = .zero → bv = 0#w) := by
  constructor
  · intro hu
    cases hu with
    | int _ bits hz => exact ⟨bits, rfl, hz⟩
  · rintro ⟨bv, rfl, hz⟩
    exact UndefValRel.int w bv hz

open scoped LeanNanoLlvm.AST.Syntax in
def undefAddDefGeneric (w : Nat) : AST.Definition := [llvm-definition|
  define i$(w) @f() {
    entry:
      %x = add i$(w) undef, undef
      ret i$(w) %x
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
def undefMul2DefGeneric (w : Nat) : AST.Definition := [llvm-definition|
  define i$(w) @f() {
    entry:
      %x = mul i$(w) undef, 2
      ret i$(w) %x
  }
]

abbrev undefAddDef : AST.Definition := undefAddDefGeneric 1
abbrev undefMul2Def : AST.Definition := undefMul2DefGeneric 1
abbrev undefAddDef8 : AST.Definition := undefAddDefGeneric 8
abbrev undefMul2Def8 : AST.Definition := undefMul2DefGeneric 8

private theorem step_mul_undef_2_inv (w : Nat) (initMem : MemoryState) :
    ∀ ev c', Step (initCallConfig .withUndef .default64LE initMem ∅ ∅ (undefMul2DefGeneric w) []) ev c' →
      ev = none ∧ ∃ b : BitVec w,
        c' = .running {
          frames := [{
            defn := undefMul2DefGeneric w
            curBlock := .name "entry"
            remainingCode := []
            terminator := entryTerm (undefMul2DefGeneric w)
            registers := (∅ : AssocMap AST.Identifier RegisterValue).insert
              (.local_id (.name "x")) (.bv w (.value (b * BitVec.ofInt w 2)))
          }]
          memory := initMem
          config := .withUndef
          dataLayout := .default64LE
        } := by
  intro ev c' hs
  rw [initCallConfig_0 .withUndef .default64LE initMem (undefMul2DefGeneric w) rfl rfl rfl rfl] at hs
  rw [Step.instr_iff rfl rfl] at hs
  cases hs with
  | intBinaryOp_e1_err he1 =>
    rw [EvalExp.undef_iff (by rfl) (by rfl)] at he1
    obtain ⟨_, h, _⟩ := he1; cases h
  | intBinaryOp_e2_err he1 he2 =>
    rw [EvalExp.undef_iff (by rfl) (by rfl)] at he1
    obtain ⟨_, h1, _⟩ := he1; cases h1
    rw [EvalExp.leaf_iff (v := .bv w (.value (BitVec.ofInt w 2))) (by simp [evalPureLeafExp?])] at he2
    cases he2
  | intBinaryOp_eval_err he1 he2 hbin =>
    rw [EvalExp.undef_iff (by rfl) (by rfl)] at he1
    obtain ⟨v1, h1, hu1⟩ := he1; cases h1
    obtain ⟨b, rfl, _⟩ := undefValRel_int_iff.mp hu1
    rw [EvalExp.leaf_iff (v := .bv w (.value (BitVec.ofInt w 2))) (by simp [evalPureLeafExp?])] at he2
    cases he2
    llvm_simp at hbin
  | intBinaryOp_ok he1 he2 hbin =>
    rw [EvalExp.undef_iff (by rfl) (by rfl)] at he1
    obtain ⟨v1, h1, hu1⟩ := he1; cases h1
    obtain ⟨b, rfl, _⟩ := undefValRel_int_iff.mp hu1
    rw [EvalExp.leaf_iff (v := .bv w (.value (BitVec.ofInt w 2))) (by simp [evalPureLeafExp?])] at he2
    cases he2
    llvm_simp at hbin
    subst hbin
    exact ⟨rfl, b, rfl⟩

private theorem step_mul_undef_2_ret (w : Nat) (initMem : MemoryState) (b : BitVec w) :
    ∀ ev c',
      Step (.running {
        frames := [{
          defn := undefMul2DefGeneric w
          curBlock := .name "entry"
          remainingCode := []
          terminator := entryTerm (undefMul2DefGeneric w)
          registers := (∅ : AssocMap AST.Identifier RegisterValue).insert
            (.local_id (.name "x")) (.bv w (.value (b * BitVec.ofInt w 2)))
        }]
        memory := initMem
        config := .withUndef
        dataLayout := .default64LE
      }) ev c' ↔
      ev = none ∧ c' = .halted (.bv w (.value (b * BitVec.ofInt w 2))) initMem := by
  intro ev c'
  rw [Step.ret_top_leaf_iff rfl rfl rfl rfl
    (v := .bv w (.value (b * BitVec.ofInt w 2)))
    (by llvm_step)]
  rfl

theorem undef_add_is_refined_by_undef_mul2_generic (w : Nat) :
    undefAddDefGeneric w ⊒[SemanticsConfig.withUndef] undefMul2DefGeneric w := by
  refine ⟨rfl, ?_⟩
  intro initMem args _ hargs
  cases args with
  | cons _ _ =>
    llvm_wf [undefAddDefGeneric] at hargs
  | nil =>
    right
    have hstep1 := step_mul_undef_2_inv w initMem
    refine ⟨?_, ?_, ?_⟩
    · rintro (⟨tr, msg, hstar⟩ | ⟨tr, err, hstar⟩)
      · cases hstar with
        | step hs hrest =>
          obtain ⟨rfl, b, rfl⟩ := hstep1 _ _ hs
          exact (det_step_to_halted (step_mul_undef_2_ret w initMem b)).1 (Or.inl ⟨_, msg, hrest⟩)
      · cases hstar with
        | step hs hrest =>
          obtain ⟨rfl, b, rfl⟩ := hstep1 _ _ hs
          exact (det_step_to_halted (step_mul_undef_2_ret w initMem b)).1 (Or.inr ⟨_, err, hrest⟩)
    · intro trY retY memY htY
      cases htY with
      | step hs hrest =>
        obtain ⟨rfl, b, rfl⟩ := hstep1 _ _ hs
        obtain ⟨rfl, rfl, hmemEq⟩ := (det_step_to_halted (step_mul_undef_2_ret w initMem b)).2.2 _ _ _ hrest
        rw [hmemEq]
        have hmulEq : b + b = b * BitVec.ofInt w 2 := by
          simpa using bitvec_double_eq_mul_two_generic b
        have hTermX : Terminates (initCallConfig .withUndef .default64LE initMem ∅ ∅ (undefAddDefGeneric w) [])
            [] (.bv w (.value (b * BitVec.ofInt w 2))) initMem := by
          rw [← hmulEq, initCallConfig_0 .withUndef .default64LE initMem (undefAddDefGeneric w) rfl rfl rfl rfl]
          refine StarStep.step (ev := none)
            (Step.instr rfl rfl (StepInstr.intBinaryOp_ok
              (EvalExp.undef_ok rfl (UndefValRel.int w b (by intro h; cases h)))
              (EvalExp.undef_ok rfl (UndefValRel.int w b (by intro h; cases h)))
              (by llvm_simp; rfl)))
            (StarStep.step (ev := none)
              (Step.term rfl rfl rfl
                (StepTerm.ret_ok rfl
                  (EvalExp.leaf_ok (by llvm_step; rfl))
                  (StepRet.top_ok rfl (by llvm_step [undefAddDefGeneric]))))
              (StarStep.refl _))
        exact ⟨[], .bv w (.value (b * BitVec.ofInt w 2)), initMem, .id,
          MemoryInjection.id_idOn _, hTermX, trivial,
          RegisterValue.IsRefinedBy.refl _, MemoryState.IsRefinedBy.refl _ _⟩
    · intro hdiv
      obtain ⟨ev, c1, hs, hdiv1⟩ := Diverges.step_inv hdiv
      obtain ⟨rfl, b, rfl⟩ := hstep1 ev c1 hs
      exact False.elim ((det_step_to_halted (step_mul_undef_2_ret w initMem b)).2.1 hdiv1)

theorem undef_mul2_is_not_refined_by_undef_add_generic (w : Nat) (hpos : 0 < w) :
    ¬ (undefMul2DefGeneric w ⊒[SemanticsConfig.withUndef] undefAddDefGeneric w) := by
  rintro ⟨_, hbeh⟩
  have hstep1 := step_mul_undef_2_inv w {}
  have hinst := hbeh {} [] MemoryState.empty_wf
    (by llvm_wf [undefMul2DefGeneric])
  rcases hinst with habortX | ⟨_, hterm, _⟩
  · rcases habortX with ⟨tr, msg, hstar⟩ | ⟨tr, err, hstar⟩
    · cases hstar with
      | step hs hrest =>
        obtain ⟨rfl, b, rfl⟩ := hstep1 _ _ hs
        exact (det_step_to_halted (step_mul_undef_2_ret w {} b)).1 (Or.inl ⟨_, msg, hrest⟩)
    · cases hstar with
      | step hs hrest =>
        obtain ⟨rfl, b, rfl⟩ := hstep1 _ _ hs
        exact (det_step_to_halted (step_mul_undef_2_ret w {} b)).1 (Or.inr ⟨_, err, hrest⟩)
  · have hTermY : Terminates (initCallConfig .withUndef .default64LE {} ∅ ∅ (undefAddDefGeneric w) [])
        [] (.bv w (.value (1#w))) {} := by
      rw [initCallConfig_0 .withUndef .default64LE {} (undefAddDefGeneric w) rfl rfl rfl rfl]
      refine StarStep.step (ev := none)
        (Step.instr rfl rfl (StepInstr.intBinaryOp_ok
          (EvalExp.undef_ok rfl (UndefValRel.int w (1#w) (by intro h; cases h)))
          (EvalExp.undef_ok rfl (UndefValRel.int w (0#w) (by intro h; cases h)))
          (by llvm_simp; rfl)))
        (StarStep.step (ev := none)
          (Step.term rfl rfl rfl
            (StepTerm.ret_ok rfl
              (EvalExp.leaf_ok (by llvm_step; rfl))
              (StepRet.top_ok rfl (by llvm_step [undefAddDefGeneric]))))
          (StarStep.refl _))
    obtain ⟨trX, retX, memX, inj, _, hTermX, _, hvalRef, _⟩ := hterm [] _ {} hTermY
    cases hTermX with
    | step hs hrest =>
      obtain ⟨rfl, b, rfl⟩ := hstep1 _ _ hs
      obtain ⟨rfl, rfl, rfl⟩ := (det_step_to_halted (step_mul_undef_2_ret w {} b)).2.2 _ _ _ hrest
      simp [RegisterValue.IsRefinedBy] at hvalRef
      exact bitvec_mul_two_ne_one_generic hpos b (by simpa using hvalRef)

theorem undef_add_is_refined_by_undef_mul2 :
    undefAddDef ⊒[SemanticsConfig.withUndef] undefMul2Def :=
  undef_add_is_refined_by_undef_mul2_generic 1

theorem undef_mul2_is_not_refined_by_undef_add :
    ¬ (undefMul2Def ⊒[SemanticsConfig.withUndef] undefAddDef) :=
  undef_mul2_is_not_refined_by_undef_add_generic 1 (by omega)

theorem undef_add_is_refined_by_undef_mul2_i8 :
    undefAddDef8 ⊒[SemanticsConfig.withUndef] undefMul2Def8 :=
  undef_add_is_refined_by_undef_mul2_generic 8

theorem undef_mul2_is_not_refined_by_undef_add_i8 :
    ¬ (undefMul2Def8 ⊒[SemanticsConfig.withUndef] undefAddDef8) :=
  undef_mul2_is_not_refined_by_undef_add_generic 8 (by omega)

end LeanNanoLlvm.Refinement
