import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax
import LeanNanoLlvm.AST.Unexpander

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

private def entryTerm (d : AST.Definition) : AST.InstructionId × AST.Terminator :=
  match d.blocks with
  | b :: _ => b.terminator
  | [] => (.void 0, .unreachable)

private def entryCode (d : AST.Definition) : AST.Code :=
  match d.blocks with
  | b :: _ => b.code
  | [] => []

private theorem initCallConfig_0 (cfg : SemanticsConfig) (dl : AST.DataLayout)
    (mem : MemoryState) (defn : AST.Definition) {retTy : AST.LlvmRetType}
    {bid : AST.BlockId} {code body : AST.Code} {term : AST.InstructionId × AST.Terminator}
    (ht : defn.prototype.type = .function retTy [] false)
    (ha : defn.args = [])
    (hb : defn.blocks = [{ id := bid, code := code, terminator := term }])
    (hcode : splitPhis code = ([], body)) :
    initCallConfig cfg dl mem ∅ ∅ defn [] =
      .running {
        frames := [{ defn := defn, curBlock := bid, remainingCode := body,
                     terminator := term, registers := ∅ }]
        memory := mem, config := cfg, dataLayout := dl } := by
  simp only [initCallConfig, mkEntryFrameWithMem, mkEntryFrame, bindFrameArgs, bindFrameArgs.go,
             applyByValCopies, applyByValCopies.go,
             ht, ha, hb, hcode, List.length_nil, bne_self_eq_false, Bool.false_or,
             Bool.false_eq_true, ↓reduceIte, ite_self, List.isEmpty_nil, Bool.not_true]

private theorem initCallConfig_1 (cfg : SemanticsConfig) (dl : AST.DataLayout)
    (mem : MemoryState) (defn : AST.Definition) {retTy : AST.LlvmRetType}
    {pTy : AST.LlvmType} {pId : AST.LocalId}
    {bid : AST.BlockId} {code body : AST.Code} {term : AST.InstructionId × AST.Terminator}
    {arg : RegisterValue}
    (ht : defn.prototype.type = .function retTy [pTy] false)
    (hpa : defn.prototype.argAttrs = [[]] ∨ defn.prototype.argAttrs = [])
    (ha : defn.args = [pId])
    (hb : defn.blocks = [{ id := bid, code := code, terminator := term }])
    (hcode : splitPhis code = ([], body))
    (hm : arg.matchesType pTy = true) :
    initCallConfig cfg dl mem ∅ ∅ defn [arg] =
      .running {
        frames := [{ defn := defn, curBlock := bid, remainingCode := body,
                     terminator := term,
                     registers := (∅ : AssocMap AST.Identifier RegisterValue).insert (.local_id pId) arg }]
        memory := mem, config := cfg, dataLayout := dl } := by
  rcases hpa with hpa | hpa <;>
  (simp only [initCallConfig, mkEntryFrameWithMem, mkEntryFrame, bindFrameArgs, bindFrameArgs.go,
             applyByValCopies, ht, hpa, ha, hb, hcode, hm,
             List.length_nil, List.length_cons, List.any_nil, List.any_cons, Bool.or_self,
             bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.isEmpty_nil, Bool.not_true]; rfl)

private theorem initCallConfig_2 (cfg : SemanticsConfig) (dl : AST.DataLayout)
    (mem : MemoryState) (defn : AST.Definition) {retTy : AST.LlvmRetType}
    {pTy1 pTy2 : AST.LlvmType} {pId1 pId2 : AST.LocalId}
    {bid : AST.BlockId} {code body : AST.Code} {term : AST.InstructionId × AST.Terminator}
    {arg1 arg2 : RegisterValue}
    (ht : defn.prototype.type = .function retTy [pTy1, pTy2] false)
    (hpa : defn.prototype.argAttrs = [[], []] ∨ defn.prototype.argAttrs = [])
    (ha : defn.args = [pId1, pId2])
    (hb : defn.blocks = [{ id := bid, code := code, terminator := term }])
    (hcode : splitPhis code = ([], body))
    (hm1 : arg1.matchesType pTy1 = true)
    (hm2 : arg2.matchesType pTy2 = true) :
    initCallConfig cfg dl mem ∅ ∅ defn [arg1, arg2] =
      .running {
        frames := [{ defn := defn, curBlock := bid, remainingCode := body,
                     terminator := term,
                     registers := ((∅ : AssocMap AST.Identifier RegisterValue).insert
                       (.local_id pId1) arg1).insert (.local_id pId2) arg2 }]
        memory := mem, config := cfg, dataLayout := dl } := by
  rcases hpa with hpa | hpa <;>
  (simp only [initCallConfig, mkEntryFrameWithMem, mkEntryFrame, bindFrameArgs, bindFrameArgs.go,
             applyByValCopies, ht, hpa, ha, hb, hcode, hm1, hm2,
             List.length_nil, List.length_cons, List.any_nil, List.any_cons, Bool.or_self,
             bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.isEmpty_nil, Bool.not_true]; rfl)

/-! ### 1. Basic Arithmetic, Reflexivity & Width-Generic Refinement (`i$(w)`) -/

open scoped LeanNanoLlvm.AST.Syntax in
def addDef : AST.Definition := [llvm-definition|
  define i8 @f(i8 %a, i8 %b) {
  entry:
    %x = add i8 %a, %b
    ret i8 %x
  }
]

theorem addDef_is_refined_by_itself : addDef ⊒ addDef :=
  Definition.IsRefinedBy.refl addDef

open scoped LeanNanoLlvm.AST.Syntax in
def retXDef (w : Nat) : AST.Definition := [llvm-definition|
  define i$(w) @f(i$(w) %x) {
  entry:
    ret i$(w) %x
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
def retAddX0Def (w : Nat) : AST.Definition := [llvm-definition|
  define i$(w) @f(i$(w) %x) {
  entry:
    %x = add i$(w) %x, 0
    ret i$(w) %x
  }
]

theorem ret_add_x_0_is_refined_by_ret_x_generic (w : Nat) :
    retAddX0Def w ⊒ retXDef w := by
  refine ⟨rfl, ?_⟩
  intro initMem args _ hargs
  rcases args with _ | ⟨arg, _ | _⟩
  · llvm_wf [retAddX0Def] at hargs
  · cases arg <;>
      llvm_wf [retAddX0Def] at hargs
    subst hargs
    rename_i v
    have hm : (RegisterValue.bv w v).matchesType (.int w) = true := by
      simp [RegisterValue.matchesType]
    rw [initCallConfig_1 .modern .default64LE initMem (retXDef w) rfl (Or.inl rfl) rfl rfl rfl hm]
    rw [initCallConfig_1 .modern .default64LE initMem (retAddX0Def w) rfl (Or.inl rfl) rfl rfl rfl hm]
    have haddVal : liftBinaryPure (.int w) (.bv w v) (.bv w (.value (BitVec.ofInt w 0)))
        (evalIntBinaryScalarPure (.add false false)) = .ok (.bv w v) := by
      cases v using PoisonOr.casesOn' with
      | poison => llvm_simp
      | value bv => llvm_simp
    refine Config.IsRefinedBy.of_det_halted
      (det_step_to_halted fun ev c' => by
        rw [Step.ret_top_leaf_iff rfl rfl rfl rfl (v := .bv w v) (by llvm_step)]
        rfl)
      (StarStep.step (ev := none)
        (Step.instr rfl rfl
          (StepInstr.intBinaryOp_ok
            (EvalExp.leaf_ok (by llvm_step))
            (EvalExp.leaf_ok (by simp [evalPureLeafExp?]))
            haddVal))
        (StarStep.step (ev := none)
          (Step.term rfl rfl rfl
            (StepTerm.ret_ok rfl
              (EvalExp.leaf_ok (by llvm_step; rfl))
              (StepRet.top_ok rfl (by llvm_step [retAddX0Def]))))
          (StarStep.refl _)))
      (RegisterValue.IsRefinedBy.refl _)
      (MemoryState.IsRefinedBy.refl _ _)
  · llvm_wf [retAddX0Def] at hargs

theorem ret_add_x_0_is_refined_by_ret_x :
    retAddX0Def 8 ⊒ retXDef 8 :=
  ret_add_x_0_is_refined_by_ret_x_generic 8

/-! ### 2. Optional `undef` Refinement (Explicitly Enabled via `SemanticsConfig.withUndef`) -/

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

private theorem undefValRel_int_iff {dl cfg w v} :
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

/-! ### 3. Poison Refinement -/

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

private theorem zeroDef_det (cfg : SemanticsConfig) (initMem : MemoryState) :
    ∀ ev c', Step (initCallConfig cfg .default64LE initMem ∅ ∅ zeroDef []) ev c' ↔
      ev = none ∧ c' = .halted (.bv 8 (.value (0 : BitVec 8))) initMem := by
  intro ev c'
  rw [initCallConfig_0 cfg .default64LE initMem zeroDef rfl rfl rfl rfl]
  rw [Step.ret_top_leaf_iff rfl rfl rfl rfl (v := .bv 8 (.value (0 : BitVec 8))) (by simp [evalPureLeafExp?])]
  rfl

private theorem poisonDef_det (cfg : SemanticsConfig) (initMem : MemoryState) :
    ∀ ev c', Step (initCallConfig cfg .default64LE initMem ∅ ∅ poisonDef []) ev c' ↔
      ev = none ∧ c' = .halted (.bv 8 .poison) initMem := by
  intro ev c'
  rw [initCallConfig_0 cfg .default64LE initMem poisonDef rfl rfl rfl rfl]
  rw [Step.ret_top_leaf_iff rfl rfl rfl rfl (v := .bv 8 .poison) (by simp [evalPureLeafExp?, RegisterValue.poisonOf])]
  rfl

theorem poison_is_refined_by_zero : poisonDef ⊒ zeroDef := by
  refine ⟨rfl, ?_⟩
  intro initMem args _ hargs
  cases args with
  | cons _ _ => llvm_wf [poisonDef] at hargs
  | nil =>
    have hY := det_step_to_halted (zeroDef_det .modern initMem)
    have hX : Terminates (initCallConfig .modern .default64LE initMem ∅ ∅ poisonDef [])
        [] (.bv 8 .poison) initMem :=
      StarStep.step ((poisonDef_det .modern initMem _ _).mpr ⟨rfl, rfl⟩) (StarStep.refl _)
    exact Config.IsRefinedBy.of_det_halted hY hX rfl (MemoryState.IsRefinedBy.refl _ _)

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

/-! ### 4. Immediate UB Refinement (UB Refines to Any Behavior) -/

open scoped LeanNanoLlvm.AST.Syntax in
def ret42Def : AST.Definition := [llvm-definition|
  define i8 @f(i8 %x) {
  entry:
    ret i8 42
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
def udivZeroDef : AST.Definition := [llvm-definition|
  define i8 @f(i8 %x) {
  entry:
    %r = udiv i8 %x, 0
    ret i8 %r
  }
]

theorem ret_42_refines_udiv_by_zero : udivZeroDef ⊒ ret42Def := by
  refine ⟨rfl, ?_⟩
  intro initMem args _ hargs
  rcases args with _ | ⟨arg, _ | _⟩
  · llvm_wf [udivZeroDef] at hargs
  · cases arg <;>
      llvm_wf [udivZeroDef] at hargs
    subst hargs
    rename_i v
    left; left
    refine ⟨[], "Division by zero", ?_⟩
    rw [initCallConfig_1 .modern .default64LE initMem udivZeroDef rfl (Or.inl rfl) rfl rfl rfl rfl]
    have hub : liftBinaryPure (.int 8) (.bv 8 v) (.bv 8 (.value (BitVec.ofInt 8 0)))
        (evalIntBinaryScalarPure (.udiv false)) = .error (.immediateUB "Division by zero") := by
      cases v using PoisonOr.casesOn' with
      | poison => rfl
      | value bv => rfl
    exact StarStep.step (ev := none)
      (Step.instr rfl rfl
        (StepInstr.intBinaryOp_eval_err
          (EvalExp.leaf_ok (by llvm_step))
          (EvalExp.leaf_ok (by simp [evalPureLeafExp?]))
          hub))
      (StarStep.refl _)
  · llvm_wf [udivZeroDef] at hargs

/-! ### 5. True Nondeterministic `freeze` Refinement -/

open scoped LeanNanoLlvm.AST.Syntax in
def freezePoisonDef : AST.Definition := [llvm-definition|
  define i8 @f() {
  entry:
    %r = freeze i8 poison
    ret i8 %r
  }
]

private theorem step_freeze_poison_inv (initMem : MemoryState) :
    ∀ ev c', Step (initCallConfig .modern .default64LE initMem ∅ ∅ freezePoisonDef []) ev c' →
      ev = none ∧ ∃ b : BitVec 8,
        c' = .running {
          frames := [{
            defn := freezePoisonDef
            curBlock := .name "entry"
            remainingCode := []
            terminator := entryTerm freezePoisonDef
            registers := (∅ : AssocMap AST.Identifier RegisterValue).insert
              (.local_id (.name "r")) (.bv 8 (.value b))
          }]
          memory := initMem
          config := .modern
          dataLayout := .default64LE
        } := by
  intro ev c' hs
  rw [initCallConfig_0 .modern .default64LE initMem freezePoisonDef rfl rfl rfl rfl] at hs
  rw [Step.instr_iff rfl rfl] at hs
  cases hs with
  | freeze_err he =>
    dsimp only at he
    rw [EvalExp.leaf_iff (v := .bv 8 .poison) (by simp [evalPureLeafExp?, RegisterValue.poisonOf])] at he
    cases he
  | freeze_ok he hfr =>
    dsimp only at he
    rw [EvalExp.leaf_iff (v := .bv 8 .poison) (by simp [evalPureLeafExp?, RegisterValue.poisonOf])] at he
    cases he
    cases hfr with
    | bv_poison _ b _ => exact ⟨rfl, b, rfl⟩

private theorem step_freeze_poison_ret (initMem : MemoryState) (b : BitVec 8) :
    ∀ ev c',
      Step (.running {
        frames := [{
          defn := freezePoisonDef
          curBlock := .name "entry"
          remainingCode := []
          terminator := entryTerm freezePoisonDef
          registers := (∅ : AssocMap AST.Identifier RegisterValue).insert
            (.local_id (.name "r")) (.bv 8 (.value b))
        }]
        memory := initMem
        config := .modern
        dataLayout := .default64LE
      }) ev c' ↔
      ev = none ∧ c' = .halted (.bv 8 (.value b)) initMem := by
  intro ev c'
  rw [Step.ret_top_leaf_iff rfl rfl rfl rfl (v := .bv 8 (.value b)) (by llvm_step)]
  rfl

theorem zero_refines_freeze_poison : freezePoisonDef ⊒ zeroDef := by
  refine ⟨rfl, ?_⟩
  intro initMem args _ hargs
  cases args with
  | cons _ _ => llvm_wf [freezePoisonDef] at hargs
  | nil =>
    have hY := det_step_to_halted (zeroDef_det .modern initMem)
    have hTermX : Terminates (initCallConfig .modern .default64LE initMem ∅ ∅ freezePoisonDef [])
        [] (.bv 8 (.value (0 : BitVec 8))) initMem := by
      rw [initCallConfig_0 .modern .default64LE initMem freezePoisonDef rfl rfl rfl rfl]
      exact StarStep.step (ev := none)
        (Step.instr rfl rfl
          (StepInstr.freeze_ok
            (EvalExp.leaf_ok (by simp [evalPureLeafExp?, RegisterValue.poisonOf]))
            (FreezeRel.bv_poison 8 (0 : BitVec 8) (by intro h; cases h))))
        (StarStep.step (ev := none)
          (Step.term rfl rfl rfl
            (StepTerm.ret_ok rfl
              (EvalExp.leaf_ok (by llvm_step; rfl))
              (StepRet.top_ok rfl (by llvm_step [freezePoisonDef]))))
          (StarStep.refl _))
    exact Config.IsRefinedBy.of_det_halted hY hTermX
      (RegisterValue.IsRefinedBy.refl _)
      (MemoryState.IsRefinedBy.refl _ _)

theorem freeze_poison_refines_poison : poisonDef ⊒ freezePoisonDef := by
  refine ⟨rfl, ?_⟩
  intro initMem args _ hargs
  cases args with
  | cons _ _ => llvm_wf [poisonDef] at hargs
  | nil =>
    right
    have hstep1 := step_freeze_poison_inv initMem
    refine ⟨?_, ?_, ?_⟩
    · rintro (⟨tr, msg, hstar⟩ | ⟨tr, err, hstar⟩)
      · cases hstar with
        | step hs hrest =>
          obtain ⟨rfl, b, rfl⟩ := hstep1 _ _ hs
          exact (det_step_to_halted (step_freeze_poison_ret initMem b)).1 (Or.inl ⟨_, msg, hrest⟩)
      · cases hstar with
        | step hs hrest =>
          obtain ⟨rfl, b, rfl⟩ := hstep1 _ _ hs
          exact (det_step_to_halted (step_freeze_poison_ret initMem b)).1 (Or.inr ⟨_, err, hrest⟩)
    · intro trY retY memY htY
      cases htY with
      | step hs hrest =>
        obtain ⟨rfl, b, rfl⟩ := hstep1 _ _ hs
        obtain ⟨rfl, rfl, hmemEq⟩ := (det_step_to_halted (step_freeze_poison_ret initMem b)).2.2 _ _ _ hrest
        rw [hmemEq]
        have hX : Terminates (initCallConfig .modern .default64LE initMem ∅ ∅ poisonDef [])
            [] (.bv 8 .poison) initMem :=
          StarStep.step ((poisonDef_det .modern initMem _ _).mpr ⟨rfl, rfl⟩) (StarStep.refl _)
        exact ⟨[], .bv 8 .poison, initMem, .id,
          MemoryInjection.id_idOn _, hX, trivial, rfl, MemoryState.IsRefinedBy.refl _ _⟩
    · intro hdiv
      obtain ⟨ev, c1, hs, hdiv1⟩ := Diverges.step_inv hdiv
      obtain ⟨rfl, b, rfl⟩ := hstep1 ev c1 hs
      exact False.elim ((det_step_to_halted (step_freeze_poison_ret initMem b)).2.1 hdiv1)

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

/-! ### 6. IEEE-754 Floating-Point Refinement (`fneg (fneg %x)` & Fast-Math Flags) -/

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
  refine ⟨rfl, ?_⟩
  intro initMem args _ hargs
  rcases args with _ | ⟨arg, _ | _⟩
  · llvm_wf [fnegFnegDef] at hargs
  · cases arg <;>
      llvm_wf [fnegFnegDef] at hargs
    subst hargs
    rename_i v
    rw [initCallConfig_1 .modern .default64LE initMem idFloatDef rfl (Or.inl rfl) rfl rfl rfl rfl]
    rw [initCallConfig_1 .modern .default64LE initMem fnegFnegDef rfl (Or.inl rfl) rfl rfl rfl rfl]
    have hfneg1 : evalFloatUnaryExec (.fneg {}) (.float .float) (.float .float v) default =
        .ok (.float .float (evalFloatUnaryOp (.fneg {}) false v), (default : OracleState).nextBool.2) := rfl
    have hfneg2 : evalFloatUnaryExec (.fneg {}) (.float .float)
        (.float .float (evalFloatUnaryOp (.fneg {}) false v)) default =
        .ok (.float .float v, (default : OracleState).nextBool.2) := by
      cases v using PoisonOr.casesOn' with
      | poison => rfl
      | value flt => simp [evalFloatUnaryExec, evalFloatUnaryOp, handleFMF, OracleState.nextBool]
    exact Config.IsRefinedBy.of_det_halted
      (det_step_to_halted fun ev c' => by
        rw [Step.ret_top_leaf_iff rfl rfl rfl rfl (v := .float .float v)
          (by llvm_step)]
        rfl)
      (StarStep.step (ev := none)
        (Step.instr rfl rfl
          (StepInstr.floatUnaryOp_ok
            (EvalExp.leaf_ok (by llvm_step))
            ⟨default, _, hfneg1⟩))
        (StarStep.step (ev := none)
          (Step.instr rfl rfl
            (StepInstr.floatUnaryOp_ok
              (EvalExp.leaf_ok (by llvm_step))
              ⟨default, _, hfneg2⟩))
          (StarStep.step (ev := none)
            (Step.term rfl rfl rfl
              (StepTerm.ret_ok rfl
                (EvalExp.leaf_ok (by llvm_step; rfl))
                (StepRet.top_ok rfl (by llvm_step [fnegFnegDef]))))
            (StarStep.refl _))))
      (RegisterValue.IsRefinedBy.refl _)
      (MemoryState.IsRefinedBy.refl _ _)
  · llvm_wf [fnegFnegDef] at hargs

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
  unfold evalFloatBinaryExec
  dsimp only [↓reduceDIte]
  cases h1 : o.nextBool with | mk flipL o1 =>
  cases h2 : o1.nextBool with | mk flipR o2 =>
  cases h3 : o2.nextBool with | mk denormL o3 =>
  cases h4 : o3.nextBool with | mk denormR o4 =>
  cases h5 : o4.nextBool with | mk nanSign o5 =>
  cases h6 : o5.nextNat with | mk nanPick o6 =>
  refine ⟨_, _, o6, o6, rfl, rfl, ?_⟩
  cases va using PoisonOr.casesOn' with
  | poison => simp [evalFloatBinaryOp]
  | value fa =>
    cases vb using PoisonOr.casesOn' with
    | poison => simp [evalFloatBinaryOp]
    | value fb =>
      simp only [evalFloatBinaryOp, handleFMF, handleDenormal_ieee, SemanticsConfig.modern,
                 PoisonOr.value_bind, Bool.true_and, Bool.false_and,
                 ite_false, Bool.false_eq_true]
      by_cases ha : fa.isNaN = true
      · rw [ha]; simp
      · rw [Bool.eq_false_iff.mpr ha]
        by_cases hb : fb.isNaN = true
        · rw [hb]; simp
        · rw [Bool.eq_false_iff.mpr hb]
          simp only [Bool.false_eq_true, ite_false, PoisonOr.value_bind]
          by_cases hr : (IEEEFloat.add RoundingMode.RNE fa fb).isNaN = true
          · rw [hr]; simp
          · rw [Bool.eq_false_iff.mpr hr]; simp

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
        obtain ⟨rt, rs, o1, o2, hok, _, _⟩ := evalFloatBinary_fadd_refines_nnan va vb o
        rw [hok] at ho; cases ho
      | floatBinaryOp_ok he1 he2 hf =>
        rw [EvalExp.leaf_iff haLeaf] at he1; cases he1
        rw [EvalExp.leaf_iff hbLeaf] at he2; cases he2
        obtain ⟨o, o1', ho⟩ := hf
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

/-! ### 7. Select Non-Poison-Propagation Refinement -/

open scoped LeanNanoLlvm.AST.Syntax in
def retADef : AST.Definition := [llvm-definition|
  define i32 @f(i32 %a, i32 %b) {
  entry:
    ret i32 %a
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
def selectTrueDef : AST.Definition := [llvm-definition|
  define i32 @f(i32 %a, i32 %b) {
  entry:
    %r = select i1 true, i32 %a, i32 %b
    ret i32 %r
  }
]

theorem ret_a_refines_select_true : selectTrueDef ⊒ retADef := by
  refine ⟨rfl, ?_⟩
  intro initMem args _ hargs
  rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · llvm_wf [selectTrueDef] at hargs
  · llvm_wf [selectTrueDef] at hargs
  · cases a <;> cases b <;>
      llvm_wf [selectTrueDef] at hargs
    rcases hargs with ⟨rfl, rfl⟩
    rename_i va vb
    have hba : (AST.Identifier.local_id (.name "b") == AST.Identifier.local_id (.name "a")) = false := rfl
    rw [initCallConfig_2 .modern .default64LE initMem retADef
          rfl (Or.inl rfl) rfl rfl rfl rfl rfl]
    rw [initCallConfig_2 .modern .default64LE initMem selectTrueDef
          rfl (Or.inl rfl) rfl rfl rfl rfl rfl]
    exact Config.IsRefinedBy.of_det_halted
      (det_step_to_halted fun ev c' => by
        rw [Step.ret_top_leaf_iff rfl rfl rfl rfl (v := .bv 32 va)
          (by llvm_step [hba])]
        rfl)
      (StarStep.step (ev := none)
        (Step.instr rfl rfl
          (StepInstr.select_ok
            (EvalExp.leaf_ok (by simp [evalPureLeafExp?]; rfl))
            (EvalExp.leaf_ok (by llvm_step [hba]; rfl))
            (EvalExp.leaf_ok (by llvm_step; rfl))
            (by rfl)
            ⟨default, default, rfl⟩))
        (StarStep.step (ev := none)
          (Step.term rfl rfl rfl
            (StepTerm.ret_ok rfl
              (EvalExp.leaf_ok (by llvm_step; rfl))
              (StepRet.top_ok rfl (by llvm_step [selectTrueDef]))))
          (StarStep.refl _)))
      (RegisterValue.IsRefinedBy.refl _)
      (MemoryState.IsRefinedBy.refl _ _)
  · llvm_wf [selectTrueDef] at hargs

/-! ### 8. Arbitrary Caller-Memory Store-to-Load Forwarding & Dead `alloca` Elimination -/

private theorem typeAllocSize_i8 :
    AST.DataLayout.default64LE.typeAllocSize (.int 8) = 1 := by decide

private theorem typeStoreSize_i8 :
    AST.DataLayout.default64LE.typeStoreSize (.int 8) = 1 := by decide

private theorem alloc_i8_steps_ok {initMem : MemoryState} (hwf : MemoryState.WellFormed initMem)
    {name : String} {obj : MemoryObject} {mem1 : MemoryState}
    (halloc : initMem.allocate .default64LE .modern 1 1 name 0 .uninitialized .stack false = .ok (obj, mem1)) :
    let ptr := MemoryState.derivePointer .default64LE obj
    MemoryState.AllocSpec initMem .default64LE .modern 1 1 name 0 .uninitialized .stack false obj mem1 ∧
    obj.allocId = initMem.nextAllocId ∧
    mem1.verifyMemAccess ptr 1 1 true = .ok (obj, 0) ∧
    (∀ b : MemByte,
      let mem2 := mem1.writeObjectBytes obj.allocId 0 #[b]
      let obj' := { obj with bytes := #[b] }
      mem2.verifyMemAccess ptr 1 1 false = .ok (obj', 0) ∧
      MemoryState.readObjectBytes obj' 0 1 = #[b]) ∧
    (∀ id ∈ initMem.allocIds, mem1.objects.get? id = initMem.objects.get? id) := by
  have hspec := MemoryState.allocate_satisfies_AllocSpec hwf halloc
  have hidEq : obj.allocId = initMem.nextAllocId := hspec.id_eq
  have haddrLt : obj.baseAddr < 2 ^ 64 := by
    have hs := hspec.addr_in_space
    change obj.baseAddr + max 1 1 < 1 <<< 64 at hs
    omega
  have hptrAddr : (MemoryState.derivePointer .default64LE obj).addr.toNat = obj.baseAddr := by
    simp only [MemoryState.derivePointer, AST.DataLayout.default64LE,
               AST.DataLayout.getPointerSizeInBits, hspec.as_eq, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt haddrLt
  have hmem1Objs : mem1.objects = initMem.objects.insert obj.allocId obj := by
    rw [hspec.mem'_eq]
  have hget1 : mem1.objects.get? obj.allocId = some obj := by
    rw [hmem1Objs, AssocMap.get?_insert, beq_self_eq_true]; rfl
  have hresolve1 : mem1.resolveObject? (MemoryState.derivePointer .default64LE obj) = some obj := by
    simp only [MemoryState.resolveObject?, MemoryState.derivePointer, hget1]
  have hverStore : mem1.verifyMemAccess (MemoryState.derivePointer .default64LE obj) 1 1 true = .ok (obj, 0) := by
    unfold MemoryState.verifyMemAccess
    rw [hresolve1]; dsimp only
    rw [hspec.state_eq, hspec.const_eq, hspec.size_eq, hptrAddr]
    simp [Nat.mod_one]
  have hcallerEq : ∀ id ∈ initMem.allocIds, mem1.objects.get? id = initMem.objects.get? id := by
    intro id hid
    have hlt := MemoryState.allocId_lt_nextAllocId_of_mem_allocIds hwf hid
    have hne : obj.allocId ≠ id := by rw [hidEq]; exact Nat.ne_of_gt hlt
    rw [hmem1Objs, AssocMap.get?_insert, beq_false_of_ne hne]; rfl
  refine ⟨hspec, hidEq, hverStore, ?_, hcallerEq⟩
  intro b
  have hwf1 : MemoryState.WellFormed mem1 := MemoryState.allocate_preserves_wf hwf halloc
  have hverLoad0 : mem1.verifyMemAccess (MemoryState.derivePointer .default64LE obj) 1 1 false = .ok (obj, 0) := by
    unfold MemoryState.verifyMemAccess
    rw [hresolve1]; dsimp only
    rw [hspec.state_eq, hspec.size_eq, hptrAddr]
    simp [Nat.mod_one]
  have hverLoad1 := MemoryState.verifyMemAccess_writeObjectBytes_same hwf1 hverLoad0 0 #[b]
  have hgoEq : MemoryState.writeObjectBytes.go 0 #[b] 0 #[b].size obj.bytes = #[b] := by
    rw [hspec.bytes_eq]
    rfl
  rw [hgoEq] at hverLoad1
  have hread : MemoryState.readObjectBytes { obj with bytes := #[b] } 0 1 = #[b] := by
    unfold MemoryState.readObjectBytes
    dsimp only
    rw [hspec.state_eq]
    rfl
  exact ⟨hverLoad1, hread⟩

private theorem readScalarBits_loop_modern_eq
    (dl : AST.DataLayout) (bytes : Array MemByte) (offsetInBits numBits : Nat)
    (i rem valBits : Nat) (hasUndef isPoison provOk : Bool)
    (provAcc : Option Provenance) (padNonZero : Bool) (o o0 : OracleState) :
    readScalarBits.loop dl .modern bytes offsetInBits numBits i rem valBits
      hasUndef isPoison provOk provAcc padNonZero o =
    let r := readScalarBits.loop dl .modern bytes offsetInBits numBits i rem valBits
      hasUndef isPoison provOk provAcc padNonZero o0
    (r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2.1, o) := by
  induction rem generalizing i valBits hasUndef isPoison provOk provAcc padNonZero with
  | zero => rfl
  | succ r ih =>
    simp only [readScalarBits.loop, SemanticsConfig.modern]
    cases getLogicalBit dl bytes (offsetInBits + i) with
    | poison => exact ih ..
    | undef => exact ih ..
    | concrete b provBit =>
      dsimp only
      cases b with
      | false => exact ih ..
      | true => by_cases hi : i < numBits <;> simp only [hi, ↓reduceIte] <;> exact ih ..

private theorem byte_roundtrip_i8 (v : IntW 8) (o : OracleState) :
    bytesToValue .default64LE .modern
      (valueToBytes .default64LE .modern (.bv 8 v) (.int 8))
      (.int 8) o = (.bv 8 v, v == .poison, o) := by
  simp only [valueToBytes, bytesToValue, writeScalarBits, readScalarBits,
             AST.DataLayout.typeStoreSize, AST.DataLayout.typeSizeInBits,
             AST.DataLayout.typeLayout, AST.DataLayout.alignTo]
  cases v using PoisonOr.casesOn' with
  | poison => rfl
  | value bv =>
    rw [readScalarBits_loop_modern_eq (o0 := ⟨fun _ => 0, 0⟩)]
    have hcheck : ∀ hi lo : Fin 16,
        let n := hi.val * 16 + lo.val
        let bs := writeBitLoop AST.DataLayout.default64LE 0
          (fun i => if i < 8 then MemBit.concrete ((BitVec.ofNat 8 n).getLsbD i) none else MemBit.concrete false none)
          0 8 (Array.replicate 1 MemByte.zero)
        let r := readScalarBits.loop AST.DataLayout.default64LE .modern bs 0 8 0 8 0 false false true none false ⟨fun _ => 0, 0⟩
        r.1 = n ∧ r.2.1 = false ∧ r.2.2.1 = false ∧ r.2.2.2.2.2.1 = false := by
      decide +kernel
    have hhi : bv.toNat / 16 < 16 := by have := bv.isLt; omega
    have hlo : bv.toNat % 16 < 16 := by omega
    have hk := hcheck ⟨bv.toNat / 16, hhi⟩ ⟨bv.toNat % 16, hlo⟩
    have hn : bv.toNat / 16 * 16 + bv.toNat % 16 = bv.toNat := by omega
    have hbv : BitVec.ofNat 8 (bv.toNat / 16 * 16 + bv.toNat % 16) = bv := by
      rw [hn]; simp
    dsimp only at hk
    rw [hbv, hn] at hk
    rcases hk with ⟨h1, h2, h3, h4⟩
    have hstep2 : (8 + 7) / 8 = 1 := rfl
    have hstep1 : ((if True then if 8 ≤ 1 then 0 + 8 else 1 * 8 else 0 + 8) - 0) = 8 := rfl
    change (if _ then _ else _) = _
    simp only [hstep2, hstep1]
    rw [h3, h4, h1, h2]
    have hof : BitVec.ofNat 8 bv.toNat = bv := by simp
    simp [hof]
    intro hc
    cases hc

private theorem valueToBytes_i8_singleton (v : IntW 8) :
    ∃ b : MemByte, valueToBytes .default64LE .modern (.bv 8 v) (.int 8) = #[b] := by
  have hloop : ∀ (fn : Nat → MemBit) (i rem : Nat) (b : MemByte),
      ∃ b', writeBitLoop .default64LE 0 fn i rem #[b] = #[b'] := by
    intro fn i rem
    induction rem generalizing i with
    | zero => intro b; exact ⟨b, rfl⟩
    | succ r ih =>
      intro b
      simp only [writeBitLoop, setLogicalBit, AST.DataLayout.default64LE,
                 AST.DataLayout.isLittleEndian, beq_self_eq_true, ↓reduceIte, Nat.zero_add]
      cases i / 8 with
      | zero =>
        simp only [setLogicalBit.updateList]
        exact ih (i + 1) (b.setBit (i % 8) (fn i))
      | succ k =>
        simp only [setLogicalBit.updateList]
        exact ih (i + 1) b
  simp only [valueToBytes, writeScalarBits, AST.DataLayout.typeStoreSize,
             AST.DataLayout.typeSizeInBits, AST.DataLayout.typeLayout,
             AST.DataLayout.default64LE]
  cases v using PoisonOr.casesOn' with
  | poison => exact hloop _ 0 _ MemByte.zero
  | value bv => exact hloop _ 0 _ MemByte.zero

open scoped LeanNanoLlvm.AST.Syntax in
def allocaStoreLoadI8Def : AST.Definition := [llvm-definition|
  define i8 @f(i8 %x) {
  entry:
    %p = alloca i8, align 1
    store i8 %x, ptr %p, align 1
    %v = load i8, ptr %p, align 1
    ret i8 %v
  }
]

/--
Store-to-load forwarding verified for ALL well-formed caller memories `initMem`!
If `initMem` is out of memory, source `alloca` aborts (`CanAbort`); otherwise source
allocates a fresh stack slot, stores `%x`, loads `%x` back, frees the slot on return,
and leaves every pre-existing caller object in `initMem.allocIds` untouched.
-/
theorem ret_x_refines_alloca_store_load_i8 :
    allocaStoreLoadI8Def ⊒ retXDef 8 := by
  refine ⟨rfl, ?_⟩
  intro initMem args hwfMem hargs
  rcases args with _ | ⟨arg, _ | _⟩
  · llvm_wf [allocaStoreLoadI8Def] at hargs
  · cases arg <;>
      llvm_wf [allocaStoreLoadI8Def] at hargs
    subst hargs
    rename_i v
    rw [initCallConfig_1 .modern .default64LE initMem (retXDef 8) rfl (Or.inl rfl) rfl rfl rfl rfl]
    rw [initCallConfig_1 .modern .default64LE initMem allocaStoreLoadI8Def rfl (Or.inl rfl) rfl rfl rfl rfl]
    cases halloc : initMem.allocate .default64LE .modern 1 1 "p" 0 .uninitialized .stack false with
    | error err =>
      left
      rcases MemoryState.allocate_error_cases halloc with ⟨rfl, hoom⟩ | ⟨msg, rfl, hsz⟩
      · right
        refine ⟨[], .outOfMemory, StarStep.step (ev := none) ?_ (StarStep.refl _)⟩
        exact Step.instr rfl rfl
          (StepInstr.alloca_oom (count := 1) ⟨rfl, rfl⟩ (by simpa [typeAllocSize_i8] using hoom))
      · exact absurd hsz (by decide +kernel)
    | ok pair =>
      obtain ⟨obj, mem1⟩ := pair
      obtain ⟨hspec, hidEq, hverStore, hreadAfterWrite, hcallerEq⟩ := alloc_i8_steps_ok hwfMem halloc
      obtain ⟨b, hb⟩ := valueToBytes_i8_singleton v
      obtain ⟨hverLoad, hreadBytes⟩ := hreadAfterWrite b
      have hpx : (AST.Identifier.local_id (.name "p") == AST.Identifier.local_id (.name "x")) = false := rfl
      have hbtv : BytesToValueRel .default64LE .modern
          (MemoryState.readObjectBytes { obj with bytes := #[b] } 0 1) (.int 8) (.bv 8 v) (v == .poison) := by
        rw [hreadBytes]
        have hrt := byte_roundtrip_i8 v default
        rw [hb] at hrt
        exact bytesToValue_satisfies_rel hrt
      let mem2 := mem1.writeObjectBytes obj.allocId 0 (valueToBytes .default64LE .modern (.bv 8 v) (.int 8))
      let memFinal := mem2.freeObject obj.allocId
      have hmemRef : MemoryState.IsRefinedBy .id initMem.allocIds memFinal initMem := by
        intro id hid
        have hlt := MemoryState.allocId_lt_nextAllocId_of_mem_allocIds hwfMem hid
        have hne : obj.allocId ≠ id := by rw [hidEq]; exact Nat.ne_of_gt hlt
        have heq : memFinal.objects.get? id = initMem.objects.get? id := by
          dsimp only [memFinal, mem2]
          rw [MemoryState.objects_get?_freeObject_ne _ _ hne,
              MemoryState.objects_get?_writeObjectBytes_ne _ _ _ _ hne,
              hcallerEq id hid]
        rw [heq]
        cases initMem.objects.get? id with
        | none => trivial
        | some mo => exact ⟨rfl, rfl, fun _ i _ => MemByte.IsRefinedBy.refl _⟩
      refine Config.IsRefinedBy.of_det_halted
        (det_step_to_halted fun ev c' => by
          rw [Step.ret_top_leaf_iff rfl rfl rfl rfl (v := .bv 8 v)
                (by llvm_step)]
          simp only [freeAllocaList, applyRetFMFAndAttrsPure, applyValueAttrsPure, retXDef]
          rfl)
        (StarStep.step (ev := none)
          (Step.instr rfl rfl
            (StepInstr.alloca_ok (count := 1) ⟨rfl, rfl⟩
              (by simpa [typeAllocSize_i8, AST.RawId.ToString] using hspec)))
          (StarStep.step (ev := none)
            (Step.instr rfl rfl
              (StepInstr.store_ok
                (EvalExp.leaf_ok (by llvm_step [hpx]))
                (EvalExp.leaf_ok (by llvm_step; exact ⟨rfl, rfl⟩))
                (by simpa [typeStoreSize_i8] using hverStore)))
            (StarStep.step (ev := none)
              (Step.instr rfl rfl
                (StepInstr.load_ok
                  (EvalExp.leaf_ok (by llvm_step; exact ⟨rfl, rfl⟩))
                  (by simpa [typeStoreSize_i8, hb] using hverLoad)
                  (by simpa [typeStoreSize_i8] using hbtv)
                  rfl
                  (by intro h; cases h)))
              (StarStep.step (ev := none)
                (Step.term rfl rfl rfl
                  (StepTerm.ret_ok rfl
                    (EvalExp.leaf_ok (by llvm_step; rfl))
                    (StepRet.top_ok rfl (by llvm_step [allocaStoreLoadI8Def]))))
                (StarStep.refl _)))))
        (RegisterValue.IsRefinedBy.refl _)
        hmemRef
  · llvm_wf [allocaStoreLoadI8Def] at hargs

open scoped LeanNanoLlvm.AST.Syntax in
def deadAllocaStoreI8Def : AST.Definition := [llvm-definition|
  define i8 @f(i8 %x) {
  entry:
    %p = alloca i8, align 1
    store i8 42, ptr %p, align 1
    ret i8 %x
  }
]

/-- Dead `alloca` + dead `store` elimination verified for ALL well-formed caller memories `initMem`. -/
theorem dead_alloca_store_elim_i8 :
    deadAllocaStoreI8Def ⊒ retXDef 8 := by
  refine ⟨rfl, ?_⟩
  intro initMem args hwfMem hargs
  rcases args with _ | ⟨arg, _ | _⟩
  · llvm_wf [deadAllocaStoreI8Def] at hargs
  · cases arg <;>
      llvm_wf [deadAllocaStoreI8Def] at hargs
    subst hargs
    rename_i v
    rw [initCallConfig_1 .modern .default64LE initMem (retXDef 8) rfl (Or.inl rfl) rfl rfl rfl rfl]
    rw [initCallConfig_1 .modern .default64LE initMem deadAllocaStoreI8Def rfl (Or.inl rfl) rfl rfl rfl rfl]
    cases halloc : initMem.allocate .default64LE .modern 1 1 "p" 0 .uninitialized .stack false with
    | error err =>
      left
      rcases MemoryState.allocate_error_cases halloc with ⟨rfl, hoom⟩ | ⟨msg, rfl, hsz⟩
      · right
        refine ⟨[], .outOfMemory, StarStep.step (ev := none) ?_ (StarStep.refl _)⟩
        exact Step.instr rfl rfl
          (StepInstr.alloca_oom (count := 1) ⟨rfl, rfl⟩ (by simpa [typeAllocSize_i8] using hoom))
      · exact absurd hsz (by decide +kernel)
    | ok pair =>
      obtain ⟨obj, mem1⟩ := pair
      obtain ⟨hspec, hidEq, hverStore, _, hcallerEq⟩ := alloc_i8_steps_ok hwfMem halloc
      have hpx : (AST.Identifier.local_id (.name "p") == AST.Identifier.local_id (.name "x")) = false := rfl
      let mem2 := mem1.writeObjectBytes obj.allocId 0
        (valueToBytes .default64LE .modern (.bv 8 (.value (BitVec.ofInt 8 42))) (.int 8))
      let memFinal := mem2.freeObject obj.allocId
      have hmemRef : MemoryState.IsRefinedBy .id initMem.allocIds memFinal initMem := by
        intro id hid
        have hlt := MemoryState.allocId_lt_nextAllocId_of_mem_allocIds hwfMem hid
        have hne : obj.allocId ≠ id := by rw [hidEq]; exact Nat.ne_of_gt hlt
        have heq : memFinal.objects.get? id = initMem.objects.get? id := by
          dsimp only [memFinal, mem2]
          rw [MemoryState.objects_get?_freeObject_ne _ _ hne,
              MemoryState.objects_get?_writeObjectBytes_ne _ _ _ _ hne,
              hcallerEq id hid]
        rw [heq]
        cases initMem.objects.get? id with
        | none => trivial
        | some mo => exact ⟨rfl, rfl, fun _ i _ => MemByte.IsRefinedBy.refl _⟩
      refine Config.IsRefinedBy.of_det_halted
        (det_step_to_halted fun ev c' => by
          rw [Step.ret_top_leaf_iff rfl rfl rfl rfl (v := .bv 8 v)
                (by llvm_step)]
          simp only [freeAllocaList, applyRetFMFAndAttrsPure, applyValueAttrsPure, retXDef]
          rfl)
        (StarStep.step (ev := none)
          (Step.instr rfl rfl
            (StepInstr.alloca_ok (count := 1) ⟨rfl, rfl⟩
              (by simpa [typeAllocSize_i8, AST.RawId.ToString] using hspec)))
          (StarStep.step (ev := none)
            (Step.instr rfl rfl
              (StepInstr.store_ok
                (EvalExp.leaf_ok (by simp [evalPureLeafExp?]))
                (EvalExp.leaf_ok (by llvm_step; exact ⟨rfl, rfl⟩))
                (by simpa [typeStoreSize_i8] using hverStore)))
            (StarStep.step (ev := none)
              (Step.term rfl rfl rfl
                (StepTerm.ret_ok rfl
                  (EvalExp.leaf_ok (by llvm_step [hpx]; rfl))
                  (StepRet.top_ok rfl (by llvm_step [deadAllocaStoreI8Def]))))
              (StarStep.refl _))))
        (RegisterValue.IsRefinedBy.refl _)
        hmemRef
  · llvm_wf [deadAllocaStoreI8Def] at hargs

/-! ### 9. Caller-Visible Memory Refinement (Positive & Negative Tests) -/

open scoped LeanNanoLlvm.AST.Syntax in
def singleStoreCallerDef : AST.Definition := [llvm-definition|
  define void @f(ptr %p, i8 %v) {
  entry:
    store i8 %v, ptr %p, align 1
    ret void
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
def doubleStoreCallerDef : AST.Definition := [llvm-definition|
  define void @f(ptr %p, i8 %v) {
  entry:
    store i8 1, ptr %p, align 1
    store i8 %v, ptr %p, align 1
    ret void
  }
]

/--
Dead-store elimination on a caller-passed pointer `ptr %p` (arbitrary well-formed `initMem`):
eliminating the overwritten `store i8 1, ptr %p` preserves caller-visible memory identically,
and whenever `%p` is invalid/poison/readonly/OOB, source immediately triggers UB (`CanAbort`).
-/
theorem dead_store_elim_caller_mem_i8 :
    doubleStoreCallerDef ⊒ singleStoreCallerDef := by
  refine ⟨rfl, ?_⟩
  intro initMem args hwfMem hargs
  rcases args with _ | ⟨pArg, _ | ⟨vArg, _ | _⟩⟩
  · llvm_wf [doubleStoreCallerDef] at hargs
  · llvm_wf [doubleStoreCallerDef] at hargs
  · cases pArg <;> cases vArg <;>
      llvm_wf [doubleStoreCallerDef] at hargs
    rcases hargs with ⟨rfl, rfl⟩
    rename_i pv vv
    have hvp : (AST.Identifier.local_id (.name "v") == AST.Identifier.local_id (.name "p")) = false := rfl
    rw [initCallConfig_2 .modern .default64LE initMem singleStoreCallerDef
          rfl (Or.inl rfl) rfl rfl rfl rfl rfl]
    rw [initCallConfig_2 .modern .default64LE initMem doubleStoreCallerDef
          rfl (Or.inl rfl) rfl rfl rfl rfl rfl]
    cases pv using PoisonOr.casesOn' with
    | poison =>
      left; left
      refine ⟨[], "store through poison pointer", StarStep.step (ev := none) ?_ (StarStep.refl _)⟩
      apply Step.instr rfl rfl
      exact StepInstr.store_ptr_poison
        (EvalExp.leaf_ok (by simp [evalPureLeafExp?]; rfl))
        (EvalExp.leaf_ok (by llvm_step [hvp]; rfl))
    | value ptr =>
      cases hver : initMem.verifyMemAccess ptr 1 1 true with
      | error err =>
        obtain ⟨msg, rfl⟩ := MemoryState.verifyMemAccess_error_is_ub hver
        left; left
        refine ⟨[], msg, StarStep.step (ev := none) ?_ (StarStep.refl _)⟩
        refine Step.instr rfl rfl ?_
        exact StepInstr.store_mem_err (err := .immediateUB msg)
          (EvalExp.leaf_ok (by simp [evalPureLeafExp?]; rfl))
          (EvalExp.leaf_ok (by llvm_step [hvp]; exact ⟨rfl, rfl⟩))
          (by simpa [typeStoreSize_i8] using hver)
      | ok pair =>
        obtain ⟨mo, offset⟩ := pair
        obtain ⟨b1, hb1⟩ := valueToBytes_i8_singleton (.value (1#8))
        obtain ⟨b2, hb2⟩ := valueToBytes_i8_singleton vv
        have hver2 := MemoryState.verifyMemAccess_writeObjectBytes_same hwfMem hver offset #[b1]
        have hmemEq :
            (initMem.writeObjectBytes mo.allocId offset
                (valueToBytes .default64LE .modern (.bv 8 (.value (1#8))) (.int 8))).writeObjectBytes
              mo.allocId offset (valueToBytes .default64LE .modern (.bv 8 vv) (.int 8)) =
            initMem.writeObjectBytes mo.allocId offset
              (valueToBytes .default64LE .modern (.bv 8 vv) (.int 8)) := by
          rw [hb1, hb2]
          exact MemoryState.writeObjectBytes_overwrite_singleton initMem mo.allocId offset b1 b2
        refine Config.IsRefinedBy.of_det_halted
          (det_step_chain
            (fun ev c' => by
              rw [Step.store_leaf_iff rfl rfl
                    (val := .bv 8 vv) (as := 0) (p := ptr)
                    (by llvm_step)
                    (by llvm_step [hvp])]
              simp only [typeStoreSize_i8, Option.getD, hver, ↓reduceIte, Bool.false_eq_true]
              rfl)
            (det_step_to_halted fun ev c' => by
              rw [Step.retVoid_top_iff rfl rfl rfl rfl]))
          (StarStep.step (ev := none)
            (Step.instr rfl rfl
              (StepInstr.store_ok
                (EvalExp.leaf_ok (by simp [evalPureLeafExp?]; rfl))
                (EvalExp.leaf_ok (by llvm_step [hvp]; exact ⟨rfl, rfl⟩))
                (by simpa [typeStoreSize_i8] using hver)))
            (StarStep.step (ev := none)
              (Step.instr rfl rfl
                (StepInstr.store_ok
                  (EvalExp.leaf_ok (by llvm_step; rfl))
                  (EvalExp.leaf_ok (by llvm_step [hvp]; exact ⟨rfl, rfl⟩))
                  (by simpa [typeStoreSize_i8, hb1] using hver2)))
              (StarStep.step (ev := none)
                (Step.term rfl rfl rfl (StepTerm.retVoid_ok rfl (StepRet.top_ok rfl rfl)))
                (StarStep.refl _))))
          (RegisterValue.IsRefinedBy.refl _)
          (by dsimp only [MachineState.withFramesAndMemory, CallFrame.advance, freeAllocaList]; rw [hmemEq]; exact MemoryState.IsRefinedBy.refl _ _)
  · llvm_wf [doubleStoreCallerDef] at hargs

private def callerObj1 : MemoryObject :=
  { allocId := 1, baseAddr := 8, size := 1, align := 1, addrSpace := 0, name := "caller",
    state := .alive, allocKind := .stack, isConstant := false, bytes := #[MemByte.zero] }

private def callerMem1 : MemoryState :=
  { nextAllocId := 2, nextAddr := 10, usedMem := 1,
    objects := (∅ : AssocMap AllocId MemoryObject).insert 1 callerObj1 }

private theorem callerMem1_wf : MemoryState.WellFormed callerMem1 := by
  refine ⟨by decide, by decide, ?_⟩
  intro id mo hget
  simp only [callerMem1, AssocMap.get?_insert, AssocMap.get?_empty] at hget
  by_cases h1 : (1 == id) = true
  · rw [if_pos h1] at hget
    cases hget
    have hid : id = 1 := (eq_of_beq h1).symm
    subst hid
    exact ⟨rfl, by decide, by decide, by decide⟩
  · rw [if_neg h1] at hget; cases hget

open scoped LeanNanoLlvm.AST.Syntax in
def bogusStoreCallerDef : AST.Definition := [llvm-definition|
  define void @f(ptr %p) {
  entry:
    store i8 42, ptr %p, align 1
    ret void
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
def nopCallerDef : AST.Definition := [llvm-definition|
  define void @f(ptr %p) {
  entry:
    ret void
  }
]

/--
Negative test for caller-visible memory refinement:
a target that performs a spurious `store i8 42, ptr %p` does NOT refine a no-op `ret void`,
because `MemoryState.IsRefinedBy` rejects the corrupted caller byte (`42 ≠ 0`).
-/
theorem bogus_store_to_caller_mem_not_refines_nop :
    ¬ (nopCallerDef ⊒ bogusStoreCallerDef) := by
  rintro ⟨_, hbeh⟩
  let ptr1 : Pointer := { prov := .concrete 1, addrWidth := 64, addr := 8#64 }
  have hinst := hbeh callerMem1 [.ptr 0 (.value ptr1)] callerMem1_wf
    (by simp [Semantics.Definition.ArgValuesWellFormed, Semantics.RegisterValue.WellFormedForList,
              Semantics.RegisterValue.WellFormedFor, nopCallerDef])
  rw [initCallConfig_1 .modern .default64LE callerMem1 nopCallerDef rfl (Or.inl rfl) rfl rfl rfl rfl] at hinst
  rw [initCallConfig_1 .modern .default64LE callerMem1 bogusStoreCallerDef rfl (Or.inl rfl) rfl rfl rfl rfl] at hinst
  have hXstep : ∀ ev c',
      Step (.running {
        frames := [{ defn := nopCallerDef, curBlock := .name "entry", remainingCode := [],
                     terminator := entryTerm nopCallerDef,
                     registers := (∅ : AssocMap AST.Identifier RegisterValue).insert
                       (.local_id (.name "p")) (.ptr 0 (.value ptr1)) }]
        memory := callerMem1, config := .modern, dataLayout := .default64LE }) ev c' ↔
      ev = none ∧ c' = .halted .void callerMem1 := by
    intro ev c'
    rw [Step.retVoid_top_iff rfl rfl rfl rfl]
    simp only [freeAllocaList]
  have hX := det_step_to_halted hXstep
  rcases hinst with habortX | ⟨_, hterm, _⟩
  · exact hX.1 habortX
  · have hver : callerMem1.verifyMemAccess ptr1 1 1 true = .ok (callerObj1, 0) := by
      unfold MemoryState.verifyMemAccess
      simp [callerMem1, callerObj1, ptr1, MemoryState.resolveObject?, AssocMap.get?_insert]
    let memY := callerMem1.writeObjectBytes 1 0
      (valueToBytes .default64LE .modern (.bv 8 (.value (BitVec.ofInt 8 42))) (.int 8))
    obtain ⟨trX, retX, memX, inj, _, hTermX, _, _, hmemRef⟩ :=
      hterm [] .void memY
        (StarStep.step (ev := none)
          (Step.instr rfl rfl
            (StepInstr.store_ok
              (EvalExp.leaf_ok (by simp [evalPureLeafExp?]; rfl))
              (EvalExp.leaf_ok (by llvm_step; exact ⟨rfl, rfl⟩))
              (by simpa [typeStoreSize_i8] using hver)))
          (StarStep.step (ev := none)
            (Step.term rfl rfl rfl (StepTerm.retVoid_ok rfl (StepRet.top_ok rfl rfl)))
            (StarStep.refl _)))
    obtain ⟨rfl, rfl, hmemEq⟩ := hX.2.2 _ _ _ hTermX
    rw [hmemEq] at hmemRef
    have hid1 : (1 : AllocId) ∈ callerMem1.allocIds := by decide +kernel
    have hobj := hmemRef 1 hid1
    let obj42 : MemoryObject :=
      { callerObj1 with bytes := valueToBytes .default64LE .modern (.bv 8 (.value (BitVec.ofInt 8 42))) (.int 8) }
    have hgetY : memY.objects.get? 1 = some obj42 := by decide +kernel
    have hgetX : callerMem1.objects.get? 1 = some callerObj1 := rfl
    rw [hgetY, hgetX] at hobj
    obtain ⟨_, _, hbytes⟩ := hobj
    have hbyte0 := hbytes (by decide) 0 (by decide)
    have hbit1 := hbyte0 1 (by decide)
    have hbitY : (obj42.bytes.getD 0 MemByte.poison).getBit 1 = MemBit.concrete true none := by
      decide +kernel
    have hbitX : (callerObj1.bytes.getD 0 MemByte.poison).getBit 1 = MemBit.concrete false none := by
      decide +kernel
    rw [hbitY, hbitX] at hbit1
    exact Bool.noConfusion hbit1.1

/-! ### 10. Transitivity Chaining via Lean Core `Trans` (`calc`) -/

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

/-! ### 11. Backward Simulation (`Config.IsRefinedBy.of_simulation`) on Diverging Loops -/

open scoped LeanNanoLlvm.AST.Syntax in
def loopWithAddDef : AST.Definition := [llvm-definition|
  define void @spin(i32 %x) {
  entry:
    %y = add i32 %x, 0
    br label %entry
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
def tightLoopDef : AST.Definition := [llvm-definition|
  define void @spin(i32 %x) {
  entry:
    br label %entry
  }
]

/--
Eliminating a redundant `%y = add i32 %x, 0` inside an infinite loop preserves full behavioral
refinement (including `Diverges`), proved cleanly via `Config.IsRefinedBy.of_simulation` with
a 2-to-1 `PlusStep` simulation!
-/
theorem loop_with_add_is_refined_by_tight_loop :
    loopWithAddDef ⊒ tightLoopDef := by
  refine ⟨rfl, ?_⟩
  intro initMem args _ hargs
  rcases args with _ | ⟨arg, _ | _⟩
  · llvm_wf [loopWithAddDef] at hargs
  · cases arg <;> llvm_wf [loopWithAddDef] at hargs
    subst hargs
    rename_i v
    rw [initCallConfig_1 .modern .default64LE initMem loopWithAddDef rfl (Or.inl rfl) rfl rfl rfl rfl]
    rw [initCallConfig_1 .modern .default64LE initMem tightLoopDef rfl (Or.inl rfl) rfl rfl rfl rfl]
    let regs0 : AssocMap AST.Identifier RegisterValue :=
      (∅ : AssocMap AST.Identifier RegisterValue).insert (.local_id (.name "x")) (.bv 32 v)
    let stY : MachineState := {
      frames := [{ defn := tightLoopDef, curBlock := .name "entry", remainingCode := [],
                   terminator := entryTerm tightLoopDef, registers := regs0 }]
      memory := initMem, config := .modern, dataLayout := .default64LE }
    -- Source register map after 0 or more loop iterations (either `regs0` or `regs0.insert %y v`)
    let isSourceLoopState (cX : Config) : Prop :=
      ∃ regsX : AssocMap AST.Identifier RegisterValue,
        regsX.get? (.local_id (.name "x")) = some (.bv 32 v) ∧
        cX = .running {
          frames := [{ defn := loopWithAddDef, curBlock := .name "entry",
                       remainingCode := entryCode loopWithAddDef,
                       terminator := entryTerm loopWithAddDef, registers := regsX }]
          memory := initMem, config := .modern, dataLayout := .default64LE }
    let R : MemoryInjection → Config → Config → Prop :=
      fun inj cX cY => inj = .id ∧ isSourceLoopState cX ∧ cY = .running stY
    refine Config.IsRefinedBy.of_simulation R (fun _ => 0) ?_ ?_ ?_ (MemoryInjection.id_idOn _)
      ⟨rfl, ⟨regs0, by llvm_step [regs0], rfl⟩, rfl⟩
    · rintro _ _ _ _ ⟨_, _, hcY⟩; cases hcY
    · rintro _ _ _ ⟨_, _, hcY⟩ (⟨_, h⟩ | ⟨_, h⟩) <;> rw [hcY] at h <;> cases h
    · rintro inj cX cY evY cY' ⟨rfl, ⟨regsX, hgetX, rfl⟩, rfl⟩ hsY
      -- Target deterministically branches back to `stY`
      rw [Step.term_iff rfl rfl rfl] at hsY
      obtain ⟨rfl, hsY⟩ := hsY
      cases hsY with
      | br_step hj =>
        cases hj with
        | ok hfind hsplit hphi =>
          have hfind' : tightLoopDef.findBlock? (.name "entry") = some (tightLoopDef.blocks.head (by decide)) := rfl
          rw [hfind'] at hfind
          injection hfind with hblk; subst hblk
          cases hsplit
          cases hphi with
          | nil =>
            -- Source takes 2 steps (`add` then `br`) back to `isSourceLoopState`
            have haddVal : liftBinaryPure (.int 32) (.bv 32 v) (.bv 32 (.value 0#32))
                (evalIntBinaryScalarPure (.add false false)) = .ok (.bv 32 v) := by
              cases v using PoisonOr.casesOn' with
              | poison => llvm_simp
              | value bv => llvm_simp
            have hs1 : Step (.running {
                frames := [{ defn := loopWithAddDef, curBlock := .name "entry",
                             remainingCode := entryCode loopWithAddDef,
                             terminator := entryTerm loopWithAddDef, registers := regsX }]
                memory := initMem, config := .modern, dataLayout := .default64LE })
              none
              (.running {
                frames := [{ defn := loopWithAddDef, curBlock := .name "entry",
                             remainingCode := [],
                             terminator := entryTerm loopWithAddDef,
                             registers := regsX.insert (.local_id (.name "y")) (.bv 32 v) }]
                memory := initMem, config := .modern, dataLayout := .default64LE }) :=
              Step.instr rfl rfl
                (StepInstr.intBinaryOp_ok
                  (EvalExp.leaf_ok (by simp [evalPureLeafExp?, hgetX]))
                  (EvalExp.leaf_ok (by llvm_step))
                  haddVal)
            have hs2 : Step (.running {
                frames := [{ defn := loopWithAddDef, curBlock := .name "entry",
                             remainingCode := [],
                             terminator := entryTerm loopWithAddDef,
                             registers := regsX.insert (.local_id (.name "y")) (.bv 32 v) }]
                memory := initMem, config := .modern, dataLayout := .default64LE })
              none
              (.running {
                frames := [{ defn := loopWithAddDef, curBlock := .name "entry",
                             remainingCode := entryCode loopWithAddDef,
                             terminator := entryTerm loopWithAddDef,
                             registers := regsX.insert (.local_id (.name "y")) (.bv 32 v) }]
                memory := initMem, config := .modern, dataLayout := .default64LE }) :=
              Step.term rfl rfl rfl
                (StepTerm.br_step (StepJump.ok (nextBlk := loopWithAddDef.blocks.head (by decide)) rfl rfl EvalPhis.nil))
            have hyx : (AST.Identifier.local_id (.name "y") == AST.Identifier.local_id (.name "x")) = false := rfl
            refine Or.inr ⟨[], _, .id, MemoryInjection.Extends.refl _,
              Or.inl ⟨none, _, [], hs1, StarStep.single hs2, rfl⟩, trivial,
              rfl, ⟨regsX.insert (.local_id (.name "y")) (.bv 32 v),
                by simp [AssocMap.get?_insert, hyx, hgetX], rfl⟩, rfl⟩
        | phi_err hfind hsplit hphi =>
          have hfind' : tightLoopDef.findBlock? (.name "entry") = some (tightLoopDef.blocks.head (by decide)) := rfl
          rw [hfind'] at hfind
          injection hfind with hblk; subst hblk
          cases hsplit
          cases hphi
        | missing_block hfind =>
          have : tightLoopDef.findBlock? (.name "entry") ≠ none := by decide +kernel
          exact absurd hfind this
  · llvm_wf [loopWithAddDef] at hargs

/-! ### 12. Module-Aware Refinement (`RefinementEnv`) with Helper Function Calls -/

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
    have hmkCallee : mkEntryFrameWithMem .default64LE .modern initMem helperId32Def [.bv 32 v] =
      .ok ({ defn := helperId32Def, curBlock := .name "entry", remainingCode := [],
             terminator := entryTerm helperId32Def,
             registers := (∅ : AssocMap AST.Identifier RegisterValue).insert
               (.local_id (.name "v")) (.bv 32 v) }, initMem) := rfl
    -- Source execution: `add` → `call @id32` → callee `ret` → caller `ret`
    have hnoIntr : ∀ o, evalNonAllocIntrinsicExec? .default64LE .modern initMem
        (AST.RawId.name "id32").ToString (.ret (.int 32)) {} [.bv 32 v] o = none :=
      fun _ => rfl
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
              (EvalCallArgs.cons_ok (EvalExp.leaf_ok (by llvm_step; rfl)) (by llvm_step) EvalCallArgs.nil)
              EvalCallee.direct rfl hnoIntr hlookupId (Or.inr (by simp [SemanticsConfig.modern])) hmkCallee))
          (StarStep.step (ev := none)
            (Step.term rfl rfl rfl
              (StepTerm.ret_ok rfl (EvalExp.leaf_ok (by llvm_step; rfl))
                (StepRet.call_ok (rd := { destId := .id (.name "r"), retTy := .ret (.int 32), fmf := {}, retAttrs := [] })
                  rfl (by llvm_step [helperId32Def]; rfl) rfl (by llvm_step; rfl))))
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
            | call_ok hcons h1 hrd h2 =>
              cases hcons
              simp only [freeAllocaList, applyRetFMFAndAttrsPure, applyValueAttrsPure, helperId32Def] at h1
              injection h1 with hv1; subst hv1
              injection hrd with hrd'; subst hrd'
              simp only [applyRetFMFAndAttrsPure, applyValueAttrsPure] at h2
              injection h2 with hv2; subst hv2
              exact ⟨rfl, rfl⟩
            | callee_attr_err h1 =>
              simp only [freeAllocaList, applyRetFMFAndAttrsPure, applyValueAttrsPure, helperId32Def] at h1
              cases h1
            | caller_attr_err hcons h1 hrd h2 =>
              cases hcons
              simp only [freeAllocaList, applyRetFMFAndAttrsPure, applyValueAttrsPure, helperId32Def] at h1
              injection h1 with hv1; subst hv1
              injection hrd with hrd'; subst hrd'
              simp only [applyRetFMFAndAttrsPure, applyValueAttrsPure] at h2
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
                rfl (by llvm_step [helperId32Def]; rfl) rfl (by llvm_step))))
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
              simp only [applyValueAttrsPure] at ha; cases ha
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
          | call_intrinsic_ok hargsEv hcallee _ hintr _ | call_intrinsic_retattr_err hargsEv hcallee _ hintr _ =>
            cases hcallee with
            | direct =>
              cases hargsEv with
              | cons_ok he ha hrest =>
                rw [EvalExp.leaf_iff (by llvm_step; rfl)] at he
                injection he with hpair; cases hpair
                simp only [applyValueAttrsPure] at ha; injection ha with hv; subst hv
                cases hrest
                obtain ⟨o, _, h⟩ := hintr; rw [hnoIntr o] at h; cases h
            | indirect_ok hne _ _ => exact absurd rfl (hne (.name "id32"))
          | call_intrinsic_err hargsEv hcallee _ hintr =>
            cases hcallee with
            | direct =>
              cases hargsEv with
              | cons_ok he ha hrest =>
                rw [EvalExp.leaf_iff (by llvm_step; rfl)] at he
                injection he with hpair; cases hpair
                simp only [applyValueAttrsPure] at ha; injection ha with hv; subst hv
                cases hrest
                obtain ⟨o, h⟩ := hintr; rw [hnoIntr o] at h; cases h
            | indirect_ok hne _ _ => exact absurd rfl (hne (.name "id32"))
          | call_user_ok hargsEv hcallee _ _ hfn _ hmk =>
            cases hcallee with
            | direct =>
              cases hargsEv with
              | cons_ok he ha hrest =>
                rw [EvalExp.leaf_iff (by llvm_step; rfl)] at he
                injection he with hpair; cases hpair
                simp only [applyValueAttrsPure] at ha; injection ha with hv; subst hv
                cases hrest
                rw [hlookupId] at hfn; injection hfn with hdef; subst hdef
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
                simp only [applyValueAttrsPure] at ha; injection ha with hv; subst hv
                cases hrest
                rw [hlookupId] at hfn; injection hfn with hdef; subst hdef
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
              (EvalCallArgs.cons_ok (EvalExp.leaf_ok (by llvm_step; rfl)) (by llvm_step) EvalCallArgs.nil)
              EvalCallee.direct rfl hnoIntr hlookupId (Or.inr (by simp [SemanticsConfig.modern])) hmkCallee))
      hY2
    exact Config.IsRefinedBy.of_det_halted hY1 hX_term
      (RegisterValue.IsRefinedBy.refl _)
      (MemoryState.IsRefinedBy.refl _ _)
  · llvm_wf [callerWithAdd0Def] at hargs

end LeanNanoLlvm.Refinement
