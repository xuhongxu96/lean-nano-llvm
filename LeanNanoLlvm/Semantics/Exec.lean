import LeanNanoLlvm.Util.Config
import LeanNanoLlvm.Util.Undef
import LeanNanoLlvm.Util.AssocMap
import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.DataLayout
import LeanNanoLlvm.AST.Print
import LeanNanoLlvm.Semantics.IntOps
import LeanNanoLlvm.Semantics.FloatOps
import LeanNanoLlvm.Semantics.Memory
import LeanNanoLlvm.Semantics.Value
import LeanNanoLlvm.Semantics.Intrinsics
import LeanNanoLlvm.Semantics.Machine
import LeanNanoLlvm.Semantics.Step

namespace LeanNanoLlvm.Semantics

open AST

/-! ### Executable Expression, Argument, Phi, and Callee Evaluators -/

/-- Forget the trailing `OracleState` from an executable evaluator result (for soundness theorems). -/
@[simp]
def stripOracle {α : Type} :
    Except ExecError (α × MemoryState × OracleState) → Except ExecError (α × MemoryState)
  | .ok (a, m, _) => .ok (a, m)
  | .error e => .error e

mutual
/-- Kernel-reducible executable expression evaluator (mirroring `EvalExp`). -/
def execExp (dl : DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap Identifier RegisterValue) (mem : MemoryState)
    (ty : LlvmType) (e : Exp) (o : OracleState) :
    Except ExecError (RegisterValue × MemoryState × OracleState) :=
  match e with
  | .identifier (.local_id id) =>
    match regs.get? (.local_id id) with
    | some v => .ok (v, mem, o)
    | none => .error (.staticError s!"unknown local id [%{id}]")
  | .identifier (.global_id id) =>
    let as := match ty with | .ptr a => a | _ => 0
    match mem.globalAddrs.get? id with
    | some p => .ok (.ptr as (.value p), mem, o)
    | none =>
      match mem.funcAddrs.get? id with
      | some p => .ok (.ptr as (.value p), mem, o)
      | none => .error (.staticError s!"unknown global id [@{id}]")
  | .bool b =>
    match ty with
    | .int 1 => .ok (.bv 1 (.value (BitVec.ofBool b)), mem, o)
    | _ => .error (.staticError s!"invalid type for bool literal: expected i1, found {ty.print}")
  | .int x =>
    match ty with
    | .int w => .ok (.bv w (.value (BitVec.ofInt w x)), mem, o)
    | _ => .error (.staticError s!"invalid type for int literal: found {ty.print}")
  | .floatBits bits =>
    match ty with
    | .float ft => .ok (.float ft (.value (IEEEFloat.ofNatBits bits)), mem, o)
    | _ => .error (.staticError s!"invalid type for float bit literal: found {ty.print}")
  | .floatDec neg m e10 =>
    match ty with
    | .float ft => .ok (.float ft (.value (IEEEFloat.ofDecimal ft.format cfg.roundingMode neg m e10)), mem, o)
    | _ => .error (.staticError s!"invalid type for float decimal literal: found {ty.print}")
  | .null =>
    match ty with
    | .ptr as => .ok (.ptr as (.value (Pointer.null dl as)), mem, o)
    | _ => .error (.staticError s!"`null` requires pointer type, found {ty.print}")
  | .zeroinitializer => .ok (RegisterValue.nullOf dl ty, mem, o)
  | .poison => .ok (RegisterValue.poisonOf ty, mem, o)
  | .undef =>
    match genUndefExec dl cfg ty o with
    | .ok (v, o') => .ok (v, mem, o')
    | .error err => .error err
  | .array elems =>
    match ty with
    | .array n elemTy =>
      if elems.length != n then
        .error (.staticError s!"array constant length mismatch: expected {n}, got {elems.length}")
      else
        match execExpList dl cfg regs mem elems o with
        | .ok (vals, m', o') => .ok (.array elemTy vals, m', o')
        | .error err => .error err
    | _ => .error (.staticError s!"array constant requires array type, found {ty.print}")
  | .struct packed fields =>
    match ty with
    | .struct _ fTys =>
      if fields.length != fTys.length then
        .error (.staticError s!"struct constant field count mismatch: expected {fTys.length}, got {fields.length}")
      else
        match execExpList dl cfg regs mem fields o with
        | .ok (vals, m', o') => .ok (.struct packed fTys vals, m', o')
        | .error err => .error err
    | _ => .error (.staticError s!"struct constant requires struct type, found {ty.print}")
  | .vector elems =>
    match ty with
    | .vector n elemTy =>
      if elems.length != n then
        .error (.staticError s!"vector constant length mismatch: expected {n}, got {elems.length}")
      else
        match execExpList dl cfg regs mem elems o with
        | .ok (vals, m', o') => .ok (.vector elemTy vals, m', o')
        | .error err => .error err
    | _ => .error (.staticError s!"vector constant requires vector type, found {ty.print}")
  | .splat (eTy, e0) =>
    match ty with
    | .vector n elemTy =>
      match execExp dl cfg regs mem eTy e0 o with
      | .ok (sv, m', o') => .ok (.vector elemTy (List.replicate n sv), m', o')
      | .error err => .error err
    | _ => .error (.staticError s!"splat constant requires vector type, found {ty.print}")
  | .gepConst flags baseTy (pTy, pExp) idxs =>
    match execExp dl cfg regs mem pTy pExp o with
    | .error err => .error err
    | .ok (baseVal, m1, o1) =>
      match execExpList dl cfg regs m1 idxs o1 with
      | .error err => .error err
      | .ok (idxVals, m2, o2) =>
        match evalGEPValuesPure dl m2 flags baseTy pTy baseVal idxVals with
        | .ok res => .ok (res, m2, o2)
        | .error err => .error err
  | .convConst op fromTy e0 toTy =>
    match execExp dl cfg regs mem fromTy e0 o with
    | .error err => .error err
    | .ok (val, m1, o1) => evalConversionExec dl cfg m1 op fromTy val toTy o1
  | .binConst op cTy e1 e2 =>
    match execExp dl cfg regs mem cTy e1 o with
    | .error err => .error err
    | .ok (v1, m1, o1) =>
      match execExp dl cfg regs m1 cTy e2 o1 with
      | .error err => .error err
      | .ok (v2, m2, o2) =>
        match liftBinaryPure cTy.scalarType v1 v2 (evalIntBinaryScalarPure op) with
        | .ok res => .ok (res, m2, o2)
        | .error err => .error err

/-- Kernel-reducible list expression evaluator (mirroring `EvalExpList`). -/
def execExpList (dl : DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap Identifier RegisterValue) (mem : MemoryState) :
    List (LlvmType × Exp) → OracleState →
    Except ExecError (List RegisterValue × MemoryState × OracleState)
  | [], o => .ok ([], mem, o)
  | (t, e) :: rest, o =>
    match execExp dl cfg regs mem t e o with
    | .error err => .error err
    | .ok (v, m1, o1) =>
      match execExpList dl cfg regs m1 rest o1 with
      | .error err => .error err
      | .ok (vs, m2, o2) => .ok (v :: vs, m2, o2)
end

/-! ### Soundness of `execExp` and `execExpList` -/

mutual
private theorem genUndefZeroExec_error_spec (dl : DataLayout) :
    ∀ (ty : LlvmType) {err : ExecError},
      genUndefZeroExec dl ty = .error err →
      ty.hasFunction = true ∧ ∃ msg, err = .staticError msg
  | .int _, _, h => by unfold genUndefZeroExec at h; cases h
  | .float _, _, h => by unfold genUndefZeroExec at h; cases h
  | .ptr _, _, h => by unfold genUndefZeroExec at h; cases h
  | .vector _ elem, _, h => by
    unfold genUndefZeroExec at h
    cases he : genUndefZeroExec dl elem with
    | ok _ => rw [he] at h; cases h
    | error e => rw [he] at h; cases h; exact genUndefZeroExec_error_spec dl elem he
  | .array _ elem, _, h => by
    unfold genUndefZeroExec at h
    cases he : genUndefZeroExec dl elem with
    | ok _ => rw [he] at h; cases h
    | error e => rw [he] at h; cases h; exact genUndefZeroExec_error_spec dl elem he
  | .struct _ fields, _, h => by
    unfold genUndefZeroExec at h
    cases hf : genUndefZeroListExec dl fields with
    | ok _ => rw [hf] at h; cases h
    | error e => rw [hf] at h; cases h; exact genUndefZeroListExec_error_spec dl fields hf
  | .function .., _, h | .named _, _, h => by unfold genUndefZeroExec at h; cases h; exact ⟨rfl, _, rfl⟩

private theorem genUndefZeroListExec_error_spec (dl : DataLayout) :
    ∀ (ts : List LlvmType) {err : ExecError},
      genUndefZeroListExec dl ts = .error err →
      LlvmType.hasFunctionList ts = true ∧ ∃ msg, err = .staticError msg
  | [], _, h => by unfold genUndefZeroListExec at h; cases h
  | t :: ts, _, h => by
    unfold genUndefZeroListExec at h
    cases h1 : genUndefZeroExec dl t with
    | error e =>
      rw [h1] at h; cases h
      obtain ⟨hf, msg, rfl⟩ := genUndefZeroExec_error_spec dl t h1
      exact ⟨by simp [hf], msg, rfl⟩
    | ok v =>
      rw [h1] at h
      cases h2 : genUndefZeroListExec dl ts with
      | ok _ => rw [h2] at h; cases h
      | error e =>
        rw [h2] at h; cases h
        obtain ⟨hf, msg, rfl⟩ := genUndefZeroListExec_error_spec dl ts h2
        exact ⟨by simp [hf], msg, rfl⟩
end

private theorem genUndefRepeatExec_error_spec {elem : LlvmType}
    {f : OracleState → Except ExecError (RegisterValue × OracleState)}
    (hf : ∀ o err, f o = .error err → elem.hasFunction = true ∧ ∃ msg, err = .staticError msg) :
    ∀ n o err, genUndefRepeatExec f n o = .error err →
      elem.hasFunction = true ∧ ∃ msg, err = .staticError msg
  | 0, _, _, h => by unfold genUndefRepeatExec at h; cases h
  | k + 1, o, err, h => by
    unfold genUndefRepeatExec at h
    cases h1 : f o with
    | error e => rw [h1] at h; cases h; exact hf o _ h1
    | ok p =>
      rw [h1] at h; obtain ⟨v, o1⟩ := p; dsimp only at h
      cases h2 : genUndefRepeatExec f k o1 with
      | ok _ => rw [h2] at h; cases h
      | error e => rw [h2] at h; cases h; exact genUndefRepeatExec_error_spec hf k o1 _ h2

mutual
private theorem genUndefNondetExec_error_spec (dl : DataLayout) :
    ∀ (ty : LlvmType) (o : OracleState) {err : ExecError},
      genUndefNondetExec dl ty o = .error err →
      ty.hasFunction = true ∧ ∃ msg, err = .staticError msg
  | .int w, o, _, h => by unfold genUndefNondetExec at h; cases o.nextBitVec w; cases h
  | .float ft, o, _, h => by unfold genUndefNondetExec at h; cases o.nextBitVec ft.bitWidth; cases h
  | .ptr as, o, _, h => by unfold genUndefNondetExec at h; dsimp only at h; cases h
  | .vector n elem, o, _, h => by
    unfold genUndefNondetExec at h
    cases hr : genUndefRepeatExec (genUndefNondetExec dl elem) n o with
    | ok _ => rw [hr] at h; cases h
    | error e =>
      rw [hr] at h; cases h
      exact genUndefRepeatExec_error_spec (fun o0 e0 h0 => genUndefNondetExec_error_spec dl elem o0 h0) n o _ hr
  | .array n elem, o, _, h => by
    unfold genUndefNondetExec at h
    cases hr : genUndefRepeatExec (genUndefNondetExec dl elem) n o with
    | ok _ => rw [hr] at h; cases h
    | error e =>
      rw [hr] at h; cases h
      exact genUndefRepeatExec_error_spec (fun o0 e0 h0 => genUndefNondetExec_error_spec dl elem o0 h0) n o _ hr
  | .struct _ fields, o, _, h => by
    unfold genUndefNondetExec at h
    cases hl : genUndefListExec dl fields o with
    | ok _ => rw [hl] at h; cases h
    | error e => rw [hl] at h; cases h; exact genUndefListExec_error_spec dl fields o hl
  | .function .., _, _, h | .named _, _, _, h => by unfold genUndefNondetExec at h; cases h; exact ⟨rfl, _, rfl⟩

private theorem genUndefListExec_error_spec (dl : DataLayout) :
    ∀ (ts : List LlvmType) (o : OracleState) {err : ExecError},
      genUndefListExec dl ts o = .error err →
      LlvmType.hasFunctionList ts = true ∧ ∃ msg, err = .staticError msg
  | [], _, _, h => by unfold genUndefListExec at h; cases h
  | t :: ts, o, _, h => by
    unfold genUndefListExec at h
    cases h1 : genUndefNondetExec dl t o with
    | error e =>
      rw [h1] at h; cases h
      obtain ⟨hf, msg, rfl⟩ := genUndefNondetExec_error_spec dl t o h1
      exact ⟨by simp [hf], msg, rfl⟩
    | ok p =>
      rw [h1] at h; obtain ⟨v, o1⟩ := p; dsimp only at h
      cases h2 : genUndefListExec dl ts o1 with
      | ok _ => rw [h2] at h; cases h
      | error e =>
        rw [h2] at h; cases h
        obtain ⟨hf, msg, rfl⟩ := genUndefListExec_error_spec dl ts o1 h2
        exact ⟨by simp [hf], msg, rfl⟩
end

private theorem genUndefExec_error_spec {dl cfg ty o err}
    (h : genUndefExec dl cfg ty o = .error err) :
    (cfg.undefMode = .disabled ∨ ty.hasFunction = true) ∧ ∃ msg, err = .staticError msg := by
  unfold genUndefExec at h
  cases hm : cfg.undefMode with
  | disabled => rw [hm] at h; cases h; exact ⟨Or.inl rfl, _, rfl⟩
  | zero =>
    rw [hm] at h
    cases hz : genUndefZeroExec dl ty with
    | ok _ => rw [hz] at h; cases h
    | error e =>
      rw [hz] at h; cases h
      obtain ⟨hf, msg, rfl⟩ := genUndefZeroExec_error_spec dl ty hz
      exact ⟨Or.inr hf, msg, rfl⟩
  | nondet =>
    rw [hm] at h
    obtain ⟨hf, msg, rfl⟩ := genUndefNondetExec_error_spec dl ty o h
    exact ⟨Or.inr hf, msg, rfl⟩

mutual
/-- Soundness of executable `execExp` with respect to relational `EvalExp`. -/
theorem execExp_sound (dl : DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap Identifier RegisterValue) :
    ∀ (mem : MemoryState) (ty : LlvmType) (e : Exp) (o : OracleState),
      EvalExp dl cfg regs mem ty e (stripOracle (execExp dl cfg regs mem ty e o))
  | mem, ty, .identifier (.local_id id), o => by
    unfold execExp
    cases hg : regs.get? (.local_id id) with
    | some v => exact EvalExp.leaf_ok (by simp [evalPureLeafExp?, hg])
    | none => exact EvalExp.leaf_err (by simp [evalPureLeafExp?, hg])
  | mem, ty, .identifier (.global_id id), o => by
    unfold execExp
    cases hg : mem.globalAddrs.get? id with
    | some p => exact EvalExp.leaf_ok (by cases ty <;> simp [evalPureLeafExp?, hg])
    | none =>
      cases hf : mem.funcAddrs.get? id with
      | some p => exact EvalExp.leaf_ok (by cases ty <;> simp [evalPureLeafExp?, hg, hf])
      | none => exact EvalExp.leaf_err (by simp [evalPureLeafExp?, hg, hf])
  | mem, ty, .bool b, o => by
    unfold execExp
    cases ty with
    | int w =>
      cases w with
      | zero => exact EvalExp.leaf_err (by simp [evalPureLeafExp?])
      | succ k =>
        cases k with
        | zero => exact EvalExp.leaf_ok (by simp [evalPureLeafExp?])
        | succ _ => exact EvalExp.leaf_err (by simp [evalPureLeafExp?])
    | _ => exact EvalExp.leaf_err (by simp [evalPureLeafExp?])
  | mem, ty, .int x, o => by
    unfold execExp
    cases ty with
    | int w => exact EvalExp.leaf_ok (by simp [evalPureLeafExp?])
    | _ => exact EvalExp.leaf_err (by simp [evalPureLeafExp?])
  | mem, ty, .floatBits bits, o => by
    unfold execExp
    cases ty with
    | float ft => exact EvalExp.leaf_ok (by simp [evalPureLeafExp?])
    | _ => exact EvalExp.leaf_err (by simp [evalPureLeafExp?])
  | mem, ty, .floatDec neg m e10, o => by
    unfold execExp
    cases ty with
    | float ft => exact EvalExp.leaf_ok (by simp [evalPureLeafExp?])
    | _ => exact EvalExp.leaf_err (by simp [evalPureLeafExp?])
  | mem, ty, .null, o => by
    unfold execExp
    cases ty with
    | ptr as => exact EvalExp.leaf_ok (by simp [evalPureLeafExp?])
    | _ => exact EvalExp.leaf_err (by simp [evalPureLeafExp?])
  | mem, ty, .zeroinitializer, o =>
    EvalExp.leaf_ok (by simp [evalPureLeafExp?])
  | mem, ty, .poison, o =>
    EvalExp.leaf_ok (by simp [evalPureLeafExp?])
  | mem, ty, .undef, o => by
    unfold execExp
    cases hu : genUndefExec dl cfg ty o with
    | ok p =>
      obtain ⟨v, o'⟩ := p
      obtain ⟨hallow, hrel⟩ := genUndefExec_sound hu
      exact EvalExp.undef_ok hallow hrel
    | error err =>
      obtain ⟨hbad, msg, rfl⟩ := genUndefExec_error_spec hu
      exact EvalExp.undef_err hbad
  | mem, ty, .array elems, o => by
    unfold execExp
    cases ty with
    | array n elemTy =>
      dsimp only
      by_cases hne : (elems.length != n) = true
      · rw [if_pos hne]
        exact EvalExp.array_len_err (by simpa [bne_iff_ne] using hne)
      · rw [if_neg hne]
        have hlen : elems.length = n := by simpa [bne_iff_ne] using hne
        have ih := execExpList_sound dl cfg regs mem elems o
        cases hl : execExpList dl cfg regs mem elems o with
        | ok p =>
          rw [hl] at ih; obtain ⟨vals, m', o'⟩ := p
          exact EvalExp.array_ok hlen ih
        | error err =>
          rw [hl] at ih
          exact EvalExp.array_err hlen ih
    | _ => exact EvalExp.array_ty_err rfl
  | mem, ty, .struct packed fields, o => by
    unfold execExp
    cases ty with
    | struct p fTys =>
      dsimp only
      by_cases hne : (fields.length != fTys.length) = true
      · rw [if_pos hne]
        exact EvalExp.struct_len_err (by simpa [bne_iff_ne] using hne)
      · rw [if_neg hne]
        have hlen : fields.length = fTys.length := by simpa [bne_iff_ne] using hne
        have ih := execExpList_sound dl cfg regs mem fields o
        cases hl : execExpList dl cfg regs mem fields o with
        | ok p =>
          rw [hl] at ih; obtain ⟨vals, m', o'⟩ := p
          exact EvalExp.struct_ok hlen ih
        | error err =>
          rw [hl] at ih
          exact EvalExp.struct_err hlen ih
    | _ => exact EvalExp.struct_ty_err rfl
  | mem, ty, .vector elems, o => by
    unfold execExp
    cases ty with
    | vector n elemTy =>
      dsimp only
      by_cases hne : (elems.length != n) = true
      · rw [if_pos hne]
        exact EvalExp.vector_len_err (by simpa [bne_iff_ne] using hne)
      · rw [if_neg hne]
        have hlen : elems.length = n := by simpa [bne_iff_ne] using hne
        have ih := execExpList_sound dl cfg regs mem elems o
        cases hl : execExpList dl cfg regs mem elems o with
        | ok p =>
          rw [hl] at ih; obtain ⟨vals, m', o'⟩ := p
          exact EvalExp.vector_ok hlen ih
        | error err =>
          rw [hl] at ih
          exact EvalExp.vector_err hlen ih
    | _ => exact EvalExp.vector_ty_err rfl
  | mem, ty, .splat (eTy, e0), o => by
    unfold execExp
    cases ty with
    | vector n elemTy =>
      have ih := execExp_sound dl cfg regs mem eTy e0 o
      cases he : execExp dl cfg regs mem eTy e0 o with
      | ok p =>
        rw [he] at ih; obtain ⟨sv, m', o'⟩ := p
        exact EvalExp.splat_ok ih
      | error err =>
        rw [he] at ih
        exact EvalExp.splat_err ih
    | _ => exact EvalExp.splat_ty_err rfl
  | mem, ty, .gepConst flags baseTy (pTy, pExp) idxs, o => by
    unfold execExp
    have ih1 := execExp_sound dl cfg regs mem pTy pExp o
    cases h1 : execExp dl cfg regs mem pTy pExp o with
    | error err => rw [h1] at ih1; exact EvalExp.gepConst_base_err ih1
    | ok p1 =>
      rw [h1] at ih1; obtain ⟨baseVal, m1, o1⟩ := p1; dsimp only at ih1 ⊢
      have ih2 := execExpList_sound dl cfg regs m1 idxs o1
      cases h2 : execExpList dl cfg regs m1 idxs o1 with
      | error err => rw [h2] at ih2; exact EvalExp.gepConst_idx_err ih1 ih2
      | ok p2 =>
        rw [h2] at ih2; obtain ⟨idxVals, m2, o2⟩ := p2; dsimp only at ih2 ⊢
        cases hgep : evalGEPValuesPure dl m2 flags baseTy pTy baseVal idxVals with
        | ok res => exact EvalExp.gepConst_ok ih1 ih2 hgep
        | error err => exact EvalExp.gepConst_eval_err ih1 ih2 hgep
  | mem, ty, .convConst op fromTy e0 toTy, o => by
    unfold execExp
    have ih := execExp_sound dl cfg regs mem fromTy e0 o
    cases h1 : execExp dl cfg regs mem fromTy e0 o with
    | error err => rw [h1] at ih; exact EvalExp.convConst_arg_err ih
    | ok p1 =>
      rw [h1] at ih; obtain ⟨val, m1, o1⟩ := p1; dsimp only at ih ⊢
      cases hc : evalConversionExec dl cfg m1 op fromTy val toTy o1 with
      | ok p2 =>
        obtain ⟨res, m2, o2⟩ := p2
        exact EvalExp.convConst_ok ih ⟨o1, o2, hc⟩
      | error err =>
        exact EvalExp.convConst_eval_err ih ⟨o1, hc⟩
  | mem, ty, .binConst op cTy e1 e2, o => by
    unfold execExp
    have ih1 := execExp_sound dl cfg regs mem cTy e1 o
    cases h1 : execExp dl cfg regs mem cTy e1 o with
    | error err => rw [h1] at ih1; exact EvalExp.binConst_lhs_err ih1
    | ok p1 =>
      rw [h1] at ih1; obtain ⟨v1, m1, o1⟩ := p1; dsimp only at ih1 ⊢
      have ih2 := execExp_sound dl cfg regs m1 cTy e2 o1
      cases h2 : execExp dl cfg regs m1 cTy e2 o1 with
      | error err => rw [h2] at ih2; exact EvalExp.binConst_rhs_err ih1 ih2
      | ok p2 =>
        rw [h2] at ih2; obtain ⟨v2, m2, o2⟩ := p2; dsimp only at ih2 ⊢
        cases hbin : liftBinaryPure cTy.scalarType v1 v2 (evalIntBinaryScalarPure op) with
        | ok res => exact EvalExp.binConst_ok ih1 ih2 hbin
        | error err => exact EvalExp.binConst_eval_err ih1 ih2 hbin

/-- Soundness of executable `execExpList` with respect to relational `EvalExpList`. -/
theorem execExpList_sound (dl : DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap Identifier RegisterValue) :
    ∀ (mem : MemoryState) (es : List (LlvmType × Exp)) (o : OracleState),
      EvalExpList dl cfg regs mem es (stripOracle (execExpList dl cfg regs mem es o))
  | mem, [], _ => EvalExpList.nil
  | mem, (t, e) :: rest, o => by
    unfold execExpList
    have ih1 := execExp_sound dl cfg regs mem t e o
    cases h1 : execExp dl cfg regs mem t e o with
    | error err => rw [h1] at ih1; exact EvalExpList.cons_head_err ih1
    | ok p1 =>
      rw [h1] at ih1; obtain ⟨v, m1, o1⟩ := p1; dsimp only at ih1 ⊢
      have ih2 := execExpList_sound dl cfg regs m1 rest o1
      cases h2 : execExpList dl cfg regs m1 rest o1 with
      | error err => rw [h2] at ih2; exact EvalExpList.cons_tail_err ih1 ih2
      | ok p2 =>
        rw [h2] at ih2; obtain ⟨vs, m2, o2⟩ := p2; dsimp only at ih2 ⊢
        exact EvalExpList.cons_ok ih1 ih2
end

/-! ### Executable Call-Arg, Phi, Callee, Jump, and Return Helpers -/

def execCallArgs (dl : DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap Identifier RegisterValue) (mem : MemoryState) :
    List (LlvmType × Exp × List ValueAttr) → OracleState →
    Except ExecError (List RegisterValue × MemoryState × OracleState)
  | [], o => .ok ([], mem, o)
  | (ty, e, attrs) :: rest, o =>
    match execExp dl cfg regs mem ty e o with
    | .error err => .error err
    | .ok (rawV, m1, o1) =>
      match applyValueAttrsPure dl m1 ty rawV attrs with
      | .error err => .error err
      | .ok v =>
        match execCallArgs dl cfg regs m1 rest o1 with
        | .error err => .error err
        | .ok (vs, m2, o2) => .ok (v :: vs, m2, o2)

theorem execCallArgs_sound (dl : DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap Identifier RegisterValue) :
    ∀ (mem : MemoryState) (args : List (LlvmType × Exp × List ValueAttr)) (o : OracleState),
      EvalCallArgs dl cfg regs mem args (stripOracle (execCallArgs dl cfg regs mem args o))
  | mem, [], _ => EvalCallArgs.nil
  | mem, (ty, e, attrs) :: rest, o => by
    unfold execCallArgs
    have ih1 := execExp_sound dl cfg regs mem ty e o
    cases h1 : execExp dl cfg regs mem ty e o with
    | error err => rw [h1] at ih1; exact EvalCallArgs.cons_exp_err ih1
    | ok p1 =>
      rw [h1] at ih1; obtain ⟨rawV, m1, o1⟩ := p1; dsimp only at ih1 ⊢
      cases hattr : applyValueAttrsPure dl m1 ty rawV attrs with
      | error err => exact EvalCallArgs.cons_attr_err ih1 hattr
      | ok v =>
        have ih2 := execCallArgs_sound dl cfg regs m1 rest o1
        cases h2 : execCallArgs dl cfg regs m1 rest o1 with
        | error err => rw [h2] at ih2; exact EvalCallArgs.cons_tail_err ih1 hattr ih2
        | ok p2 =>
          rw [h2] at ih2; obtain ⟨vs, m2, o2⟩ := p2; dsimp only at ih2 ⊢
          exact EvalCallArgs.cons_ok ih1 hattr ih2

def execPhis (dl : DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap Identifier RegisterValue) (predId : BlockId) (mem : MemoryState) :
    Code → OracleState → Except ExecError (List (RawId × RegisterValue) × MemoryState × OracleState)
  | [], o => .ok ([], mem, o)
  | (iid, instr) :: rest, o =>
    match instr with
    | .phi ty fmf incs =>
      match iid with
      | .void _ => .error (.staticError "phi instruction must have a local register id")
      | .id rid =>
        match incs.find? (fun (_, b) => b == predId) with
        | none => .error (.staticError s!"phi node %{rid} has no incoming value for predecessor %{predId}")
        | some (incExp, _) =>
          match execExp dl cfg regs mem ty incExp o with
          | .error err => .error err
          | .ok (rawV, m1, o1) =>
            match applyInputFMFExec fmf ty rawV o1 with
            | .error err => .error err
            | .ok (v, o2) =>
              match execPhis dl cfg regs predId m1 rest o2 with
              | .error err => .error err
              | .ok (ups, m2, o3) => .ok ((rid, v) :: ups, m2, o3)
    | _ => .error (.staticError "Non-phi instruction in phi prefix")

theorem execPhis_sound (dl : DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap Identifier RegisterValue) (predId : BlockId) :
    ∀ (mem : MemoryState) (phis : Code) (o : OracleState),
      EvalPhis dl cfg regs predId mem phis (stripOracle (execPhis dl cfg regs predId mem phis o))
  | mem, [], _ => EvalPhis.nil
  | mem, (iid, instr) :: rest, o => by
    unfold execPhis
    cases instr with
    | phi ty fmf incs =>
      dsimp only
      cases iid with
      | void n => exact EvalPhis.cons_void_err
      | id rid =>
        dsimp only
        cases hfind : incs.find? (fun (_, b) => b == predId) with
        | none => exact EvalPhis.cons_missing_pred hfind
        | some pair =>
          obtain ⟨incExp, b⟩ := pair; dsimp only
          have ih1 := execExp_sound dl cfg regs mem ty incExp o
          cases h1 : execExp dl cfg regs mem ty incExp o with
          | error err => rw [h1] at ih1; exact EvalPhis.cons_exp_err hfind ih1
          | ok p1 =>
            rw [h1] at ih1; obtain ⟨rawV, m1, o1⟩ := p1; dsimp only at ih1 ⊢
            cases hfmf : applyInputFMFExec fmf ty rawV o1 with
            | error err => exact EvalPhis.cons_fmf_err hfind ih1 ⟨o1, hfmf⟩
            | ok p2 =>
              obtain ⟨v, o2⟩ := p2; dsimp only
              have ih2 := execPhis_sound dl cfg regs predId m1 rest o2
              cases h2 : execPhis dl cfg regs predId m1 rest o2 with
              | error err => rw [h2] at ih2; exact EvalPhis.cons_tail_err hfind ih1 ⟨o1, o2, hfmf⟩ ih2
              | ok p3 =>
                rw [h2] at ih2; obtain ⟨ups, m2, o3⟩ := p3; dsimp only at ih2 ⊢
                exact EvalPhis.cons_ok hfind ih1 ⟨o1, o2, hfmf⟩ ih2
    | _ => exact EvalPhis.cons_nonphi_err (by intro _ _ _ h; cases h)

def execCallee (dl : DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap Identifier RegisterValue) (mem : MemoryState)
    (e : Exp) (o : OracleState) :
    Except ExecError (FunctionId × MemoryState × OracleState) :=
  match e with
  | .identifier (.global_id fid) => .ok (fid, mem, o)
  | other =>
    match execExp dl cfg regs mem (.ptr dl.programAddrSpace) other o with
    | .error err => .error err
    | .ok (ptrVal, m1, o1) =>
      match ptrVal with
      | .ptr _ .poison => .error (.immediateUB "Indirect call through poison function pointer")
      | .ptr _ (.value p) =>
        match m1.addrToFunc.get? p.addr.toNat with
        | some fid => .ok (fid, m1, o1)
        | none => .error (.immediateUB s!"Indirect call through invalid function pointer {p}")
      | _ => .error (.staticError "Invalid callee expression in call")

theorem execCallee_sound (dl : DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap Identifier RegisterValue) (mem : MemoryState)
    (e : Exp) (o : OracleState) :
    EvalCallee dl cfg regs mem e (stripOracle (execCallee dl cfg regs mem e o)) := by
  have hIndir : ∀ (hnot : ∀ fid', e ≠ .identifier (.global_id fid')),
      EvalCallee dl cfg regs mem e
        (stripOracle (match execExp dl cfg regs mem (.ptr dl.programAddrSpace) e o with
          | .error err => .error err
          | .ok (ptrVal, m1, o1) =>
            match ptrVal with
            | .ptr _ .poison => .error (.immediateUB "Indirect call through poison function pointer")
            | .ptr _ (.value p) =>
              match m1.addrToFunc.get? p.addr.toNat with
              | some fid => .ok (fid, m1, o1)
              | none => .error (.immediateUB s!"Indirect call through invalid function pointer {p}")
            | _ => .error (.staticError "Invalid callee expression in call"))) := by
    intro hnot
    have ih := execExp_sound dl cfg regs mem (.ptr dl.programAddrSpace) e o
    cases h1 : execExp dl cfg regs mem (.ptr dl.programAddrSpace) e o with
    | error err => rw [h1] at ih; exact EvalCallee.indirect_exp_err hnot ih
    | ok p1 =>
      rw [h1] at ih; obtain ⟨ptrVal, m1, o1⟩ := p1; dsimp only at ih ⊢
      cases ptrVal with
      | ptr as pv =>
        cases pv using PoisonOr.casesOn' with
        | poison => exact EvalCallee.indirect_poison hnot ih
        | value p =>
          dsimp only
          cases hg : m1.addrToFunc.get? p.addr.toNat with
          | some fid => exact EvalCallee.indirect_ok hnot ih hg
          | none => exact EvalCallee.indirect_bad_addr hnot ih hg
      | _ => exact EvalCallee.indirect_nonptr hnot ih (by intro _ _ h; cases h)
  cases e with
  | identifier id =>
    cases id with
    | global_id fid => exact EvalCallee.direct
    | local_id lid => exact hIndir (by intro _ h; cases h)
  | _ => exact hIndir (by intro _ h; cases h)

def execJump (st : MachineState) (frame : CallFrame) (callers : List CallFrame)
    (mem : MemoryState) (dest : BlockId) (o : OracleState) : Config × OracleState :=
  match frame.defn.findBlock? dest with
  | none => (.staticError s!"Unknown branch target label %{dest}", o)
  | some nextBlk =>
    match splitPhis nextBlk.code with
    | (phis, body) =>
      match execPhis st.dataLayout st.config frame.registers frame.curBlock mem phis o with
      | .error err => (Config.ofError err, o)
      | .ok (ups, mem', o') =>
        (.running (st.withFramesAndMemory
          (frame.jumpTo nextBlk.id body nextBlk.terminator (commitPhiUpdates frame.registers ups) :: callers) mem'), o')

theorem execJump_sound {st frame callers mem dest o c' o'}
    (h : execJump st frame callers mem dest o = (c', o')) :
    StepJump st frame callers mem dest c' := by
  unfold execJump at h
  cases hblk : frame.defn.findBlock? dest with
  | none => rw [hblk] at h; cases h; exact StepJump.missing_block hblk
  | some nextBlk =>
    rw [hblk] at h; dsimp only at h
    cases hsp : splitPhis nextBlk.code with
    | mk phis body =>
      rw [hsp] at h; dsimp only at h
      have ih := execPhis_sound st.dataLayout st.config frame.registers frame.curBlock mem phis o
      cases hp : execPhis st.dataLayout st.config frame.registers frame.curBlock mem phis o with
      | error err => rw [hp] at ih h; cases h; exact StepJump.phi_err hblk hsp ih
      | ok p =>
        rw [hp] at ih h; obtain ⟨ups, mem', o1⟩ := p; cases h
        exact StepJump.ok hblk hsp ih

def execRet (st : MachineState) (frame : CallFrame) (callers : List CallFrame)
    (retTy : LlvmRetType) (retVal : RegisterValue) (m1 : MemoryState) : Config :=
  let m2 := freeAllocaList m1 frame.frameAllocas
  match applyRetFMFAndAttrsPure st.dataLayout m2 retTy {} frame.defn.prototype.retAttrs retVal with
  | .error err => Config.ofError err
  | .ok retVal1 =>
    match callers with
    | [] => .halted retVal1 m2
    | caller :: restCallers =>
      match caller.returnDest? with
      | none => .staticError "Missing return continuation on call stack"
      | some rd =>
        match applyRetFMFAndAttrsPure st.dataLayout m2 rd.retTy rd.fmf rd.retAttrs retVal1 with
        | .error err => Config.ofError err
        | .ok retVal2 =>
          let regs' := match rd.retTy, rd.destId with
            | .ret _, .id rid => caller.registers.insert (.local_id rid) retVal2
            | _, _ => caller.registers
          .running (st.withFramesAndMemory (((caller.withRegisters regs').withReturnDest none) :: restCallers) m2)

theorem execRet_sound (st : MachineState) (frame : CallFrame) (callers : List CallFrame)
    (retTy : LlvmRetType) (retVal : RegisterValue) (m1 : MemoryState) :
    StepRet st frame callers retTy retVal m1 (execRet st frame callers retTy retVal m1) := by
  unfold execRet
  dsimp only
  cases h1 : applyRetFMFAndAttrsPure st.dataLayout (freeAllocaList m1 frame.frameAllocas)
      retTy {} frame.defn.prototype.retAttrs retVal with
  | error err => exact StepRet.callee_attr_err h1
  | ok retVal1 =>
    cases callers with
    | nil => exact StepRet.top_ok rfl h1
    | cons caller restCallers =>
      dsimp only
      cases hrd : caller.returnDest? with
      | none => exact StepRet.missing_dest rfl h1 hrd
      | some rd =>
        dsimp only
        cases h2 : applyRetFMFAndAttrsPure st.dataLayout (freeAllocaList m1 frame.frameAllocas)
            rd.retTy rd.fmf rd.retAttrs retVal1 with
        | error err => exact StepRet.caller_attr_err rfl h1 hrd h2
        | ok retVal2 => exact StepRet.call_ok rfl h1 hrd h2

/-! ### Executable Instruction, Terminator, and Single-Step Functions -/

/-- Kernel-reducible single-instruction step (mirroring `StepInstr`). -/
def execInstr (st : MachineState) (frame : CallFrame) (callers : List CallFrame)
    (iid : InstructionId) (rest : Code) (instr : Instruction) (o : OracleState) :
    Option TraceEvent × Config × OracleState :=
  let dl := st.dataLayout
  let cfg := st.config
  let regs := frame.registers
  match instr with
  | .intBinaryOp op ty e1 e2 =>
    match execExp dl cfg regs st.memory ty e1 o with
    | .error err => (none, Config.ofError err, o)
    | .ok (v1, m1, o1) =>
      match execExp dl cfg regs m1 ty e2 o1 with
      | .error err => (none, Config.ofError err, o1)
      | .ok (v2, m2, o2) =>
        match liftBinaryPure ty.scalarType v1 v2 (evalIntBinaryScalarPure op) with
        | .ok res => (none, finishRegInstr st frame callers rest iid res m2, o2)
        | .error err => (none, Config.ofError err, o2)
  | .floatUnaryOp op ty e =>
    match execExp dl cfg regs st.memory ty e o with
    | .error err => (none, Config.ofError err, o)
    | .ok (v, m1, o1) =>
      match evalFloatUnaryExec op ty v o1 with
      | .ok (res, o2) => (none, finishRegInstr st frame callers rest iid res m1, o2)
      | .error err => (none, Config.ofError err, o1)
  | .floatBinaryOp op ty e1 e2 =>
    match execExp dl cfg regs st.memory ty e1 o with
    | .error err => (none, Config.ofError err, o)
    | .ok (v1, m1, o1) =>
      match execExp dl cfg regs m1 ty e2 o1 with
      | .error err => (none, Config.ofError err, o1)
      | .ok (v2, m2, o2) =>
        match evalFloatBinaryExec cfg op ty v1 v2 o2 with
        | .ok (res, o3) => (none, finishRegInstr st frame callers rest iid res m2, o3)
        | .error err => (none, Config.ofError err, o2)
  | .icmp ss pred ty e1 e2 =>
    match execExp dl cfg regs st.memory ty e1 o with
    | .error err => (none, Config.ofError err, o)
    | .ok (v1, m1, o1) =>
      match execExp dl cfg regs m1 ty e2 o1 with
      | .error err => (none, Config.ofError err, o1)
      | .ok (v2, m2, o2) =>
        match liftBinaryPure .i1 v1 v2 (evalICmpScalarPure ss pred) with
        | .ok res => (none, finishRegInstr st frame callers rest iid res m2, o2)
        | .error err => (none, Config.ofError err, o2)
  | .fcmp fmf pred ty e1 e2 =>
    match execExp dl cfg regs st.memory ty e1 o with
    | .error err => (none, Config.ofError err, o)
    | .ok (v1, m1, o1) =>
      match execExp dl cfg regs m1 ty e2 o1 with
      | .error err => (none, Config.ofError err, o1)
      | .ok (v2, m2, o2) =>
        match evalFCmpExec cfg fmf pred v1 v2 o2 with
        | .ok (res, o3) => (none, finishRegInstr st frame callers rest iid res m2, o3)
        | .error err => (none, Config.ofError err, o2)
  | .conversionOp op fromTy e toTy =>
    match execExp dl cfg regs st.memory fromTy e o with
    | .error err => (none, Config.ofError err, o)
    | .ok (v, m1, o1) =>
      match evalConversionExec dl cfg m1 op fromTy v toTy o1 with
      | .ok (res, m2, o2) => (none, finishRegInstr st frame callers rest iid res m2, o2)
      | .error err => (none, Config.ofError err, o1)
  | .select fmf condTy cond valTy tv fv =>
    match execExp dl cfg regs st.memory condTy cond o with
    | .error err => (none, Config.ofError err, o)
    | .ok (cV, m1, o1) =>
      match execExp dl cfg regs m1 valTy tv o1 with
      | .error err => (none, Config.ofError err, o1)
      | .ok (tV, m2, o2) =>
        match execExp dl cfg regs m2 valTy fv o2 with
        | .error err => (none, Config.ofError err, o2)
        | .ok (fV, m3, o3) =>
          match evalSelectPure cV tV fV with
          | .error err => (none, Config.ofError err, o3)
          | .ok rawRes =>
            match applyInputFMFExec fmf valTy rawRes o3 with
            | .ok (res, o4) => (none, finishRegInstr st frame callers rest iid res m3, o4)
            | .error err => (none, Config.ofError err, o3)
  | .phi _ _ _ =>
    (none, .staticError "Unexpected phi instruction outside block entry", o)
  | .alloca allocTy numEl? align? addrSpace =>
    let cntRes : Except ExecError (Nat × MemoryState × OracleState) :=
      match numEl? with
      | none => .ok (1, st.memory, o)
      | some (nTy, nExp) =>
        match execExp dl cfg regs st.memory nTy nExp o with
        | .error err => .error err
        | .ok (nVal, m1, o1) =>
          match nVal with
          | .bv _ .poison => .error (.immediateUB "alloca with poison array size")
          | .bv _ (.value bv) => .ok (bv.toNat, m1, o1)
          | _ => .error (.staticError "alloca array size must be an integer")
    match cntRes with
    | .error err => (none, Config.ofError err, o)
    | .ok (count, m1, o1) =>
      let totalSize := dl.typeAllocSize allocTy * count
      let effAlign := align?.getD (dl.typeABIAlign allocTy)
      let name := match iid with | .id rid => rid.ToString | .void n => s!"alloca.{n}"
      match m1.allocate dl cfg totalSize effAlign name addrSpace .uninitialized .stack false with
      | .ok (obj, mem') =>
        (none, finishRegInstr st frame callers rest iid
          (.ptr addrSpace (.value (MemoryState.derivePointer dl obj)))
          mem' (obj.allocId :: frame.frameAllocas), o1)
      | .error err => (none, Config.ofError err, o1)
  | .load ty ptrTy ptrExp align? isVol noundef md =>
    match execExp dl cfg regs st.memory ptrTy ptrExp o with
    | .error err => (none, Config.ofError err, o)
    | .ok (ptrVal, m1, o1) =>
      match ptrVal with
      | .ptr _ .poison => (none, .ub "load through poison pointer", o1)
      | .ptr _ (.value p) =>
        let effAlign := align?.getD (dl.typeABIAlign ty)
        let storeSize := dl.typeStoreSize ty
        match m1.verifyMemAccess p storeSize effAlign false with
        | .error err => (none, Config.ofError err, o1)
        | .ok (mo, offset) =>
          let rawBytes := MemoryState.readObjectBytes mo offset storeSize
          let ev := if isVol then some (.volatileLoad mo.addrSpace p.addr.toNat rawBytes) else none
          match bytesToValue dl cfg rawBytes ty o1 with
          | (rawVal, hasUndef, o2) =>
            match applyValueAttrsPure dl m1 ty rawVal md with
            | .error err => (ev, Config.ofError err, o2)
            | .ok val =>
              if noundef && (hasUndef || val.containsPoison) then
                (ev, .ub "Loaded value violates !noundef (contains poison or undef bits)", o2)
              else
                (ev, finishRegInstr st frame callers rest iid val m1, o2)
      | _ => (none, .staticError s!"Expected pointer in load, got {ptrVal}", o1)
  | .store valTy valExp ptrTy ptrExp align? isVol =>
    match execExp dl cfg regs st.memory valTy valExp o with
    | .error err => (none, Config.ofError err, o)
    | .ok (val, m1, o1) =>
      match execExp dl cfg regs m1 ptrTy ptrExp o1 with
      | .error err => (none, Config.ofError err, o1)
      | .ok (ptrVal, m2, o2) =>
        match ptrVal with
        | .ptr _ .poison => (none, .ub "store through poison pointer", o2)
        | .ptr _ (.value p) =>
          let effAlign := align?.getD (dl.typeABIAlign valTy)
          let storeSize := dl.typeStoreSize valTy
          match m2.verifyMemAccess p storeSize effAlign true with
          | .error err => (none, Config.ofError err, o2)
          | .ok (mo, offset) =>
            let rawBytes := valueToBytes dl cfg val valTy
            let ev := if isVol then some (.volatileStore mo.addrSpace p.addr.toNat rawBytes) else none
            (ev, finishVoidInstr st frame callers rest (m2.writeObjectBytes mo.allocId offset rawBytes), o2)
        | _ => (none, .staticError s!"Expected pointer in store, got {ptrVal}", o2)
  | .getelementptr flags baseTy ptrTy ptrExp idxs =>
    match execExp dl cfg regs st.memory ptrTy ptrExp o with
    | .error err => (none, Config.ofError err, o)
    | .ok (baseVal, m1, o1) =>
      match execExpList dl cfg regs m1 idxs o1 with
      | .error err => (none, Config.ofError err, o1)
      | .ok (idxVals, m2, o2) =>
        match evalGEPValuesPure dl m2 flags baseTy ptrTy baseVal idxVals with
        | .ok res => (none, finishRegInstr st frame callers rest iid res m2, o2)
        | .error err => (none, Config.ofError err, o2)
  | .extractvalue aggTy aggExp idxs =>
    match execExp dl cfg regs st.memory aggTy aggExp o with
    | .error err => (none, Config.ofError err, o)
    | .ok (aggV, m1, o1) =>
      match extractValueAux aggV idxs with
      | .ok res => (none, finishRegInstr st frame callers rest iid res m1, o1)
      | .error err => (none, Config.ofError err, o1)
  | .insertvalue aggTy aggExp valTy valExp idxs =>
    match execExp dl cfg regs st.memory aggTy aggExp o with
    | .error err => (none, Config.ofError err, o)
    | .ok (aggV, m1, o1) =>
      match execExp dl cfg regs m1 valTy valExp o1 with
      | .error err => (none, Config.ofError err, o1)
      | .ok (insV, m2, o2) =>
        match insertValueAux aggV insV idxs with
        | .ok res => (none, finishRegInstr st frame callers rest iid res m2, o2)
        | .error err => (none, Config.ofError err, o2)
  | .extractelement vecTy vecExp idxTy idxExp =>
    match execExp dl cfg regs st.memory vecTy vecExp o with
    | .error err => (none, Config.ofError err, o)
    | .ok (vecV, m1, o1) =>
      match execExp dl cfg regs m1 idxTy idxExp o1 with
      | .error err => (none, Config.ofError err, o1)
      | .ok (idxV, m2, o2) =>
        match evalExtractElementPure vecV idxV with
        | .ok res => (none, finishRegInstr st frame callers rest iid res m2, o2)
        | .error err => (none, Config.ofError err, o2)
  | .insertelement vecTy vecExp valTy valExp idxTy idxExp =>
    match execExp dl cfg regs st.memory vecTy vecExp o with
    | .error err => (none, Config.ofError err, o)
    | .ok (vecV, m1, o1) =>
      match execExp dl cfg regs m1 valTy valExp o1 with
      | .error err => (none, Config.ofError err, o1)
      | .ok (valV, m2, o2) =>
        match execExp dl cfg regs m2 idxTy idxExp o2 with
        | .error err => (none, Config.ofError err, o2)
        | .ok (idxV, m3, o3) =>
          match evalInsertElementPure vecV valV idxV with
          | .ok res => (none, finishRegInstr st frame callers rest iid res m3, o3)
          | .error err => (none, Config.ofError err, o3)
  | .shufflevector vecTy e1 e2 mask =>
    match execExp dl cfg regs st.memory vecTy e1 o with
    | .error err => (none, Config.ofError err, o)
    | .ok (v1, m1, o1) =>
      match execExp dl cfg regs m1 vecTy e2 o1 with
      | .error err => (none, Config.ofError err, o1)
      | .ok (v2, m2, o2) =>
        match evalShuffleVectorPure v1 v2 mask with
        | .ok res => (none, finishRegInstr st frame callers rest iid res m2, o2)
        | .error err => (none, Config.ofError err, o2)
  | .freeze (ty, e) =>
    match execExp dl cfg regs st.memory ty e o with
    | .error err => (none, Config.ofError err, o)
    | .ok (val, m1, o1) =>
      match freezeValue dl cfg val o1 with
      | (frozen, o2) => (none, finishRegInstr st frame callers rest iid frozen m1, o2)
  | .call retTy fmf calleeExp args retAttrs =>
    match execCallArgs dl cfg regs st.memory args o with
    | .error err => (none, Config.ofError err, o)
    | .ok (argVals, m1, o1) =>
      match execCallee dl cfg regs m1 calleeExp o1 with
      | .error err => (none, Config.ofError err, o1)
      | .ok (fid, m2, o2) =>
        let fname := fid.ToString
        if isAllocLibcall fname then
          match execAllocLibcall dl cfg m2 fname retTy argVals with
          | some (.ok (rawRet, m3)) =>
            match applyRetFMFAndAttrsPure dl m3 retTy fmf retAttrs rawRet with
            | .ok finalRet => (none, finishCallResult st frame callers rest iid retTy finalRet m3, o2)
            | .error err => (none, Config.ofError err, o2)
          | some (.error err) => (none, Config.ofError err, o2)
          | none => (none, .staticError s!"Internal error: alloc libcall {fname}", o2)
        else
          match evalNonAllocIntrinsicExec? dl cfg m2 fname retTy fmf argVals o2 with
          | some (.ok (rawRet, m3, o3)) =>
            match applyRetFMFAndAttrsPure dl m3 retTy fmf retAttrs rawRet with
            | .ok finalRet => (none, finishCallResult st frame callers rest iid retTy finalRet m3, o3)
            | .error err => (none, Config.ofError err, o3)
          | some (.error err) => (none, Config.ofError err, o2)
          | none =>
            match st.functions.get? fid with
            | none => (none, .staticError s!"Call to undefined external function @{fid}", o2)
            | some calleeDef =>
              if cfg.maxStackDepth != 0 && st.frames.length ≥ cfg.maxStackDepth then
                (none, .resourceError .stackOverflow, o2)
              else
                match mkEntryFrameWithMem dl cfg m2 calleeDef argVals with
                | .error err => (none, Config.ofError err, o2)
                | .ok (calleeFrame, m3) =>
                  let caller' := (frame.advance rest frame.registers frame.frameAllocas).withReturnDest
                    (some { destId := iid, retTy := retTy, fmf := fmf, retAttrs := retAttrs })
                  (none, .running (st.withFramesAndMemory (calleeFrame :: caller' :: callers) m3), o2)

/-- Kernel-reducible block-terminator step (mirroring `StepTerm`). -/
def execTerm (st : MachineState) (frame : CallFrame) (callers : List CallFrame)
    (_tid : InstructionId) (term : Terminator) (o : OracleState) : Config × OracleState :=
  let dl := st.dataLayout
  let cfg := st.config
  let regs := frame.registers
  match term with
  | .retVoid =>
    if frame.defn.retType? = some .void then
      (execRet st frame callers .void .void st.memory, o)
    else
      (.staticError s!"Expected return type mismatch for ret void in @{frame.defn.prototype.name}", o)
  | .ret (ty, e) =>
    if frame.defn.retType? = some (.ret ty) then
      match execExp dl cfg regs st.memory ty e o with
      | .error err => (Config.ofError err, o)
      | .ok (retVal, m1, o1) => (execRet st frame callers (.ret ty) retVal m1, o1)
    else
      (.staticError s!"Expected return type mismatch for ret [{ty.print}] in @{frame.defn.prototype.name}", o)
  | .br dest =>
    execJump st frame callers st.memory dest o
  | .condBr condExp tDest fDest =>
    match execExp dl cfg regs st.memory .i1 condExp o with
    | .error err => (Config.ofError err, o)
    | .ok (condVal, m1, o1) =>
      match condVal with
      | .bv 1 .poison => (.ub "Branch on poison condition", o1)
      | .bv 1 (.value b) => execJump st frame callers m1 (if b != 0 then tDest else fDest) o1
      | other => (.staticError s!"Expected i1 condition in br, got {other}", o1)
  | .switch ty condExp defDest cases =>
    match execExp dl cfg regs st.memory ty condExp o with
    | .error err => (Config.ofError err, o)
    | .ok (condVal, m1, o1) =>
      match condVal with
      | .bv _ .poison => (.ub "Switch on poison condition", o1)
      | .bv w (.value bv) =>
        let dest := match cases.find? (fun (cv, _) => BitVec.ofInt w cv == bv) with
          | some (_, lbl) => lbl
          | none => defDest
        execJump st frame callers m1 dest o1
      | other => (.staticError s!"Expected integer condition in switch, got {other}", o1)
  | .unreachable =>
    (.ub "Executed unreachable instruction", o)

/-- Kernel-reducible single small-step transition (mirroring `Step`). -/
def execStep (o : OracleState) (c : Config) : Option TraceEvent × Config × OracleState :=
  match c with
  | .running st =>
    match st.frames with
    | [] => (none, .staticError "Empty call stack", o)
    | frame :: callers =>
      match frame.remainingCode with
      | (iid, instr) :: rest => execInstr st frame callers iid rest instr o
      | [] =>
        match frame.terminator with
        | (tid, term) =>
          match execTerm st frame callers tid term o with
          | (c', o') => (none, c', o')
  | other => (none, other, o)

/-! ### Full Soundness Theorems (`execInstr_sound`, `execTerm_sound`, `execStep_sound`, `runSteps_sound`) -/

private theorem execAllocLibcall_isSome_of_isAlloc {dl cfg mem name retTy argVals}
    (h : isAllocLibcall name = true) :
    ∃ res, execAllocLibcall dl cfg mem name retTy argVals = some res := by
  unfold isAllocLibcall at h
  simp only [Bool.or_eq_true] at h
  unfold execAllocLibcall
  rcases h with hm | hc
  · rw [if_pos hm]; exact ⟨_, rfl⟩
  · by_cases hm : (name == "malloc") = true
    · rw [if_pos hm]; exact ⟨_, rfl⟩
    · rw [if_neg hm, if_pos hc]; exact ⟨_, rfl⟩

/-- Soundness of executable `execInstr` with respect to relational `StepInstr`. -/
theorem execInstr_sound {st frame callers iid rest instr o ev c' o'}
    (hwf : MemoryState.WellFormed st.memory)
    (h : execInstr st frame callers iid rest instr o = (ev, c', o')) :
    StepInstr st frame callers iid rest instr ev c' := by
  unfold execInstr at h
  dsimp only at h
  cases instr with
  | intBinaryOp op ty e1 e2 =>
    dsimp only at h
    have ih1 := execExp_sound st.dataLayout st.config frame.registers st.memory ty e1 o
    cases h1 : execExp st.dataLayout st.config frame.registers st.memory ty e1 o with
    | error err => rw [h1] at ih1 h; cases h; exact StepInstr.intBinaryOp_e1_err ih1
    | ok p1 =>
      rw [h1] at ih1 h; obtain ⟨v1, m1, o1⟩ := p1; dsimp only at ih1 h
      have ih2 := execExp_sound st.dataLayout st.config frame.registers m1 ty e2 o1
      cases h2 : execExp st.dataLayout st.config frame.registers m1 ty e2 o1 with
      | error err => rw [h2] at ih2 h; cases h; exact StepInstr.intBinaryOp_e2_err ih1 ih2
      | ok p2 =>
        rw [h2] at ih2 h; obtain ⟨v2, m2, o2⟩ := p2; dsimp only at ih2 h
        cases hb : liftBinaryPure ty.scalarType v1 v2 (evalIntBinaryScalarPure op) with
        | ok res => rw [hb] at h; cases h; exact StepInstr.intBinaryOp_ok ih1 ih2 hb
        | error err => rw [hb] at h; cases h; exact StepInstr.intBinaryOp_eval_err ih1 ih2 hb
  | floatUnaryOp op ty e =>
    dsimp only at h
    have ih1 := execExp_sound st.dataLayout st.config frame.registers st.memory ty e o
    cases h1 : execExp st.dataLayout st.config frame.registers st.memory ty e o with
    | error err => rw [h1] at ih1 h; cases h; exact StepInstr.floatUnaryOp_e_err ih1
    | ok p1 =>
      rw [h1] at ih1 h; obtain ⟨v, m1, o1⟩ := p1; dsimp only at ih1 h
      cases hf : evalFloatUnaryExec op ty v o1 with
      | ok p2 => rw [hf] at h; obtain ⟨res, o2⟩ := p2; cases h; exact StepInstr.floatUnaryOp_ok ih1 ⟨_, _, hf⟩
      | error err => rw [hf] at h; cases h; exact StepInstr.floatUnaryOp_eval_err ih1 ⟨_, hf⟩
  | floatBinaryOp op ty e1 e2 =>
    dsimp only at h
    have ih1 := execExp_sound st.dataLayout st.config frame.registers st.memory ty e1 o
    cases h1 : execExp st.dataLayout st.config frame.registers st.memory ty e1 o with
    | error err => rw [h1] at ih1 h; cases h; exact StepInstr.floatBinaryOp_e1_err ih1
    | ok p1 =>
      rw [h1] at ih1 h; obtain ⟨v1, m1, o1⟩ := p1; dsimp only at ih1 h
      have ih2 := execExp_sound st.dataLayout st.config frame.registers m1 ty e2 o1
      cases h2 : execExp st.dataLayout st.config frame.registers m1 ty e2 o1 with
      | error err => rw [h2] at ih2 h; cases h; exact StepInstr.floatBinaryOp_e2_err ih1 ih2
      | ok p2 =>
        rw [h2] at ih2 h; obtain ⟨v2, m2, o2⟩ := p2; dsimp only at ih2 h
        cases hf : evalFloatBinaryExec st.config op ty v1 v2 o2 with
        | ok p3 => rw [hf] at h; obtain ⟨res, o3⟩ := p3; cases h; exact StepInstr.floatBinaryOp_ok ih1 ih2 ⟨_, _, hf⟩
        | error err => rw [hf] at h; cases h; exact StepInstr.floatBinaryOp_eval_err ih1 ih2 ⟨_, hf⟩
  | icmp ss pred ty e1 e2 =>
    dsimp only at h
    have ih1 := execExp_sound st.dataLayout st.config frame.registers st.memory ty e1 o
    cases h1 : execExp st.dataLayout st.config frame.registers st.memory ty e1 o with
    | error err => rw [h1] at ih1 h; cases h; exact StepInstr.icmp_e1_err ih1
    | ok p1 =>
      rw [h1] at ih1 h; obtain ⟨v1, m1, o1⟩ := p1; dsimp only at ih1 h
      have ih2 := execExp_sound st.dataLayout st.config frame.registers m1 ty e2 o1
      cases h2 : execExp st.dataLayout st.config frame.registers m1 ty e2 o1 with
      | error err => rw [h2] at ih2 h; cases h; exact StepInstr.icmp_e2_err ih1 ih2
      | ok p2 =>
        rw [h2] at ih2 h; obtain ⟨v2, m2, o2⟩ := p2; dsimp only at ih2 h
        cases hc : liftBinaryPure .i1 v1 v2 (evalICmpScalarPure ss pred) with
        | ok res => rw [hc] at h; cases h; exact StepInstr.icmp_ok ih1 ih2 hc
        | error err => rw [hc] at h; cases h; exact StepInstr.icmp_eval_err ih1 ih2 hc
  | fcmp fmf pred ty e1 e2 =>
    dsimp only at h
    have ih1 := execExp_sound st.dataLayout st.config frame.registers st.memory ty e1 o
    cases h1 : execExp st.dataLayout st.config frame.registers st.memory ty e1 o with
    | error err => rw [h1] at ih1 h; cases h; exact StepInstr.fcmp_e1_err ih1
    | ok p1 =>
      rw [h1] at ih1 h; obtain ⟨v1, m1, o1⟩ := p1; dsimp only at ih1 h
      have ih2 := execExp_sound st.dataLayout st.config frame.registers m1 ty e2 o1
      cases h2 : execExp st.dataLayout st.config frame.registers m1 ty e2 o1 with
      | error err => rw [h2] at ih2 h; cases h; exact StepInstr.fcmp_e2_err ih1 ih2
      | ok p2 =>
        rw [h2] at ih2 h; obtain ⟨v2, m2, o2⟩ := p2; dsimp only at ih2 h
        cases hf : evalFCmpExec st.config fmf pred v1 v2 o2 with
        | ok p3 => rw [hf] at h; obtain ⟨res, o3⟩ := p3; cases h; exact StepInstr.fcmp_ok ih1 ih2 ⟨_, _, hf⟩
        | error err => rw [hf] at h; cases h; exact StepInstr.fcmp_eval_err ih1 ih2 ⟨_, hf⟩
  | conversionOp op fromTy e toTy =>
    dsimp only at h
    have ih1 := execExp_sound st.dataLayout st.config frame.registers st.memory fromTy e o
    cases h1 : execExp st.dataLayout st.config frame.registers st.memory fromTy e o with
    | error err => rw [h1] at ih1 h; cases h; exact StepInstr.conversionOp_e_err ih1
    | ok p1 =>
      rw [h1] at ih1 h; obtain ⟨v, m1, o1⟩ := p1; dsimp only at ih1 h
      cases hc : evalConversionExec st.dataLayout st.config m1 op fromTy v toTy o1 with
      | ok p2 => rw [hc] at h; obtain ⟨res, m2, o2⟩ := p2; cases h; exact StepInstr.conversionOp_ok ih1 ⟨_, _, hc⟩
      | error err => rw [hc] at h; cases h; exact StepInstr.conversionOp_eval_err ih1 ⟨_, hc⟩
  | select fmf condTy cond valTy tv fv =>
    dsimp only at h
    have ih1 := execExp_sound st.dataLayout st.config frame.registers st.memory condTy cond o
    cases h1 : execExp st.dataLayout st.config frame.registers st.memory condTy cond o with
    | error err => rw [h1] at ih1 h; cases h; exact StepInstr.select_cond_err ih1
    | ok p1 =>
      rw [h1] at ih1 h; obtain ⟨cV, m1, o1⟩ := p1; dsimp only at ih1 h
      have ih2 := execExp_sound st.dataLayout st.config frame.registers m1 valTy tv o1
      cases h2 : execExp st.dataLayout st.config frame.registers m1 valTy tv o1 with
      | error err => rw [h2] at ih2 h; cases h; exact StepInstr.select_tv_err ih1 ih2
      | ok p2 =>
        rw [h2] at ih2 h; obtain ⟨tV, m2, o2⟩ := p2; dsimp only at ih2 h
        have ih3 := execExp_sound st.dataLayout st.config frame.registers m2 valTy fv o2
        cases h3 : execExp st.dataLayout st.config frame.registers m2 valTy fv o2 with
        | error err => rw [h3] at ih3 h; cases h; exact StepInstr.select_fv_err ih1 ih2 ih3
        | ok p3 =>
          rw [h3] at ih3 h; obtain ⟨fV, m3, o3⟩ := p3; dsimp only at ih3 h
          cases hs : evalSelectPure cV tV fV with
          | error err => rw [hs] at h; cases h; exact StepInstr.select_eval_err ih1 ih2 ih3 hs
          | ok rawRes =>
            rw [hs] at h; dsimp only at h
            cases hfmf : applyInputFMFExec fmf valTy rawRes o3 with
            | error err => rw [hfmf] at h; cases h; exact StepInstr.select_fmf_err ih1 ih2 ih3 hs ⟨_, hfmf⟩
            | ok p4 => rw [hfmf] at h; obtain ⟨res, o4⟩ := p4; cases h; exact StepInstr.select_ok ih1 ih2 ih3 hs ⟨_, _, hfmf⟩
  | phi ty fmf incs =>
    dsimp only at h
    cases h; exact StepInstr.stray_phi
  | alloca allocTy numEl? align? addrSpace =>
    dsimp only at h
    have finishAlloca : ∀ (count : Nat) (m1 : MemoryState) (o1 : OracleState),
        MemoryState.WellFormed m1 →
        (match (generalizing := false) numEl? with
          | none => count = 1 ∧ m1 = st.memory
          | some (nTy, nExp) => ∃ (w : Nat) (bv : BitVec w),
              EvalExp st.dataLayout st.config frame.registers st.memory nTy nExp (.ok (.bv w (.value bv), m1)) ∧
              count = bv.toNat) →
        (match m1.allocate st.dataLayout st.config (st.dataLayout.typeAllocSize allocTy * count)
            (align?.getD (st.dataLayout.typeABIAlign allocTy))
            (match (generalizing := false) iid with | .id rid => rid.ToString | .void n => s!"alloca.{n}")
            addrSpace .uninitialized .stack false with
          | .ok (obj, mem') =>
            (none, finishRegInstr st frame callers rest iid
              (.ptr addrSpace (.value (MemoryState.derivePointer st.dataLayout obj)))
              mem' (obj.allocId :: frame.frameAllocas), o1)
          | .error err => (none, Config.ofError err, o1)) = (ev, c', o') →
        StepInstr st frame callers iid rest (.alloca allocTy numEl? align? addrSpace) ev c' := by
      intro count m1 o1 hwf1 hcnt ha
      cases halloc : m1.allocate st.dataLayout st.config (st.dataLayout.typeAllocSize allocTy * count)
          (align?.getD (st.dataLayout.typeABIAlign allocTy))
          (match (generalizing := false) iid with | .id rid => rid.ToString | .void n => s!"alloca.{n}")
          addrSpace .uninitialized .stack false with
      | ok p =>
        rw [halloc] at ha; obtain ⟨obj, mem'⟩ := p; cases ha
        cases numEl? with
        | none => exact StepInstr.alloca_ok hcnt (MemoryState.allocate_satisfies_AllocSpec hwf1 halloc)
        | some p => exact StepInstr.alloca_ok hcnt (MemoryState.allocate_satisfies_AllocSpec hwf1 halloc)
      | error err =>
        rw [halloc] at ha; cases ha
        rcases MemoryState.allocate_error_cases halloc with ⟨rfl, hoom⟩ | ⟨msg, rfl, hsz⟩
        · cases numEl? with
          | none => exact StepInstr.alloca_oom hcnt hoom
          | some p => exact StepInstr.alloca_oom hcnt hoom
        · cases numEl? with
          | none => exact StepInstr.alloca_bad_size hcnt hsz
          | some p => exact StepInstr.alloca_bad_size hcnt hsz
    cases numEl? with
    | none =>
      dsimp only at h
      exact finishAlloca 1 st.memory o hwf ⟨rfl, rfl⟩ h
    | some pair =>
      obtain ⟨nTy, nExp⟩ := pair
      dsimp only at h
      have ih := execExp_sound st.dataLayout st.config frame.registers st.memory nTy nExp o
      cases h1 : execExp st.dataLayout st.config frame.registers st.memory nTy nExp o with
      | error err => rw [h1] at ih h; cases h; exact StepInstr.alloca_count_err ih
      | ok p1 =>
        rw [h1] at ih h; obtain ⟨nVal, m1, o1⟩ := p1; dsimp only at ih h
        cases nVal with
        | bv w iv =>
          cases iv using PoisonOr.casesOn' with
          | poison => dsimp only at h; cases h; exact StepInstr.alloca_count_poison ih
          | value bv =>
            dsimp only at h
            exact finishAlloca bv.toNat m1 o1 (EvalExp.preserves_wf hwf ih) ⟨w, bv, ih, rfl⟩ h
        | _ => dsimp only at h; cases h; exact StepInstr.alloca_count_nonint ih (by intro _ _ heq; cases heq)
  | load ty ptrTy ptrExp align? isVol noundef md =>
    dsimp only at h
    have ih1 := execExp_sound st.dataLayout st.config frame.registers st.memory ptrTy ptrExp o
    cases h1 : execExp st.dataLayout st.config frame.registers st.memory ptrTy ptrExp o with
    | error err => rw [h1] at ih1 h; cases h; exact StepInstr.load_ptr_err ih1
    | ok p1 =>
      rw [h1] at ih1 h; obtain ⟨ptrVal, m1, o1⟩ := p1; dsimp only at ih1 h
      cases ptrVal with
      | ptr as pv =>
        cases pv using PoisonOr.casesOn' with
        | poison => cases h; exact StepInstr.load_ptr_poison ih1
        | value p =>
          dsimp only at h
          cases hver : m1.verifyMemAccess p (st.dataLayout.typeStoreSize ty)
              (align?.getD (st.dataLayout.typeABIAlign ty)) false with
          | error err => rw [hver] at h; cases h; exact StepInstr.load_mem_err ih1 hver
          | ok pm =>
            rw [hver] at h; obtain ⟨mo, offset⟩ := pm; dsimp only at h
            cases hbtv : bytesToValue st.dataLayout st.config
                (MemoryState.readObjectBytes mo offset (st.dataLayout.typeStoreSize ty)) ty o1 with
            | mk rawVal restP =>
              obtain ⟨hasUndef, o2⟩ := restP
              rw [hbtv] at h; dsimp only at h
              have hrel := bytesToValue_satisfies_rel hbtv
              cases hmd : applyValueAttrsPure st.dataLayout m1 ty rawVal md with
              | error err => rw [hmd] at h; cases h; exact StepInstr.load_md_err ih1 hver hrel hmd
              | ok val =>
                rw [hmd] at h; dsimp only at h
                by_cases hbad : (noundef && (hasUndef || val.containsPoison)) = true
                · rw [if_pos hbad] at h; cases h
                  simp only [Bool.and_eq_true, Bool.or_eq_true] at hbad
                  obtain ⟨rfl, hup⟩ := hbad
                  exact StepInstr.load_noundef_ub ih1 hver hrel hmd hup
                · rw [if_neg hbad] at h; cases h
                  exact StepInstr.load_ok ih1 hver hrel hmd (by
                    intro hn
                    simp only [hn, Bool.true_and, Bool.or_eq_true, not_or] at hbad
                    exact ⟨Bool.eq_false_iff.mpr hbad.1, Bool.eq_false_iff.mpr hbad.2⟩)
      | _ => cases h; exact StepInstr.load_ptr_nonptr ih1 (by intro _ _ heq; cases heq)
  | store valTy valExp ptrTy ptrExp align? isVol =>
    dsimp only at h
    have ih1 := execExp_sound st.dataLayout st.config frame.registers st.memory valTy valExp o
    cases h1 : execExp st.dataLayout st.config frame.registers st.memory valTy valExp o with
    | error err => rw [h1] at ih1 h; cases h; exact StepInstr.store_val_err ih1
    | ok p1 =>
      rw [h1] at ih1 h; obtain ⟨val, m1, o1⟩ := p1; dsimp only at ih1 h
      have ih2 := execExp_sound st.dataLayout st.config frame.registers m1 ptrTy ptrExp o1
      cases h2 : execExp st.dataLayout st.config frame.registers m1 ptrTy ptrExp o1 with
      | error err => rw [h2] at ih2 h; cases h; exact StepInstr.store_ptr_err ih1 ih2
      | ok p2 =>
        rw [h2] at ih2 h; obtain ⟨ptrVal, m2, o2⟩ := p2; dsimp only at ih2 h
        cases ptrVal with
        | ptr as pv =>
          cases pv using PoisonOr.casesOn' with
          | poison => cases h; exact StepInstr.store_ptr_poison ih1 ih2
          | value p =>
            dsimp only at h
            cases hver : m2.verifyMemAccess p (st.dataLayout.typeStoreSize valTy)
                (align?.getD (st.dataLayout.typeABIAlign valTy)) true with
            | error err => rw [hver] at h; cases h; exact StepInstr.store_mem_err ih1 ih2 hver
            | ok pm =>
              rw [hver] at h; obtain ⟨mo, offset⟩ := pm; cases h
              exact StepInstr.store_ok ih1 ih2 hver
        | _ => cases h; exact StepInstr.store_ptr_nonptr ih1 ih2 (by intro _ _ heq; cases heq)
  | getelementptr flags baseTy ptrTy ptrExp idxs =>
    dsimp only at h
    have ih1 := execExp_sound st.dataLayout st.config frame.registers st.memory ptrTy ptrExp o
    cases h1 : execExp st.dataLayout st.config frame.registers st.memory ptrTy ptrExp o with
    | error err => rw [h1] at ih1 h; cases h; exact StepInstr.gep_base_err ih1
    | ok p1 =>
      rw [h1] at ih1 h; obtain ⟨baseVal, m1, o1⟩ := p1; dsimp only at ih1 h
      have ih2 := execExpList_sound st.dataLayout st.config frame.registers m1 idxs o1
      cases h2 : execExpList st.dataLayout st.config frame.registers m1 idxs o1 with
      | error err => rw [h2] at ih2 h; cases h; exact StepInstr.gep_idx_err ih1 ih2
      | ok p2 =>
        rw [h2] at ih2 h; obtain ⟨idxVals, m2, o2⟩ := p2; dsimp only at ih2 h
        cases hg : evalGEPValuesPure st.dataLayout m2 flags baseTy ptrTy baseVal idxVals with
        | ok res => rw [hg] at h; cases h; exact StepInstr.gep_ok ih1 ih2 hg
        | error err => rw [hg] at h; cases h; exact StepInstr.gep_eval_err ih1 ih2 hg
  | extractvalue aggTy aggExp idxs =>
    dsimp only at h
    have ih1 := execExp_sound st.dataLayout st.config frame.registers st.memory aggTy aggExp o
    cases h1 : execExp st.dataLayout st.config frame.registers st.memory aggTy aggExp o with
    | error err => rw [h1] at ih1 h; cases h; exact StepInstr.extractvalue_e_err ih1
    | ok p1 =>
      rw [h1] at ih1 h; obtain ⟨aggV, m1, o1⟩ := p1; dsimp only at ih1 h
      cases hev : extractValueAux aggV idxs with
      | ok res => rw [hev] at h; cases h; exact StepInstr.extractvalue_ok ih1 hev
      | error err => rw [hev] at h; cases h; exact StepInstr.extractvalue_eval_err ih1 hev
  | insertvalue aggTy aggExp valTy valExp idxs =>
    dsimp only at h
    have ih1 := execExp_sound st.dataLayout st.config frame.registers st.memory aggTy aggExp o
    cases h1 : execExp st.dataLayout st.config frame.registers st.memory aggTy aggExp o with
    | error err => rw [h1] at ih1 h; cases h; exact StepInstr.insertvalue_agg_err ih1
    | ok p1 =>
      rw [h1] at ih1 h; obtain ⟨aggV, m1, o1⟩ := p1; dsimp only at ih1 h
      have ih2 := execExp_sound st.dataLayout st.config frame.registers m1 valTy valExp o1
      cases h2 : execExp st.dataLayout st.config frame.registers m1 valTy valExp o1 with
      | error err => rw [h2] at ih2 h; cases h; exact StepInstr.insertvalue_val_err ih1 ih2
      | ok p2 =>
        rw [h2] at ih2 h; obtain ⟨insV, m2, o2⟩ := p2; dsimp only at ih2 h
        cases hev : insertValueAux aggV insV idxs with
        | ok res => rw [hev] at h; cases h; exact StepInstr.insertvalue_ok ih1 ih2 hev
        | error err => rw [hev] at h; cases h; exact StepInstr.insertvalue_eval_err ih1 ih2 hev
  | extractelement vecTy vecExp idxTy idxExp =>
    dsimp only at h
    have ih1 := execExp_sound st.dataLayout st.config frame.registers st.memory vecTy vecExp o
    cases h1 : execExp st.dataLayout st.config frame.registers st.memory vecTy vecExp o with
    | error err => rw [h1] at ih1 h; cases h; exact StepInstr.extractelement_vec_err ih1
    | ok p1 =>
      rw [h1] at ih1 h; obtain ⟨vecV, m1, o1⟩ := p1; dsimp only at ih1 h
      have ih2 := execExp_sound st.dataLayout st.config frame.registers m1 idxTy idxExp o1
      cases h2 : execExp st.dataLayout st.config frame.registers m1 idxTy idxExp o1 with
      | error err => rw [h2] at ih2 h; cases h; exact StepInstr.extractelement_idx_err ih1 ih2
      | ok p2 =>
        rw [h2] at ih2 h; obtain ⟨idxV, m2, o2⟩ := p2; dsimp only at ih2 h
        cases hev : evalExtractElementPure vecV idxV with
        | ok res => rw [hev] at h; cases h; exact StepInstr.extractelement_ok ih1 ih2 hev
        | error err => rw [hev] at h; cases h; exact StepInstr.extractelement_eval_err ih1 ih2 hev
  | insertelement vecTy vecExp valTy valExp idxTy idxExp =>
    dsimp only at h
    have ih1 := execExp_sound st.dataLayout st.config frame.registers st.memory vecTy vecExp o
    cases h1 : execExp st.dataLayout st.config frame.registers st.memory vecTy vecExp o with
    | error err => rw [h1] at ih1 h; cases h; exact StepInstr.insertelement_vec_err ih1
    | ok p1 =>
      rw [h1] at ih1 h; obtain ⟨vecV, m1, o1⟩ := p1; dsimp only at ih1 h
      have ih2 := execExp_sound st.dataLayout st.config frame.registers m1 valTy valExp o1
      cases h2 : execExp st.dataLayout st.config frame.registers m1 valTy valExp o1 with
      | error err => rw [h2] at ih2 h; cases h; exact StepInstr.insertelement_val_err ih1 ih2
      | ok p2 =>
        rw [h2] at ih2 h; obtain ⟨valV, m2, o2⟩ := p2; dsimp only at ih2 h
        have ih3 := execExp_sound st.dataLayout st.config frame.registers m2 idxTy idxExp o2
        cases h3 : execExp st.dataLayout st.config frame.registers m2 idxTy idxExp o2 with
        | error err => rw [h3] at ih3 h; cases h; exact StepInstr.insertelement_idx_err ih1 ih2 ih3
        | ok p3 =>
          rw [h3] at ih3 h; obtain ⟨idxV, m3, o3⟩ := p3; dsimp only at ih3 h
          cases hev : evalInsertElementPure vecV valV idxV with
          | ok res => rw [hev] at h; cases h; exact StepInstr.insertelement_ok ih1 ih2 ih3 hev
          | error err => rw [hev] at h; cases h; exact StepInstr.insertelement_eval_err ih1 ih2 ih3 hev
  | shufflevector vecTy e1 e2 mask =>
    dsimp only at h
    have ih1 := execExp_sound st.dataLayout st.config frame.registers st.memory vecTy e1 o
    cases h1 : execExp st.dataLayout st.config frame.registers st.memory vecTy e1 o with
    | error err => rw [h1] at ih1 h; cases h; exact StepInstr.shufflevector_e1_err ih1
    | ok p1 =>
      rw [h1] at ih1 h; obtain ⟨v1, m1, o1⟩ := p1; dsimp only at ih1 h
      have ih2 := execExp_sound st.dataLayout st.config frame.registers m1 vecTy e2 o1
      cases h2 : execExp st.dataLayout st.config frame.registers m1 vecTy e2 o1 with
      | error err => rw [h2] at ih2 h; cases h; exact StepInstr.shufflevector_e2_err ih1 ih2
      | ok p2 =>
        rw [h2] at ih2 h; obtain ⟨v2, m2, o2⟩ := p2; dsimp only at ih2 h
        cases hev : evalShuffleVectorPure v1 v2 mask with
        | ok res => rw [hev] at h; cases h; exact StepInstr.shufflevector_ok ih1 ih2 hev
        | error err => rw [hev] at h; cases h; exact StepInstr.shufflevector_eval_err ih1 ih2 hev
  | freeze pair =>
    dsimp only at h
    obtain ⟨ty, e⟩ := pair
    have ih1 := execExp_sound st.dataLayout st.config frame.registers st.memory ty e o
    cases h1 : execExp st.dataLayout st.config frame.registers st.memory ty e o with
    | error err => rw [h1] at ih1 h; cases h; exact StepInstr.freeze_err ih1
    | ok p1 =>
      rw [h1] at ih1 h; obtain ⟨val, m1, o1⟩ := p1; dsimp only at ih1 h
      have hfr := freezeValue_sound st.dataLayout st.config val o1
      cases hfz : freezeValue st.dataLayout st.config val o1 with
      | mk frozen o2 =>
        rw [hfz] at hfr h; cases h
        exact StepInstr.freeze_ok ih1 hfr
  | call retTy fmf calleeExp args retAttrs =>
    dsimp only at h
    have iha := execCallArgs_sound st.dataLayout st.config frame.registers st.memory args o
    cases ha : execCallArgs st.dataLayout st.config frame.registers st.memory args o with
    | error err => rw [ha] at iha h; cases h; exact StepInstr.call_args_err iha
    | ok pa =>
      rw [ha] at iha h; obtain ⟨argVals, m1, o1⟩ := pa; dsimp only at iha h
      have hwf1 := EvalCallArgs.preserves_wf hwf iha
      have ihc := execCallee_sound st.dataLayout st.config frame.registers m1 calleeExp o1
      cases hc : execCallee st.dataLayout st.config frame.registers m1 calleeExp o1 with
      | error err => rw [hc] at ihc h; cases h; exact StepInstr.call_callee_err iha ihc
      | ok pc =>
        rw [hc] at ihc h; obtain ⟨fid, m2, o2⟩ := pc; dsimp only at ihc h
        have hwf2 := EvalCallee.preserves_wf hwf1 ihc
        by_cases halloc : isAllocLibcall fid.ToString = true
        · rw [if_pos halloc] at h
          obtain ⟨res, hres⟩ := execAllocLibcall_isSome_of_isAlloc (dl := st.dataLayout)
            (cfg := st.config) (mem := m2) (retTy := retTy) (argVals := argVals) halloc
          rw [hres] at h
          have hspec := execAllocLibcall_sound hwf2 hres
          cases res with
          | error err => cases h; exact StepInstr.call_alloc_err iha ihc halloc hspec
          | ok pm =>
            obtain ⟨rawRet, m3⟩ := pm; dsimp only at h
            cases hattr : applyRetFMFAndAttrsPure st.dataLayout m3 retTy fmf retAttrs rawRet with
            | error err => rw [hattr] at h; cases h; exact StepInstr.call_alloc_retattr_err iha ihc halloc hspec hattr
            | ok finalRet => rw [hattr] at h; cases h; exact StepInstr.call_alloc_ok iha ihc halloc hspec hattr
        · have hallocF : isAllocLibcall fid.ToString = false := Bool.eq_false_iff.mpr halloc
          rw [if_neg halloc] at h
          cases hint : evalNonAllocIntrinsicExec? st.dataLayout st.config m2 fid.ToString retTy fmf argVals o2 with
          | some r =>
            rw [hint] at h
            cases r with
            | error err => cases h; exact StepInstr.call_intrinsic_err iha ihc hallocF ⟨_, hint⟩
            | ok pm =>
              obtain ⟨rawRet, m3, o3⟩ := pm; dsimp only at h
              cases hattr : applyRetFMFAndAttrsPure st.dataLayout m3 retTy fmf retAttrs rawRet with
              | error err =>
                rw [hattr] at h; cases h
                exact StepInstr.call_intrinsic_retattr_err iha ihc hallocF ⟨_, _, hint⟩ hattr
              | ok finalRet =>
                rw [hattr] at h; cases h
                exact StepInstr.call_intrinsic_ok iha ihc hallocF ⟨_, _, hint⟩ hattr
          | none =>
            rw [hint] at h; dsimp only at h
            have hnoneAll : ∀ o0, evalNonAllocIntrinsicExec? st.dataLayout st.config m2 fid.ToString retTy fmf argVals o0 = none :=
              fun o0 => evalNonAllocIntrinsicExec?_none_indep hint
            cases hfn : st.functions.get? fid with
            | none => rw [hfn] at h; cases h; exact StepInstr.call_external_err iha ihc hallocF hnoneAll hfn
            | some calleeDef =>
              rw [hfn] at h; dsimp only at h
              by_cases hov : (st.config.maxStackDepth != 0 && decide (st.frames.length ≥ st.config.maxStackDepth)) = true
              · rw [if_pos hov] at h; cases h
                simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hov
                exact StepInstr.call_user_overflow iha ihc hallocF hnoneAll hfn hov.1 hov.2
              · rw [if_neg hov] at h
                have hdepth : st.config.maxStackDepth == 0 ∨ st.frames.length < st.config.maxStackDepth := by
                  by_cases hz : st.config.maxStackDepth = 0
                  · exact Or.inl (by simp [hz])
                  · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_and] at hov
                    have := hov hz
                    exact Or.inr (by omega)
                cases hentry : mkEntryFrameWithMem st.dataLayout st.config m2 calleeDef argVals with
                | error err =>
                  rw [hentry] at h; cases h
                  exact StepInstr.call_user_entry_err iha ihc hallocF hnoneAll hfn hdepth hentry
                | ok pframe =>
                  obtain ⟨calleeFrame, m3⟩ := pframe
                  rw [hentry] at h; cases h
                  exact StepInstr.call_user_ok iha ihc hallocF hnoneAll hfn hdepth hentry

/-- Soundness of executable `execTerm` with respect to relational `StepTerm`. -/
theorem execTerm_sound {st frame callers tid term o c' o'}
    (h : execTerm st frame callers tid term o = (c', o')) :
    StepTerm st frame callers tid term c' := by
  unfold execTerm at h
  dsimp only at h
  cases term with
  | retVoid =>
    dsimp only at h
    by_cases hrt : frame.defn.retType? = some .void
    · rw [if_pos hrt] at h; cases h
      exact StepTerm.retVoid_ok hrt (execRet_sound ..)
    · rw [if_neg hrt] at h; cases h
      exact StepTerm.retVoid_ty_err hrt
  | ret pair =>
    dsimp only at h
    obtain ⟨ty, e⟩ := pair
    by_cases hrt : frame.defn.retType? = some (.ret ty)
    · rw [if_pos hrt] at h
      have ih := execExp_sound st.dataLayout st.config frame.registers st.memory ty e o
      cases he : execExp st.dataLayout st.config frame.registers st.memory ty e o with
      | error err => rw [he] at ih h; cases h; exact StepTerm.ret_exp_err hrt ih
      | ok p1 =>
        rw [he] at ih h; obtain ⟨retVal, m1, o1⟩ := p1; cases h
        exact StepTerm.ret_ok hrt ih (execRet_sound ..)
    · rw [if_neg hrt] at h; cases h
      exact StepTerm.ret_ty_err hrt
  | br dest =>
    dsimp only at h
    exact StepTerm.br_step (execJump_sound h)
  | condBr condExp tDest fDest =>
    dsimp only at h
    have ih := execExp_sound st.dataLayout st.config frame.registers st.memory .i1 condExp o
    cases he : execExp st.dataLayout st.config frame.registers st.memory .i1 condExp o with
    | error err => rw [he] at ih h; cases h; exact StepTerm.condBr_err ih
    | ok p1 =>
      rw [he] at ih h; obtain ⟨condVal, m1, o1⟩ := p1; dsimp only at ih h
      cases condVal with
      | bv w iv =>
        cases w with
        | zero => cases h; exact StepTerm.condBr_nonbool ih (by intro _ heq; cases heq)
        | succ k =>
          cases k with
          | zero =>
            cases iv using PoisonOr.casesOn' with
            | poison => cases h; exact StepTerm.condBr_poison ih
            | value b => exact StepTerm.condBr_ok ih (execJump_sound h)
          | succ _ => cases h; exact StepTerm.condBr_nonbool ih (by intro _ heq; cases heq)
      | _ => cases h; exact StepTerm.condBr_nonbool ih (by intro _ heq; cases heq)
  | switch ty condExp defDest casesList =>
    dsimp only at h
    have ih := execExp_sound st.dataLayout st.config frame.registers st.memory ty condExp o
    cases he : execExp st.dataLayout st.config frame.registers st.memory ty condExp o with
    | error err => rw [he] at ih h; cases h; exact StepTerm.switch_err ih
    | ok p1 =>
      rw [he] at ih h; obtain ⟨condVal, m1, o1⟩ := p1; dsimp only at ih h
      cases condVal with
      | bv w iv =>
        cases iv using PoisonOr.casesOn' with
        | poison => cases h; exact StepTerm.switch_poison ih
        | value bv => exact StepTerm.switch_ok ih (execJump_sound h)
      | _ => cases h; exact StepTerm.switch_nonint ih (by intro _ _ heq; cases heq)
  | unreachable =>
    dsimp only at h
    cases h; exact StepTerm.unreachable_ub

/-- Main single-step soundness theorem: every executable `execStep` from a well-formed running state
    is a valid transition of the primary relational `Step` specification. -/
theorem execStep_sound {st o ev c' o'}
    (hwf : MemoryState.WellFormed st.memory)
    (h : execStep o (.running st) = (ev, c', o')) :
    Step (.running st) ev c' := by
  unfold execStep at h
  dsimp only at h
  cases hf : st.frames with
  | nil => rw [hf] at h; cases h; exact Step.empty_stack hf
  | cons frame callers =>
    rw [hf] at h; dsimp only at h
    cases hc : frame.remainingCode with
    | cons hd rest =>
      rw [hc] at h; obtain ⟨iid, instr⟩ := hd; dsimp only at h
      exact Step.instr hf hc (execInstr_sound hwf h)
    | nil =>
      rw [hc] at h; dsimp only at h
      cases ht : frame.terminator with
      | mk tid term =>
        have h1 : frame.terminator.1 = tid := congrArg Prod.fst ht
        have h2 : frame.terminator.2 = term := congrArg Prod.snd ht
        rw [h1, h2] at h
        cases hterm : execTerm st frame callers tid term o with
        | mk c1 o1 =>
          rw [hterm] at h; cases h
          exact Step.term hf hc ht (execTerm_sound hterm)

theorem execStep_preserves_wf {c o ev c' o'}
    (hwf : Config.WellFormed c)
    (h : execStep o c = (ev, c', o')) :
    Config.WellFormed c' := by
  cases c with
  | running st => exact Step.preserves_wf hwf (execStep_sound hwf h)
  | halted _ _ | ub _ | staticError _ | resourceError _ =>
    unfold execStep at h; cases h; exact hwf

/-! ### Kernel-Reducible Multi-Step Driver (`runSteps`) & Soundness -/

/--
Fuel-bounded small-step execution loop using direct `Nat.rec` and strict constructor forcing
on `MachineState` and `OracleState` so Lean's call-by-name C++ kernel (`decide +kernel`)
runs in `O(actual_steps)` instead of `O(fuel)` or `O(k^N)`.
-/
def runSteps (fuel : Nat) : OracleState → Config → List TraceEvent × Config × OracleState :=
  Nat.rec
    (fun o c => ([], c, o))
    (fun _ rec o c =>
      match c with
      | .running ⟨frames, mem, cfg, dl, fns, decls⟩ =>
        match o with
        | ⟨ora, idx⟩ =>
          match execStep ⟨ora, idx⟩ (.running ⟨frames, mem, cfg, dl, fns, decls⟩) with
          | (ev, c1, ⟨ora1, idx1⟩) =>
            match rec ⟨ora1, idx1⟩ c1 with
            | (tr, cFinal, oFinal) =>
              match ev with
              | none => (tr, cFinal, oFinal)
              | some e => (e :: tr, cFinal, oFinal)
      | cTerm => ([], cTerm, o))
    fuel

private theorem runSteps_succ_running (n : Nat) (ora : NondetOracle) (idx : Nat)
    (frames : List CallFrame) (mem : MemoryState) (cfg : SemanticsConfig) (dl : DataLayout)
    (fns : AssocMap FunctionId Definition) (decls : AssocMap FunctionId Declaration) :
    runSteps (n + 1) ⟨ora, idx⟩ (.running ⟨frames, mem, cfg, dl, fns, decls⟩) =
      match execStep ⟨ora, idx⟩ (.running ⟨frames, mem, cfg, dl, fns, decls⟩) with
      | (ev, c1, ⟨ora1, idx1⟩) =>
        match runSteps n ⟨ora1, idx1⟩ c1 with
        | (tr, cFinal, oFinal) =>
          match ev with
          | none => (tr, cFinal, oFinal)
          | some e => (e :: tr, cFinal, oFinal) := rfl

/-- Main multi-step soundness theorem: every fuel-bounded `runSteps` execution from a well-formed
    configuration corresponds to a valid `StarStep` derivation with the exact same `TraceEvent`s. -/
theorem runSteps_sound (fuel : Nat) (o : OracleState) (c : Config)
    (hwf : Config.WellFormed c) :
    StarStep c (runSteps fuel o c).1 (runSteps fuel o c).2.1 := by
  induction fuel generalizing o c with
  | zero => exact StarStep.refl c
  | succ n ih =>
    cases c with
    | running st =>
      cases st with
      | mk frames mem cfg dl fns decls =>
        cases o with
        | mk ora idx =>
          rw [runSteps_succ_running]
          cases hstep : execStep ⟨ora, idx⟩ (.running ⟨frames, mem, cfg, dl, fns, decls⟩) with
          | mk ev rest1 =>
            obtain ⟨c1, o1⟩ := rest1
            cases o1 with
            | mk ora1 idx1 =>
              dsimp only
              have hs := execStep_sound hwf hstep
              have hwf1 := Step.preserves_wf hwf hs
              have hrec := ih ⟨ora1, idx1⟩ c1 hwf1
              cases hrun : runSteps n ⟨ora1, idx1⟩ c1 with
              | mk tr rest2 =>
                obtain ⟨cFinal, oFinal⟩ := rest2
                rw [hrun] at hrec
                dsimp only at hrec ⊢
                cases ev with
                | none => exact StarStep.step hs hrec
                | some e => exact StarStep.step hs hrec
    | halted _ _ | ub _ | staticError _ | resourceError _ =>
      exact StarStep.refl _

/-! ### Module Initialization & Top-Level Runners -/

private def initModulePass1 (dl : DataLayout) (cfg : SemanticsConfig) :
    List TopLevelEntity → MemoryState → AssocMap FunctionId Definition → AssocMap FunctionId Declaration →
    Except ExecError (MemoryState × AssocMap FunctionId Definition × AssocMap FunctionId Declaration)
  | [], mem, fns, decls => .ok (mem, fns, decls)
  | ent :: rest, mem, fns, decls =>
    match ent with
    | .declaration decl =>
      match mem.allocate dl cfg 0 1 decl.name.ToString dl.programAddrSpace .zeroed .func true with
      | .error e => .error e
      | .ok (obj, mem') =>
        let ptr := MemoryState.derivePointer dl obj
        let mem'' := mem'.insertFuncAddr decl.name obj.baseAddr ptr
        initModulePass1 dl cfg rest mem'' fns (decls.insert decl.name decl)
    | .definition defn =>
      match mem.allocate dl cfg 0 1 defn.prototype.name.ToString dl.programAddrSpace .zeroed .func true with
      | .error e => .error e
      | .ok (obj, mem') =>
        let ptr := MemoryState.derivePointer dl obj
        let mem'' := mem'.insertFuncAddr defn.prototype.name obj.baseAddr ptr
        initModulePass1 dl cfg rest mem'' (fns.insert defn.prototype.name defn) decls
    | .global gv =>
      let size := dl.typeAllocSize gv.ty
      let effAlign := gv.align.getD (dl.typeABIAlign gv.ty)
      let initKind := if gv.initializer.isSome then MemInitKind.zeroed else MemInitKind.uninitialized
      match mem.allocate dl cfg size effAlign gv.name.ToString gv.addrSpace initKind .global gv.isConstant with
      | .error e => .error e
      | .ok (obj, mem') =>
        let ptr := MemoryState.derivePointer dl obj
        let mem'' := mem'.insertGlobalAddr gv.name ptr
        initModulePass1 dl cfg rest mem'' fns decls
    | .typeDef _ _ => initModulePass1 dl cfg rest mem fns decls

private def initModulePass2 (dl : DataLayout) (cfg : SemanticsConfig) :
    List TopLevelEntity → MemoryState → OracleState →
    Except ExecError (MemoryState × OracleState)
  | [], mem, o => .ok (mem, o)
  | ent :: rest, mem, o =>
    match ent with
    | .global gv =>
      match gv.initializer with
      | none => initModulePass2 dl cfg rest mem o
      | some initExp =>
        match execExp dl cfg ∅ mem gv.ty initExp o with
        | .error e => .error e
        | .ok (initVal, m1, o1) =>
          let m2 := match m1.globalAddrs.get? gv.name with
            | some ptr =>
              match ptr.prov with
              | .concrete aid =>
                m1.writeObjectBytes aid 0 (valueToBytes dl cfg initVal gv.ty)
              | _ => m1
            | none => m1
          initModulePass2 dl cfg rest m2 o1
    | _ => initModulePass2 dl cfg rest mem o

/-- Initialize all globals, declarations, and function addresses for a `TopLevel` module. -/
def initModuleExec (mod : TopLevel) (cfg : SemanticsConfig := .modern)
    (dl : DataLayout := .default64LE) (oracle : OracleState := default) :
    Except ExecError (MemoryState × AssocMap FunctionId Definition × AssocMap FunctionId Declaration × OracleState) :=
  match mod.resolveTypes with
  | .error msg => .error (.staticError msg)
  | .ok resolvedMod =>
    match initModulePass1 dl cfg resolvedMod.entities {} ∅ ∅ with
    | .error e => .error e
    | .ok (mem1, fns, decls) =>
      match initModulePass2 dl cfg resolvedMod.entities mem1 oracle with
      | .error e => .error e
      | .ok (mem2, o2) => .ok (mem2, fns, decls, o2)

private theorem initModulePass1_wf {dl cfg ents mem fns decls mem' fns' decls'}
    (hwf : MemoryState.WellFormed mem)
    (h : initModulePass1 dl cfg ents mem fns decls = .ok (mem', fns', decls')) :
    MemoryState.WellFormed mem' := by
  induction ents generalizing mem fns decls with
  | nil => unfold initModulePass1 at h; cases h; exact hwf
  | cons ent rest ih =>
    unfold initModulePass1 at h
    cases ent with
    | declaration decl =>
      dsimp only at h
      cases ha : mem.allocate dl cfg 0 1 decl.name.ToString dl.programAddrSpace .zeroed .func true with
      | error e => rw [ha] at h; cases h
      | ok p =>
        rw [ha] at h; obtain ⟨obj, m1⟩ := p
        exact ih (MemoryState.insertFuncAddr_preserves_wf (MemoryState.allocate_preserves_wf hwf ha) _ _ _) h
    | definition defn =>
      dsimp only at h
      cases ha : mem.allocate dl cfg 0 1 defn.prototype.name.ToString dl.programAddrSpace .zeroed .func true with
      | error e => rw [ha] at h; cases h
      | ok p =>
        rw [ha] at h; obtain ⟨obj, m1⟩ := p
        exact ih (MemoryState.insertFuncAddr_preserves_wf (MemoryState.allocate_preserves_wf hwf ha) _ _ _) h
    | global gv =>
      dsimp only at h
      cases ha : mem.allocate dl cfg (dl.typeAllocSize gv.ty) (gv.align.getD (dl.typeABIAlign gv.ty))
          gv.name.ToString gv.addrSpace
          (if gv.initializer.isSome then MemInitKind.zeroed else MemInitKind.uninitialized)
          .global gv.isConstant with
      | error e => rw [ha] at h; cases h
      | ok p =>
        rw [ha] at h; obtain ⟨obj, m1⟩ := p
        exact ih (MemoryState.insertGlobalAddr_preserves_wf (MemoryState.allocate_preserves_wf hwf ha) _ _) h
    | typeDef _ _ => exact ih hwf h

private theorem initModulePass2_wf {dl cfg ents mem o mem' o'}
    (hwf : MemoryState.WellFormed mem)
    (h : initModulePass2 dl cfg ents mem o = .ok (mem', o')) :
    MemoryState.WellFormed mem' := by
  induction ents generalizing mem o with
  | nil => unfold initModulePass2 at h; cases h; exact hwf
  | cons ent rest ih =>
    unfold initModulePass2 at h
    cases ent with
    | global gv =>
      dsimp only at h
      cases hinit : gv.initializer with
      | none => rw [hinit] at h; exact ih hwf h
      | some initExp =>
        rw [hinit] at h; dsimp only at h
        have ihe := execExp_sound dl cfg ∅ mem gv.ty initExp o
        cases he : execExp dl cfg ∅ mem gv.ty initExp o with
        | error e => rw [he] at h; cases h
        | ok p =>
          rw [he] at ihe h; obtain ⟨initVal, m1, o1⟩ := p; dsimp only at ihe h
          have hwf1 := EvalExp.preserves_wf hwf ihe
          have hwf2 : MemoryState.WellFormed (match m1.globalAddrs.get? gv.name with
              | some ptr => match ptr.prov with
                | .concrete aid => m1.writeObjectBytes aid 0 (valueToBytes dl cfg initVal gv.ty)
                | _ => m1
              | none => m1) := by
            cases m1.globalAddrs.get? gv.name with
            | none => exact hwf1
            | some ptr =>
              dsimp only
              cases ptr.prov with
              | concrete aid => exact MemoryState.writeObjectBytes_preserves_wf hwf1 _ _ _
              | _ => exact hwf1
          exact ih hwf2 h
    | _ => dsimp only at h; exact ih hwf h

theorem initModuleExec_wf {mod cfg dl oracle mem fns decls o'}
    (h : initModuleExec mod cfg dl oracle = .ok (mem, fns, decls, o')) :
    MemoryState.WellFormed mem := by
  unfold initModuleExec at h
  cases hres : mod.resolveTypes with
  | error msg => rw [hres] at h; cases h
  | ok rmod =>
    rw [hres] at h; dsimp only at h
    cases h1 : initModulePass1 dl cfg rmod.entities {} ∅ ∅ with
    | error e => rw [h1] at h; cases h
    | ok p1 =>
      rw [h1] at h; obtain ⟨m1, fns1, decls1⟩ := p1; dsimp only at h
      have hwf1 := initModulePass1_wf MemoryState.empty_wf h1
      cases h2 : initModulePass2 dl cfg rmod.entities m1 oracle with
      | error e => rw [h2] at h; cases h
      | ok p2 => rw [h2] at h; obtain ⟨m2, o2⟩ := p2; cases h; exact initModulePass2_wf hwf1 h2

/-- Execute a `Definition`, returning the full `(trace, finalConfig, finalOracle)`. -/
def runDefinitionWithTrace (defn : Definition) (args : List RegisterValue := [])
    (cfg : SemanticsConfig := .modern) (dl : DataLayout := .default64LE)
    (oracle : OracleState := default) (initMem : MemoryState := {}) :
    List TraceEvent × Config × OracleState :=
  let initCfg := initCallConfig cfg dl initMem ∅ ∅ defn args
  runSteps cfg.maxSteps oracle initCfg

/-- Execute a `Definition` and extract its `Except ExecError RegisterValue` result. -/
def runDefinition (defn : Definition) (args : List RegisterValue := [])
    (cfg : SemanticsConfig := .modern) (dl : DataLayout := .default64LE)
    (oracle : OracleState := default) : Except ExecError RegisterValue :=
  (runDefinitionWithTrace defn args cfg dl oracle).2.1.toExcept

/-- Execute a named function inside a `TopLevel` module, returning `(trace, finalConfig, finalOracle)`. -/
def runModuleFunctionWithTrace (mod : TopLevel) (fnName : FunctionId)
    (args : List RegisterValue := []) (cfg : SemanticsConfig := .modern)
    (dl : DataLayout := .default64LE) (oracle : OracleState := default) :
    Except ExecError (List TraceEvent × Config × OracleState) :=
  match initModuleExec mod cfg dl oracle with
  | .error e => .error e
  | .ok (mem, fns, decls, o1) =>
    match fns.get? fnName with
    | none => .error (.staticError s!"Function @{fnName} not found in module")
    | some defn =>
      let initCfg := initCallConfig cfg dl mem fns decls defn args
      .ok (runSteps cfg.maxSteps o1 initCfg)

/-- Execute a named function inside a `TopLevel` module and extract its return value. -/
def runModuleFunction (mod : TopLevel) (fnName : FunctionId)
    (args : List RegisterValue := []) (cfg : SemanticsConfig := .modern)
    (dl : DataLayout := .default64LE) (oracle : OracleState := default) :
    Except ExecError RegisterValue :=
  match runModuleFunctionWithTrace mod fnName args cfg dl oracle with
  | .error e => .error e
  | .ok (_, finalCfg, _) => finalCfg.toExcept

/-- Execute a straight-line `Code` snippet in a fresh frame, returning final registers and memory. -/
def runCode (code : Code) (cfg : SemanticsConfig := .modern)
    (dl : DataLayout := .default64LE) (oracle : OracleState := default) :
    Except ExecError (AssocMap Identifier RegisterValue × MemoryState) :=
  let dummyDef : Definition := {
    prototype := { name := .name "__code__", type := .function .void [] false }
    args := []
    blocks := [{ id := .name "entry", code := code, terminator := (.void 0, .retVoid) }]
  }
  let initFrame : CallFrame := {
    defn := dummyDef
    curBlock := .name "entry"
    remainingCode := code
    terminator := (.void 0, .retVoid)
  }
  let initCfg : Config := .running {
    frames := [initFrame]
    memory := {}
    config := cfg
    dataLayout := dl
  }
  let (_, finalCfg, _) := runSteps code.length oracle initCfg
  match finalCfg with
  | .running st =>
    match st.frames with
    | f :: _ => .ok (f.registers, st.memory)
    | [] => .error (.staticError "Empty frame stack after runCode")
  | .halted _ mem => .ok (∅, mem)
  | .ub msg => .error (.immediateUB msg)
  | .staticError msg => .error (.staticError msg)
  | .resourceError e => .error e

end LeanNanoLlvm.Semantics
