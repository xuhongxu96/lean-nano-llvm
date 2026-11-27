import LeanNanoLlvm.Util.Config
import LeanNanoLlvm.Util.Oracle
import LeanNanoLlvm.Util.AssocMap
import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.DataLayout
import LeanNanoLlvm.AST.Resolve
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
    | .byte w => .ok (RegisterValue.byteOfBitVec (BitVec.ofInt w x), mem, o)
    | _ => .error (.staticError s!"invalid type for int literal: found {ty.print}")
  | .floatBits bits =>
    match ty with
    | .float .float =>
      let flt : IEEEFloat .single :=
        if bits ≥ (1 <<< 32) then
          IEEEFloat.convert .single .RNE (IEEEFloat.ofNatBits (fmt := .double) bits)
        else
          IEEEFloat.ofNatBits bits
      .ok (.float .float (.value flt), mem, o)
    | .float .ppc_fp128 =>
      let hi := bits >>> 64
      let lo := bits &&& ((1 <<< 64) - 1)
      .ok (.float .ppc_fp128 (.value (IEEEFloat.ofNatBits ((lo <<< 64) ||| hi))), mem, o)
    | .float ft => .ok (.float ft (.value (IEEEFloat.ofNatBits bits)), mem, o)
    | _ => .error (.staticError s!"invalid type for float bit literal: found {ty.print}")
  | .floatDec neg m e10 =>
    match ty with
    | .float ft => .ok (.float ft (.value (IEEEFloat.ofDecimal ft.format cfg.roundingMode neg m e10)), mem, o)
    | _ => .error (.staticError s!"invalid type for float decimal literal: found {ty.print}")
  | .floatSpecial neg isInf quiet payload =>
    match ty with
    | .float ft =>
      let flt :=
        if isInf then IEEEFloat.inf ft.format neg
        else if quiet then IEEEFloat.qNaN ft.format neg payload
        else IEEEFloat.sNaN ft.format neg (if payload == 0 then 1 else payload)
      .ok (.float ft (.value flt), mem, o)
    | _ => .error (.staticError s!"invalid type for special float literal: found {ty.print}")
  | .blockAddress fn blk =>
    match ty with
    | .ptr as =>
      match mem.funcAddrs.get? (blockAddrKey fn blk) with
      | some p => .ok (.ptr as (.value p), mem, o)
      | none => .ok (.ptr as (.value (Pointer.null dl as)), mem, o)
    | _ => .error (.staticError s!"`blockaddress` requires pointer type, found {ty.print}")
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
  | .insertElemConst vecTy vecE elemTy elemE idxTy idxE =>
    match execExp dl cfg regs mem vecTy vecE o with
    | .error err => .error err
    | .ok (vecV, m1, o1) =>
      match execExp dl cfg regs m1 elemTy elemE o1 with
      | .error err => .error err
      | .ok (elemV, m2, o2) =>
        match execExp dl cfg regs m2 idxTy idxE o2 with
        | .error err => .error err
        | .ok (idxV, m3, o3) =>
          match evalInsertElementPure vecV elemV idxV with
          | .ok res => .ok (res, m3, o3)
          | .error err => .error err
  | .extractElemConst vecTy vecE idxTy idxE =>
    match execExp dl cfg regs mem vecTy vecE o with
    | .error err => .error err
    | .ok (vecV, m1, o1) =>
      match execExp dl cfg regs m1 idxTy idxE o1 with
      | .error err => .error err
      | .ok (idxV, m2, o2) =>
        match evalExtractElementPure vecV idxV with
        | .ok res => .ok (res, m2, o2)
        | .error err => .error err
  | .shuffleVecConst vecTy e1 e2 mask =>
    match execExp dl cfg regs mem vecTy e1 o with
    | .error err => .error err
    | .ok (v1, m1, o1) =>
      match execExp dl cfg regs m1 vecTy e2 o1 with
      | .error err => .error err
      | .ok (v2, m2, o2) =>
        match evalShuffleVectorPure v1 v2 mask with
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
    | byte w => exact EvalExp.leaf_ok (by simp [evalPureLeafExp?])
    | _ => exact EvalExp.leaf_err (by simp [evalPureLeafExp?])
  | mem, ty, .floatBits bits, o => by
    unfold execExp
    cases ty with
    | float ft =>
      cases ft <;> exact EvalExp.leaf_ok (by simp [evalPureLeafExp?])
    | _ => exact EvalExp.leaf_err (by simp [evalPureLeafExp?])
  | mem, ty, .floatDec neg m e10, o => by
    unfold execExp
    cases ty with
    | float ft => exact EvalExp.leaf_ok (by simp [evalPureLeafExp?])
    | _ => exact EvalExp.leaf_err (by simp [evalPureLeafExp?])
  | mem, ty, .floatSpecial neg isInf quiet payload, o => by
    unfold execExp
    cases ty with
    | float ft => exact EvalExp.leaf_ok (by simp [evalPureLeafExp?])
    | _ => exact EvalExp.leaf_err (by simp [evalPureLeafExp?])
  | mem, ty, .blockAddress fn blk, o => by
    unfold execExp
    cases ty with
    | ptr as =>
      cases hfa : mem.funcAddrs.get? (blockAddrKey fn blk) with
      | some p => exact EvalExp.leaf_ok (by simp [evalPureLeafExp?, blockAddrKey] at hfa ⊢; rw [hfa])
      | none => exact EvalExp.leaf_ok (by simp [evalPureLeafExp?, blockAddrKey] at hfa ⊢; rw [hfa])
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
  | mem, ty, .insertElemConst vecTy vecE elemTy elemE idxTy idxE, o => by
    unfold execExp
    have ih1 := execExp_sound dl cfg regs mem vecTy vecE o
    cases h1 : execExp dl cfg regs mem vecTy vecE o with
    | error err => rw [h1] at ih1; exact EvalExp.insertElemConst_vec_err ih1
    | ok p1 =>
      rw [h1] at ih1; obtain ⟨vecV, m1, o1⟩ := p1; dsimp only at ih1 ⊢
      have ih2 := execExp_sound dl cfg regs m1 elemTy elemE o1
      cases h2 : execExp dl cfg regs m1 elemTy elemE o1 with
      | error err => rw [h2] at ih2; exact EvalExp.insertElemConst_elem_err ih1 ih2
      | ok p2 =>
        rw [h2] at ih2; obtain ⟨elemV, m2, o2⟩ := p2; dsimp only at ih2 ⊢
        have ih3 := execExp_sound dl cfg regs m2 idxTy idxE o2
        cases h3 : execExp dl cfg regs m2 idxTy idxE o2 with
        | error err => rw [h3] at ih3; exact EvalExp.insertElemConst_idx_err ih1 ih2 ih3
        | ok p3 =>
          rw [h3] at ih3; obtain ⟨idxV, m3, o3⟩ := p3; dsimp only at ih3 ⊢
          cases hins : evalInsertElementPure vecV elemV idxV with
          | ok res => exact EvalExp.insertElemConst_ok ih1 ih2 ih3 hins
          | error err => exact EvalExp.insertElemConst_eval_err ih1 ih2 ih3 hins
  | mem, ty, .extractElemConst vecTy vecE idxTy idxE, o => by
    unfold execExp
    have ih1 := execExp_sound dl cfg regs mem vecTy vecE o
    cases h1 : execExp dl cfg regs mem vecTy vecE o with
    | error err => rw [h1] at ih1; exact EvalExp.extractElemConst_vec_err ih1
    | ok p1 =>
      rw [h1] at ih1; obtain ⟨vecV, m1, o1⟩ := p1; dsimp only at ih1 ⊢
      have ih2 := execExp_sound dl cfg regs m1 idxTy idxE o1
      cases h2 : execExp dl cfg regs m1 idxTy idxE o1 with
      | error err => rw [h2] at ih2; exact EvalExp.extractElemConst_idx_err ih1 ih2
      | ok p2 =>
        rw [h2] at ih2; obtain ⟨idxV, m2, o2⟩ := p2; dsimp only at ih2 ⊢
        cases hev : evalExtractElementPure vecV idxV with
        | ok res => exact EvalExp.extractElemConst_ok ih1 ih2 hev
        | error err => exact EvalExp.extractElemConst_eval_err ih1 ih2 hev
  | mem, ty, .shuffleVecConst vecTy e1 e2 mask, o => by
    unfold execExp
    have ih1 := execExp_sound dl cfg regs mem vecTy e1 o
    cases h1 : execExp dl cfg regs mem vecTy e1 o with
    | error err => rw [h1] at ih1; exact EvalExp.shuffleVecConst_e1_err ih1
    | ok p1 =>
      rw [h1] at ih1; obtain ⟨v1, m1, o1⟩ := p1; dsimp only at ih1 ⊢
      have ih2 := execExp_sound dl cfg regs m1 vecTy e2 o1
      cases h2 : execExp dl cfg regs m1 vecTy e2 o1 with
      | error err => rw [h2] at ih2; exact EvalExp.shuffleVecConst_e2_err ih1 ih2
      | ok p2 =>
        rw [h2] at ih2; obtain ⟨v2, m2, o2⟩ := p2; dsimp only at ih2 ⊢
        cases hev : evalShuffleVectorPure v1 v2 mask with
        | ok res => exact EvalExp.shuffleVecConst_ok ih1 ih2 hev
        | error err => exact EvalExp.shuffleVecConst_eval_err ih1 ih2 hev

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
      match applyValueAttrsPure dl m1 ty rawV (byvalDeferredAttrs attrs) with
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
      cases hattr : applyValueAttrsPure dl m1 ty rawV (byvalDeferredAttrs attrs) with
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
    | .phi ty fmf incs md =>
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
            | .ok (v1, o2) =>
              match applyValueAttrsPure dl m1 ty v1 md with
              | .error err => .error err
              | .ok v =>
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
    | phi ty fmf incs md =>
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
              obtain ⟨v1, o2⟩ := p2; dsimp only
              cases hmd : applyValueAttrsPure dl m1 ty v1 md with
              | error err => exact EvalPhis.cons_md_err hfind ih1 ⟨o1, o2, hfmf⟩ hmd
              | ok v =>
                have ih2 := execPhis_sound dl cfg regs predId m1 rest o2
                cases h2 : execPhis dl cfg regs predId m1 rest o2 with
                | error err => rw [h2] at ih2; exact EvalPhis.cons_tail_err hfind ih1 ⟨o1, o2, hfmf⟩ hmd ih2
                | ok p3 =>
                  rw [h2] at ih2; obtain ⟨ups, m2, o3⟩ := p3; dsimp only at ih2 ⊢
                  exact EvalPhis.cons_ok hfind ih1 ⟨o1, o2, hfmf⟩ hmd ih2
    | _ => exact EvalPhis.cons_nonphi_err (by intro _ _ _ _ h; cases h)

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
        | none => .error (.immediateUB "Indirect call through invalid function pointer.")
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
              | none => .error (.immediateUB "Indirect call through invalid function pointer.")
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

def execAssumeBundles (dl : DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap Identifier RegisterValue) (mem : MemoryState) :
    List (String × List (LlvmType × Exp)) → OracleState →
    Except ExecError (MemoryState × OracleState)
  | [], o => .ok (mem, o)
  | (tag, bargs) :: rest, o =>
    if assumeBundleShouldEval tag then
      match execExpList dl cfg regs mem bargs o with
      | .error err => .error err
      | .ok (vals, m1, o1) =>
        match evalAssumeBundlePure dl m1 tag vals with
        | .error err => .error err
        | .ok () => execAssumeBundles dl cfg regs m1 rest o1
    else
      execAssumeBundles dl cfg regs mem rest o

theorem execAssumeBundles_sound (dl : DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap Identifier RegisterValue) :
    ∀ (mem : MemoryState) (bundles : List (String × List (LlvmType × Exp))) (o : OracleState),
      EvalAssumeBundles dl cfg regs mem bundles
        ((execAssumeBundles dl cfg regs mem bundles o).map Prod.fst)
  | mem, [], _ => EvalAssumeBundles.nil
  | mem, (tag, bargs) :: rest, o => by
    unfold execAssumeBundles
    by_cases htag : assumeBundleShouldEval tag = true
    · rw [if_pos htag]
      have ih1 := execExpList_sound dl cfg regs mem bargs o
      cases h1 : execExpList dl cfg regs mem bargs o with
      | error err => rw [h1] at ih1; exact EvalAssumeBundles.cons_eval_err htag ih1
      | ok p1 =>
        rw [h1] at ih1; obtain ⟨vals, m1, o1⟩ := p1; dsimp only at ih1 ⊢
        cases hchk : evalAssumeBundlePure dl m1 tag vals with
        | error err => exact EvalAssumeBundles.cons_check_err htag ih1 hchk
        | ok u =>
          cases u
          have ih2 := execAssumeBundles_sound dl cfg regs m1 rest o1
          cases h2 : execAssumeBundles dl cfg regs m1 rest o1 with
          | error err => rw [h2] at ih2; exact EvalAssumeBundles.cons_tail_err htag ih1 hchk ih2
          | ok p2 => rw [h2] at ih2; obtain ⟨m2, o2⟩ := p2; dsimp only [Except.map] at ih2 ⊢; exact EvalAssumeBundles.cons_ok htag ih1 hchk ih2
    · have htagF : assumeBundleShouldEval tag = false := Bool.eq_false_iff.mpr htag
      rw [if_neg htag]
      exact EvalAssumeBundles.cons_skip htagF (execAssumeBundles_sound dl cfg regs mem rest o)

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
        if frame.defn.prototype.isNoReturn || rd.isNoReturn then
          .ub "Return from a noreturn function/callsite"
        else
          match finishCallerReturn st.dataLayout st.config m2 rd retVal1 with
          | .error err => Config.ofError err
          | .ok retVal2 =>
            let regs' := match rd.retTy, rd.destId with
              | .ret _, .id rid => caller.registers.insert (.local_id rid) retVal2
              | _, _ => caller.registers
            .running (st.withFramesAndMemory (((caller.withRegisters regs').withReturnDest none) :: restCallers) (m2.unhide rd.hidden))

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
        by_cases hnr : (frame.defn.prototype.isNoReturn || rd.isNoReturn) = true
        · rw [if_pos hnr]; exact StepRet.noreturn_ub rfl h1 hrd hnr
        · have hnrF : (frame.defn.prototype.isNoReturn || rd.isNoReturn) = false := Bool.eq_false_iff.mpr hnr
          rw [if_neg hnr]
          cases h2 : finishCallerReturn st.dataLayout st.config (freeAllocaList m1 frame.frameAllocas)
              rd retVal1 with
          | error err => exact StepRet.caller_attr_err rfl h1 hrd hnrF h2
          | ok retVal2 => exact StepRet.call_ok rfl h1 hrd hnrF h2

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
        match evalFloatBinaryExec (frameDenormalCfg st frame) op ty v1 v2 o2 with
        | .ok (res, o3) => (none, finishRegInstr st frame callers rest iid res m2, o3)
        | .error err => (none, Config.ofError err, o2)
  | .icmp ss pred ty e1 e2 =>
    match execExp dl cfg regs st.memory ty e1 o with
    | .error err => (none, Config.ofError err, o)
    | .ok (v1, m1, o1) =>
      match execExp dl cfg regs m1 ty e2 o1 with
      | .error err => (none, Config.ofError err, o1)
      | .ok (v2, m2, o2) =>
        match liftBinaryPure .i1 v1 v2 (evalICmpScalarPure dl ss pred) with
        | .ok res => (none, finishRegInstr st frame callers rest iid res m2, o2)
        | .error err => (none, Config.ofError err, o2)
  | .fcmp fmf pred ty e1 e2 =>
    match execExp dl cfg regs st.memory ty e1 o with
    | .error err => (none, Config.ofError err, o)
    | .ok (v1, m1, o1) =>
      match execExp dl cfg regs m1 ty e2 o1 with
      | .error err => (none, Config.ofError err, o1)
      | .ok (v2, m2, o2) =>
        match evalFCmpExec (frameDenormalCfg st frame) fmf pred v1 v2 o2 with
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
  | .phi _ _ _ _ =>
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
          | .bv _ .poison => .error (.immediateUB "Alloca with poison array size.")
          | .bv _ (.value bv) => .ok (bv.toNat, m1, o1)
          | _ => .error (.staticError "alloca array size must be an integer")
    match cntRes with
    | .error err => (none, Config.ofError err, o)
    | .ok (count, m1, o1) =>
      let totalSize := dl.typeAllocSize allocTy * count
      let effAlign := align?.getD (dl.typePrefAlign allocTy)
      let name := match iid with | .id rid => rid.toString | .void n => s!"alloca.{n}"
      match m1.allocate dl cfg totalSize effAlign name addrSpace (allocaInitKind frame.defn iid) .stack false with
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
      | .ptr _ .poison => (none, .ub "Invalid memory access with a poison pointer.", o1)
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
                (ev, .ub (if hasUndef || rawVal.containsPoison then "The value loaded contains undefined bits."
                          else s!"The value {val.llubiString m1 dl} violates !noundef metadata."), o2)
              else
                (ev, finishRegInstr st frame callers rest iid val (m1.bindWildcard p.prov mo.allocId), o2)
      | _ => (none, .staticError s!"Expected pointer in load, got {ptrVal}", o1)
  | .store valTy valExp ptrTy ptrExp align? isVol =>
    match execExp dl cfg regs st.memory valTy valExp o with
    | .error err => (none, Config.ofError err, o)
    | .ok (val, m1, o1) =>
      match execExp dl cfg regs m1 ptrTy ptrExp o1 with
      | .error err => (none, Config.ofError err, o1)
      | .ok (ptrVal, m2, o2) =>
        match ptrVal with
        | .ptr _ .poison => (none, .ub "Invalid memory access with a poison pointer.", o2)
        | .ptr _ (.value p) =>
          let effAlign := align?.getD (dl.typeABIAlign valTy)
          let storeSize := dl.typeStoreSize valTy
          match m2.verifyMemAccess p storeSize effAlign true with
          | .error err => (none, Config.ofError err, o2)
          | .ok (mo, offset) =>
            let rawBytes := valueToBytes dl cfg val valTy
            let ev := if isVol then some (.volatileStore mo.addrSpace p.addr.toNat rawBytes) else none
            (ev, finishVoidInstr st frame callers rest ((m2.bindWildcard p.prov mo.allocId).writeObjectBytes mo.allocId offset rawBytes), drawPtrTags val o2)
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
  | .bitinsert baseTy base valTy val offTy off =>
    match execExp dl cfg regs st.memory baseTy base o with
    | .error err => (none, Config.ofError err, o)
    | .ok (vBase, m1, o1) =>
      match execExp dl cfg regs m1 valTy val o1 with
      | .error err => (none, Config.ofError err, o1)
      | .ok (vVal, m2, o2) =>
        match execExp dl cfg regs m2 offTy off o2 with
        | .error err => (none, Config.ofError err, o2)
        | .ok (vOff, m3, o3) =>
          match evalBitInsertPure dl baseTy valTy vBase vVal vOff with
          | .ok res => (none, finishRegInstr st frame callers rest iid res m3, drawPtrTags vVal o3)
          | .error err => (none, Config.ofError err, o3)
  | .bitextract retTy srcTy src offTy off =>
    match execExp dl cfg regs st.memory srcTy src o with
    | .error err => (none, Config.ofError err, o)
    | .ok (vSrc, m1, o1) =>
      match execExp dl cfg regs m1 offTy off o1 with
      | .error err => (none, Config.ofError err, o1)
      | .ok (vOff, m2, o2) =>
        match evalBitExtractPure dl retTy vSrc vOff with
        | .ok res => (none, finishRegInstr st frame callers rest iid res m2, o2)
        | .error err => (none, Config.ofError err, o2)
  | .call retTy fmf calleeExp args retAttrs bundles isNoRet site =>
    match execCallArgs dl cfg regs (st.memory.hide (tailHidden site frame)) args o with
    | .error err => (none, Config.ofError err, o)
    | .ok (argVals, m1, o1) =>
      match execCallee dl cfg regs m1 calleeExp o1 with
      | .error err => (none, Config.ofError err, o1)
      | .ok (fid, m2, o2) =>
        let fname := fid.toString
        let allowLib := st.allowLibcallsFor fid
        if allowLib && isAllocLibcall fname then
          match execAllocLibcall dl cfg m2 (heapObjName iid) fname retTy argVals with
          | some (.ok (rawRet, m3)) =>
            match applyRetFMFAndAttrsPure dl m3 retTy fmf retAttrs rawRet with
            | .ok finalRet => (none, finishCallResult st frame callers rest iid retTy finalRet (m3.unhide (tailHidden site frame)), o2)
            | .error err => (none, Config.ofError err, o2)
          | some (.error err) => (none, Config.ofError err, o2)
          | none => (none, .staticError s!"Internal error: alloc libcall {fname}", o2)
        else
          match specLoadOracleCall? st m2 fname argVals with
          | some (oracleDef, ptrVal, revVal, oracleArgs) =>
            if cfg.maxStackDepth != 0 && st.frames.length ≥ cfg.maxStackDepth then
              (none, .resourceError .stackOverflow, o2)
            else
              match mkCallEntryFrameWithMem dl cfg m2 (oracleDef.retType?.getD (.ret (.int 64))) ((args.drop 3).map (fun a => a.2.2)) oracleDef oracleArgs oracleDef.prototype.callingConv (tailHidden site frame) with
              | .error err => (none, Config.ofError err, o2)
              | .ok (calleeFrame, m3) =>
                let caller' := (frame.advance rest frame.registers frame.frameAllocas).withReturnDest
                  (some { destId := iid, retTy := retTy, fmf := fmf, retAttrs := retAttrs, isNoReturn := isNoRet, specLoad? := some (ptrVal, revVal), hidden := tailHidden site frame })
                (none, .running (st.withFramesAndMemory (calleeFrame :: caller' :: callers) m3), o2)
          | none =>
          match evalNonAllocIntrinsicExec? dl (frameDenormalCfg st frame) m2 fname retTy fmf argVals o2 allowLib (args.map (fun a => a.2.2)) with
          | some (.ok (rawRet, m3, o3)) =>
            let effBundles := if fname == "llvm.assume" then bundles else []
            match execAssumeBundles dl cfg regs m3 effBundles o3 with
            | .error err => (none, Config.ofError err, o3)
            | .ok (m4, o4) =>
              match applyRetFMFAndAttrsPure dl m4 retTy fmf retAttrs rawRet with
              | .ok finalRet => (none, finishCallResult st frame callers rest iid retTy finalRet (m4.unhide (tailHidden site frame)), o4)
              | .error err => (none, Config.ofError err, o4)
          | some (.error err) => (none, Config.ofError err, o2)
          | none =>
            match st.functions.get? fid with
            | none => (none, .staticError s!"Call to undefined external function @{fid}", o2)
            | some calleeDef =>
              if cfg.maxStackDepth != 0 && st.frames.length ≥ cfg.maxStackDepth then
                (none, .resourceError .stackOverflow, o2)
              else
                match mkCallEntryFrameWithMem dl cfg m2 retTy (args.map (fun a => a.2.2)) calleeDef argVals site.callingConv (tailHidden site frame) with
                | .error err => (none, Config.ofError err, o2)
                | .ok (calleeFrame, m3) =>
                  let caller' := (frame.advance rest frame.registers frame.frameAllocas).withReturnDest
                    (some { destId := iid, retTy := retTy, fmf := fmf, retAttrs := retAttrs, isNoReturn := isNoRet, hidden := tailHidden site frame })
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
  | .indirectBr addrExp dests =>
    match execExp dl cfg regs st.memory (.ptr dl.programAddrSpace) addrExp o with
    | .error err => (Config.ofError err, o)
    | .ok (addrVal, m1, o1) =>
      match addrVal with
      | .ptr _ .poison => (.ub "Indirect branch on poison", o1)
      | .ptr _ (.value p) =>
        match dests.find? (fun d => m1.addrToFunc.get? p.addr.toNat == some (blockAddrKey frame.defn.prototype.name d)) with
        | some dest => execJump st frame callers m1 dest o1
        | none => (.ub (if (m1.addrToFunc.get? p.addr.toNat).isSome then "Indirect branch on unlisted target BB." else "Indirect branch on invalid target BB."), o1)
      | other => (.staticError s!"Expected pointer in indirectbr, got {other}", o1)
  | .unreachable =>
    (.ub "Unreachable code.", o)

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

private theorem execAllocLibcall_isSome_of_isAlloc {dl cfg mem objName name retTy argVals}
    (h : isAllocLibcall name = true) :
    ∃ res, execAllocLibcall dl cfg mem objName name retTy argVals = some res := by
  unfold isAllocLibcall at h
  simp only [Bool.or_eq_true] at h
  unfold execAllocLibcall
  rcases h with (hm | hc) | hn
  · rw [if_pos hm]; exact ⟨_, rfl⟩
  · by_cases hm : (name == "malloc") = true
    · rw [if_pos hm]; exact ⟨_, rfl⟩
    · rw [if_neg hm, if_pos hc]; exact ⟨_, rfl⟩
  · by_cases hm : (name == "malloc") = true
    · rw [if_pos hm]; exact ⟨_, rfl⟩
    · rw [if_neg hm]
      by_cases hc : (name == "calloc") = true
      · rw [if_pos hc]; exact ⟨_, rfl⟩
      · rw [if_neg hc, if_pos hn]; exact ⟨_, rfl⟩

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
        cases hf : evalFloatBinaryExec (frameDenormalCfg st frame) op ty v1 v2 o2 with
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
        cases hc : liftBinaryPure .i1 v1 v2 (evalICmpScalarPure st.dataLayout ss pred) with
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
        cases hf : evalFCmpExec (frameDenormalCfg st frame) fmf pred v1 v2 o2 with
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
  | phi ty fmf incs md =>
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
            (align?.getD (st.dataLayout.typePrefAlign allocTy))
            (match (generalizing := false) iid with | .id rid => rid.toString | .void n => s!"alloca.{n}")
            addrSpace (allocaInitKind frame.defn iid) .stack false with
          | .ok (obj, mem') =>
            (none, finishRegInstr st frame callers rest iid
              (.ptr addrSpace (.value (MemoryState.derivePointer st.dataLayout obj)))
              mem' (obj.allocId :: frame.frameAllocas), o1)
          | .error err => (none, Config.ofError err, o1)) = (ev, c', o') →
        StepInstr st frame callers iid rest (.alloca allocTy numEl? align? addrSpace) ev c' := by
      intro count m1 o1 hwf1 hcnt ha
      cases halloc : m1.allocate st.dataLayout st.config (st.dataLayout.typeAllocSize allocTy * count)
          (align?.getD (st.dataLayout.typePrefAlign allocTy))
          (match (generalizing := false) iid with | .id rid => rid.toString | .void n => s!"alloca.{n}")
          addrSpace (allocaInitKind frame.defn iid) .stack false with
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
  | bitinsert baseTy base valTy val offTy off =>
    dsimp only at h
    have ih1 := execExp_sound st.dataLayout st.config frame.registers st.memory baseTy base o
    cases h1 : execExp st.dataLayout st.config frame.registers st.memory baseTy base o with
    | error err => rw [h1] at ih1 h; cases h; exact StepInstr.bitinsert_err1 ih1
    | ok p1 =>
      rw [h1] at ih1 h; obtain ⟨vBase, m1, o1⟩ := p1; dsimp only at ih1 h
      have ih2 := execExp_sound st.dataLayout st.config frame.registers m1 valTy val o1
      cases h2 : execExp st.dataLayout st.config frame.registers m1 valTy val o1 with
      | error err => rw [h2] at ih2 h; cases h; exact StepInstr.bitinsert_err2 ih1 ih2
      | ok p2 =>
        rw [h2] at ih2 h; obtain ⟨vVal, m2, o2⟩ := p2; dsimp only at ih2 h
        have ih3 := execExp_sound st.dataLayout st.config frame.registers m2 offTy off o2
        cases h3 : execExp st.dataLayout st.config frame.registers m2 offTy off o2 with
        | error err => rw [h3] at ih3 h; cases h; exact StepInstr.bitinsert_err3 ih1 ih2 ih3
        | ok p3 =>
          rw [h3] at ih3 h; obtain ⟨vOff, m3, o3⟩ := p3; dsimp only at ih3 h
          cases hev : evalBitInsertPure st.dataLayout baseTy valTy vBase vVal vOff with
          | ok res => rw [hev] at h; cases h; exact StepInstr.bitinsert_ok ih1 ih2 ih3 hev
          | error err => rw [hev] at h; cases h; exact StepInstr.bitinsert_eval_err ih1 ih2 ih3 hev
  | bitextract retTy srcTy src offTy off =>
    dsimp only at h
    have ih1 := execExp_sound st.dataLayout st.config frame.registers st.memory srcTy src o
    cases h1 : execExp st.dataLayout st.config frame.registers st.memory srcTy src o with
    | error err => rw [h1] at ih1 h; cases h; exact StepInstr.bitextract_err1 ih1
    | ok p1 =>
      rw [h1] at ih1 h; obtain ⟨vSrc, m1, o1⟩ := p1; dsimp only at ih1 h
      have ih2 := execExp_sound st.dataLayout st.config frame.registers m1 offTy off o1
      cases h2 : execExp st.dataLayout st.config frame.registers m1 offTy off o1 with
      | error err => rw [h2] at ih2 h; cases h; exact StepInstr.bitextract_err2 ih1 ih2
      | ok p2 =>
        rw [h2] at ih2 h; obtain ⟨vOff, m2, o2⟩ := p2; dsimp only at ih2 h
        cases hev : evalBitExtractPure st.dataLayout retTy vSrc vOff with
        | ok res => rw [hev] at h; cases h; exact StepInstr.bitextract_ok ih1 ih2 hev
        | error err => rw [hev] at h; cases h; exact StepInstr.bitextract_eval_err ih1 ih2 hev
  | call retTy fmf calleeExp args retAttrs bundles isNoRet site =>
    dsimp only at h
    have iha := execCallArgs_sound st.dataLayout st.config frame.registers (st.memory.hide (tailHidden site frame)) args o
    cases ha : execCallArgs st.dataLayout st.config frame.registers (st.memory.hide (tailHidden site frame)) args o with
    | error err => rw [ha] at iha h; cases h; exact StepInstr.call_args_err iha
    | ok pa =>
      rw [ha] at iha h; obtain ⟨argVals, m1, o1⟩ := pa; dsimp only at iha h
      have hwf1 := EvalCallArgs.preserves_wf (MemoryState.hide_preserves_wf hwf _) iha
      have ihc := execCallee_sound st.dataLayout st.config frame.registers m1 calleeExp o1
      cases hc : execCallee st.dataLayout st.config frame.registers m1 calleeExp o1 with
      | error err => rw [hc] at ihc h; cases h; exact StepInstr.call_callee_err iha ihc
      | ok pc =>
        rw [hc] at ihc h; obtain ⟨fid, m2, o2⟩ := pc; dsimp only at ihc h
        have hwf2 := EvalCallee.preserves_wf hwf1 ihc
        by_cases halloc : (st.allowLibcallsFor fid && isAllocLibcall fid.toString) = true
        · rw [if_pos halloc] at h
          have hisAlloc : isAllocLibcall fid.toString = true := (Bool.and_eq_true _ _ |>.mp halloc).2
          obtain ⟨res, hres⟩ := execAllocLibcall_isSome_of_isAlloc (dl := st.dataLayout)
            (cfg := st.config) (mem := m2) (objName := heapObjName iid) (retTy := retTy) (argVals := argVals) hisAlloc
          rw [hres] at h
          have hspec := execAllocLibcall_sound hwf2 hres
          cases res with
          | error err => cases h; exact StepInstr.call_alloc_err iha ihc halloc hspec
          | ok pm =>
            obtain ⟨rawRet, m3⟩ := pm; dsimp only at h
            cases hattr : applyRetFMFAndAttrsPure st.dataLayout m3 retTy fmf retAttrs rawRet with
            | error err => rw [hattr] at h; cases h; exact StepInstr.call_alloc_retattr_err iha ihc halloc hspec hattr
            | ok finalRet => rw [hattr] at h; cases h; exact StepInstr.call_alloc_ok iha ihc halloc hspec hattr
        · have hallocF : (st.allowLibcallsFor fid && isAllocLibcall fid.toString) = false := Bool.eq_false_iff.mpr halloc
          rw [if_neg halloc] at h
          cases hspec : specLoadOracleCall? st m2 fid.toString argVals with
          | some pspec =>
            rw [hspec] at h
            obtain ⟨oracleDef, ptrVal, revVal, oracleArgs⟩ := pspec; dsimp only at h
            by_cases hov : (st.config.maxStackDepth != 0 && decide (st.frames.length ≥ st.config.maxStackDepth)) = true
            · rw [if_pos hov] at h; cases h
              simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hov
              exact StepInstr.call_spec_oracle_overflow iha ihc hallocF hspec hov.1 hov.2
            · rw [if_neg hov] at h
              have hdepth : st.config.maxStackDepth == 0 ∨ st.frames.length < st.config.maxStackDepth := by
                by_cases hz : st.config.maxStackDepth = 0
                · exact Or.inl (beq_iff_eq.mpr hz)
                · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_and] at hov
                  exact Or.inr (Nat.lt_of_not_ge (hov hz))
              cases hmk : mkCallEntryFrameWithMem st.dataLayout st.config m2 (oracleDef.retType?.getD (.ret (.int 64))) ((args.drop 3).map (fun a => a.2.2)) oracleDef oracleArgs oracleDef.prototype.callingConv (tailHidden site frame) with
              | error err => rw [hmk] at h; cases h; exact StepInstr.call_spec_oracle_entry_err iha ihc hallocF hspec hdepth hmk
              | ok pm =>
                rw [hmk] at h; obtain ⟨calleeFrame, m3⟩ := pm; cases h
                exact StepInstr.call_spec_oracle_ok iha ihc hallocF hspec hdepth hmk
          | none =>
          rw [hspec] at h; dsimp only at h
          cases hint : evalNonAllocIntrinsicExec? st.dataLayout (frameDenormalCfg st frame) m2 fid.toString retTy fmf argVals o2 (st.allowLibcallsFor fid) (args.map (fun a => a.2.2)) with
          | some r =>
            rw [hint] at h
            cases r with
            | error err => cases h; exact StepInstr.call_intrinsic_err iha ihc hallocF ⟨_, hint⟩
            | ok pm =>
              obtain ⟨rawRet, m3, o3⟩ := pm; dsimp only at h
              let effBundles := if fid.toString == "llvm.assume" then bundles else []
              have ihb := execAssumeBundles_sound st.dataLayout st.config frame.registers m3 effBundles o3
              cases hb : execAssumeBundles st.dataLayout st.config frame.registers m3 effBundles o3 with
              | error err =>
                rw [hb] at ihb h; cases h
                exact StepInstr.call_intrinsic_bundle_err iha ihc hallocF ⟨_, _, hint⟩ ihb
              | ok pb =>
                rw [hb] at ihb h; obtain ⟨m4, o4⟩ := pb; dsimp only at ihb h
                cases hattr : applyRetFMFAndAttrsPure st.dataLayout m4 retTy fmf retAttrs rawRet with
                | error err =>
                  rw [hattr] at h; cases h
                  exact StepInstr.call_intrinsic_retattr_err iha ihc hallocF ⟨_, _, hint⟩ ihb hattr
                | ok finalRet =>
                  rw [hattr] at h; cases h
                  exact StepInstr.call_intrinsic_ok iha ihc hallocF ⟨_, _, hint⟩ ihb hattr
          | none =>
            rw [hint] at h; dsimp only at h
            have hnoneAll : ∀ o0, evalNonAllocIntrinsicExec? st.dataLayout (frameDenormalCfg st frame) m2 fid.toString retTy fmf argVals o0 (st.allowLibcallsFor fid) (args.map (fun a => a.2.2)) = none :=
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
                cases hentry : mkCallEntryFrameWithMem st.dataLayout st.config m2 retTy (args.map (fun a => a.2.2)) calleeDef argVals site.callingConv (tailHidden site frame) with
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
  | indirectBr addrExp dests =>
    dsimp only at h
    have ih := execExp_sound st.dataLayout st.config frame.registers st.memory (.ptr st.dataLayout.programAddrSpace) addrExp o
    cases he : execExp st.dataLayout st.config frame.registers st.memory (.ptr st.dataLayout.programAddrSpace) addrExp o with
    | error err => rw [he] at ih h; cases h; exact StepTerm.indirectBr_err ih
    | ok p1 =>
      rw [he] at ih h; obtain ⟨addrVal, m1, o1⟩ := p1; dsimp only at ih h
      cases addrVal with
      | ptr as pv =>
        cases pv using PoisonOr.casesOn' with
        | poison => cases h; exact StepTerm.indirectBr_poison ih
        | value p =>
          dsimp only at h
          cases hfind : dests.find? (fun d => m1.addrToFunc.get? p.addr.toNat == some (blockAddrKey frame.defn.prototype.name d)) with
          | none =>
            rw [hfind] at h; cases h
            refine StepTerm.indirectBr_invalid ih ?_
            intro d hd heq
            have := List.find?_eq_none.mp hfind d hd
            simp [heq] at this
          | some dest =>
            rw [hfind] at h
            have hmem := List.mem_of_find?_eq_some hfind
            have hpred := List.find?_some hfind
            simp only [beq_iff_eq] at hpred
            exact StepTerm.indirectBr_ok ih hpred hmem (execJump_sound h)
      | _ => cases h; exact StepTerm.indirectBr_nonptr ih (by intro _ _ heq; cases heq)
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
        | ⟨ora, idx, nid, tg⟩ =>
          match execStep ⟨ora, idx, nid, tg⟩ (.running ⟨frames, mem, cfg, dl, fns, decls⟩) with
          | (ev, c1, ⟨ora1, idx1, nid1, tg1⟩) =>
            match rec ⟨ora1, idx1, nid1, tg1⟩ c1 with
            | (tr, cFinal, oFinal) =>
              match ev with
              | none => (tr, cFinal, oFinal)
              | some e => (e :: tr, cFinal, oFinal)
      | cTerm => ([], cTerm, o))
    fuel

private theorem runSteps_succ_running (n : Nat) (ora : NondetOracle) (idx nid : Nat) (tg : List (Nat × Nat))
    (frames : List CallFrame) (mem : MemoryState) (cfg : SemanticsConfig) (dl : DataLayout)
    (fns : AssocMap FunctionId Definition) (decls : AssocMap FunctionId Declaration) :
    runSteps (n + 1) ⟨ora, idx, nid, tg⟩ (.running ⟨frames, mem, cfg, dl, fns, decls⟩) =
      match execStep ⟨ora, idx, nid, tg⟩ (.running ⟨frames, mem, cfg, dl, fns, decls⟩) with
      | (ev, c1, ⟨ora1, idx1, nid1, tg1⟩) =>
        match runSteps n ⟨ora1, idx1, nid1, tg1⟩ c1 with
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
        | mk ora idx nid tg =>
          rw [runSteps_succ_running]
          cases hstep : execStep ⟨ora, idx, nid, tg⟩ (.running ⟨frames, mem, cfg, dl, fns, decls⟩) with
          | mk ev rest1 =>
            obtain ⟨c1, o1⟩ := rest1
            cases o1 with
            | mk ora1 idx1 nid1 tg1 =>
              dsimp only
              have hs := execStep_sound hwf hstep
              have hwf1 := Step.preserves_wf hwf hs
              have hrec := ih ⟨ora1, idx1, nid1, tg1⟩ c1 hwf1
              cases hrun : runSteps n ⟨ora1, idx1, nid1, tg1⟩ c1 with
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

mutual
private def collectAddrTakenExp : Exp → List GlobalId × List GlobalId
  | .identifier (.global_id gid) => ([gid], [])
  | .blockAddress fn blk => ([], [blockAddrKey fn blk])
  | .array es | .struct _ es | .vector es => collectAddrTakenTypedList es
  | .splat (_, e) => collectAddrTakenExp e
  | .gepConst _ _ (_, p) idxs =>
    let (f1, b1) := collectAddrTakenExp p
    let (f2, b2) := collectAddrTakenTypedList idxs
    (f1 ++ f2, b1 ++ b2)
  | .convConst _ _ e _ => collectAddrTakenExp e
  | .binConst _ _ e1 e2 =>
    let (f1, b1) := collectAddrTakenExp e1
    let (f2, b2) := collectAddrTakenExp e2
    (f1 ++ f2, b1 ++ b2)
  | .insertElemConst _ v _ e _ idx =>
    let (f1, b1) := collectAddrTakenExp v
    let (f2, b2) := collectAddrTakenExp e
    let (f3, b3) := collectAddrTakenExp idx
    (f1 ++ f2 ++ f3, b1 ++ b2 ++ b3)
  | .extractElemConst _ v _ idx =>
    let (f1, b1) := collectAddrTakenExp v
    let (f2, b2) := collectAddrTakenExp idx
    (f1 ++ f2, b1 ++ b2)
  | .shuffleVecConst _ v1 v2 _ =>
    let (f1, b1) := collectAddrTakenExp v1
    let (f2, b2) := collectAddrTakenExp v2
    (f1 ++ f2, b1 ++ b2)
  | _ => ([], [])

private def collectAddrTakenTypedList : List (LlvmType × Exp) → List GlobalId × List GlobalId
  | [] => ([], [])
  | (_, e) :: rest =>
    let (f1, b1) := collectAddrTakenExp e
    let (f2, b2) := collectAddrTakenTypedList rest
    (f1 ++ f2, b1 ++ b2)
end

private def collectAddrTakenInstr : Instruction → List GlobalId × List GlobalId
  | .intBinaryOp _ _ e1 e2 | .floatBinaryOp _ _ e1 e2 | .icmp _ _ _ e1 e2 | .fcmp _ _ _ e1 e2 =>
    let (f1, b1) := collectAddrTakenExp e1; let (f2, b2) := collectAddrTakenExp e2; (f1 ++ f2, b1 ++ b2)
  | .floatUnaryOp _ _ e | .conversionOp _ _ e _ | .load _ _ e _ _ _ _ | .extractvalue _ e _ | .freeze (_, e) =>
    collectAddrTakenExp e
  | .select _ _ c _ tv fv =>
    let (f1, b1) := collectAddrTakenExp c; let (f2, b2) := collectAddrTakenExp tv; let (f3, b3) := collectAddrTakenExp fv
    (f1 ++ f2 ++ f3, b1 ++ b2 ++ b3)
  | .phi _ _ inc _ =>
    inc.foldl (init := ([], [])) fun (fs, bs) (e, _) =>
      let (f1, b1) := collectAddrTakenExp e; (fs ++ f1, bs ++ b1)
  | .alloca _ (some (_, e)) _ _ => collectAddrTakenExp e
  | .alloca _ none _ _ => ([], [])
  | .store _ v _ p _ _ | .insertvalue _ v _ p _ | .extractelement _ v _ p | .shufflevector _ v p _ | .bitextract _ _ v _ p =>
    let (f1, b1) := collectAddrTakenExp v; let (f2, b2) := collectAddrTakenExp p; (f1 ++ f2, b1 ++ b2)
  | .getelementptr _ _ _ p idxs =>
    let (f1, b1) := collectAddrTakenExp p; let (f2, b2) := collectAddrTakenTypedList idxs; (f1 ++ f2, b1 ++ b2)
  | .insertelement _ v _ e _ idx | .bitinsert _ v _ e _ idx =>
    let (f1, b1) := collectAddrTakenExp v; let (f2, b2) := collectAddrTakenExp e; let (f3, b3) := collectAddrTakenExp idx
    (f1 ++ f2 ++ f3, b1 ++ b2 ++ b3)
  | .call _ _ callee args _ bundles _ _ =>
    -- Direct call `@f(...)` does NOT take the address of `@f`; only non-direct callees and arguments do.
    let (fc, bc) := match callee with
      | .identifier (.global_id _) => ([], [])
      | other => collectAddrTakenExp other
    let (fa, ba) := args.foldl (init := (fc, bc)) fun (fs, bs) (_, e, _) =>
      let (f1, b1) := collectAddrTakenExp e; (fs ++ f1, bs ++ b1)
    bundles.foldl (init := (fa, ba)) fun (fs, bs) (_, bes) =>
      let (f1, b1) := collectAddrTakenTypedList bes; (fs ++ f1, bs ++ b1)

private def collectAddrTakenTerm : Terminator → List GlobalId × List GlobalId
  | .ret (_, e) | .condBr e _ _ | .switch _ e _ _ | .indirectBr e _ => collectAddrTakenExp e
  | _ => ([], [])

private def collectAddrTaken (ents : List TopLevelEntity) : List GlobalId × List GlobalId :=
  ents.foldl (init := ([], [])) fun (fs, bs) ent =>
    match ent with
    | .global gv =>
      match gv.initializer with
      | some e => let (f1, b1) := collectAddrTakenExp e; (fs ++ f1, bs ++ b1)
      | none => (fs, bs)
    | .definition defn =>
      defn.blocks.foldl (init := (fs, bs)) fun (fs1, bs1) blk =>
        let (fs2, bs2) := blk.code.foldl (init := (fs1, bs1)) fun (fa, ba) (_, ins) =>
          let (f1, b1) := collectAddrTakenInstr ins; (fa ++ f1, ba ++ b1)
        let (ft, bt) := collectAddrTakenTerm blk.terminator.2
        (fs2 ++ ft, bs2 ++ bt)
    | _ => (fs, bs)

private def registerBlockAddrs (dl : DataLayout) (cfg : SemanticsConfig)
    (takenBlks : List GlobalId) (fnName : FunctionId) :
    List Block → MemoryState → Except ExecError MemoryState
  | [], mem => .ok mem
  | blk :: rest, mem =>
    let key := blockAddrKey fnName blk.id
    if takenBlks.contains key then
      match mem.allocate dl cfg 0 1 key.toString dl.programAddrSpace .zeroed .func true with
      | .error e => .error e
      | .ok (obj, mem') =>
        let ptr := MemoryState.derivePointer dl obj
        registerBlockAddrs dl cfg takenBlks fnName rest (mem'.insertFuncAddr key obj.baseAddr ptr)
    else
      registerBlockAddrs dl cfg takenBlks fnName rest mem

private theorem registerBlockAddrs_wf {dl cfg takenBlks fnName blks mem mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : registerBlockAddrs dl cfg takenBlks fnName blks mem = .ok mem') :
    MemoryState.WellFormed mem' := by
  induction blks generalizing mem with
  | nil => unfold registerBlockAddrs at h; cases h; exact hwf
  | cons blk rest ih =>
    unfold registerBlockAddrs at h
    dsimp only at h
    split at h
    · cases ha : mem.allocate dl cfg 0 1 (blockAddrKey fnName blk.id).toString dl.programAddrSpace .zeroed .func true with
      | error e => rw [ha] at h; cases h
      | ok p =>
        rw [ha] at h; obtain ⟨obj, m1⟩ := p
        exact ih (MemoryState.insertFuncAddr_preserves_wf (MemoryState.allocate_preserves_wf hwf ha) _ _ _) h
    · exact ih hwf h

/-- Module-initialization order of `llubi::Context::initGlobalValues`: function (and block)
address objects for all functions first, then global variables. -/
def functionsFirst (ents : List TopLevelEntity) : List TopLevelEntity :=
  ents.filter (fun | .global _ => false | _ => true) ++ ents.filter (fun | .global _ => true | _ => false)

private def initModulePass1 (dl : DataLayout) (cfg : SemanticsConfig)
    (takenFns takenBlks : List GlobalId) :
    List TopLevelEntity → MemoryState → AssocMap FunctionId Definition → AssocMap FunctionId Declaration →
    Except ExecError (MemoryState × AssocMap FunctionId Definition × AssocMap FunctionId Declaration)
  | [], mem, fns, decls => .ok (mem, fns, decls)
  | ent :: rest, mem, fns, decls =>
    match ent with
    | .declaration decl =>
      if takenFns.contains decl.name then
        match mem.allocate dl cfg 0 1 decl.name.toString dl.programAddrSpace .zeroed .func true with
        | .error e => .error e
        | .ok (obj, mem') =>
          let ptr := MemoryState.derivePointer dl obj
          let mem'' := mem'.insertFuncAddr decl.name obj.baseAddr ptr
          initModulePass1 dl cfg takenFns takenBlks rest mem'' fns (decls.insert decl.name decl)
      else
        initModulePass1 dl cfg takenFns takenBlks rest mem fns (decls.insert decl.name decl)
    | .definition defn =>
      let afterFn : Except ExecError MemoryState :=
        if takenFns.contains defn.prototype.name then
          match mem.allocate dl cfg 0 1 defn.prototype.name.toString dl.programAddrSpace .zeroed .func true with
          | .error e => .error e
          | .ok (obj, mem') =>
            let ptr := MemoryState.derivePointer dl obj
            .ok (mem'.insertFuncAddr defn.prototype.name obj.baseAddr ptr)
        else .ok mem
      match afterFn with
      | .error e => .error e
      | .ok mem'' =>
        match registerBlockAddrs dl cfg takenBlks defn.prototype.name defn.blocks mem'' with
        | .error e => .error e
        | .ok mem''' => initModulePass1 dl cfg takenFns takenBlks rest mem''' (fns.insert defn.prototype.name defn) decls
    | .global gv =>
      let size := dl.typeAllocSize gv.ty
      let effAlign := dl.globalAlign gv.ty gv.align gv.initializer.isSome
      let initKind := if gv.initializer.isSome then MemInitKind.zeroed else MemInitKind.uninitialized
      match mem.allocate dl cfg size effAlign gv.name.toString gv.addrSpace initKind .global gv.isConstant with
      | .error e => .error e
      | .ok (obj, mem') =>
        let ptr := MemoryState.derivePointer dl obj
        let mem'' := mem'.insertGlobalAddr gv.name ptr
        initModulePass1 dl cfg takenFns takenBlks rest mem'' fns decls
    | .typeDef _ _ => initModulePass1 dl cfg takenFns takenBlks rest mem fns decls

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
          initModulePass2 dl cfg rest m2 (drawPtrTags initVal o1)
    | _ => initModulePass2 dl cfg rest mem o

/-- Initialize all globals, declarations, and function addresses for a `TopLevel` module. -/
def initModuleExec (mod : TopLevel) (cfg : SemanticsConfig := .modern)
    (dl : DataLayout := .default64LE) (oracle : OracleState := default) :
    Except ExecError (MemoryState × AssocMap FunctionId Definition × AssocMap FunctionId Declaration × OracleState) :=
  match mod.resolveTypes with
  | .error msg => .error (.staticError msg)
  | .ok resolvedMod =>
    let (takenFns, takenBlks) := collectAddrTaken resolvedMod.entities
    match initModulePass1 dl cfg takenFns takenBlks (functionsFirst resolvedMod.entities) {} ∅ ∅ with
    | .error e => .error e
    | .ok (mem1, fns, decls) =>
      match initModulePass2 dl cfg resolvedMod.entities mem1 oracle with
      | .error e => .error e
      | .ok (mem2, o2) => .ok (mem2, fns, decls, o2)

private theorem initModulePass1_wf {dl cfg takenFns takenBlks ents mem fns decls mem' fns' decls'}
    (hwf : MemoryState.WellFormed mem)
    (h : initModulePass1 dl cfg takenFns takenBlks ents mem fns decls = .ok (mem', fns', decls')) :
    MemoryState.WellFormed mem' := by
  induction ents generalizing mem fns decls with
  | nil => unfold initModulePass1 at h; cases h; exact hwf
  | cons ent rest ih =>
    unfold initModulePass1 at h
    cases ent with
    | declaration decl =>
      dsimp only at h
      split at h
      · cases ha : mem.allocate dl cfg 0 1 decl.name.toString dl.programAddrSpace .zeroed .func true with
        | error e => rw [ha] at h; cases h
        | ok p =>
          rw [ha] at h; obtain ⟨obj, m1⟩ := p
          exact ih (MemoryState.insertFuncAddr_preserves_wf (MemoryState.allocate_preserves_wf hwf ha) _ _ _) h
      · exact ih hwf h
    | definition defn =>
      dsimp only at h
      have hwfAfter : ∀ m2, ((if takenFns.contains defn.prototype.name then
            match mem.allocate dl cfg 0 1 defn.prototype.name.toString dl.programAddrSpace .zeroed .func true with
            | .error e => .error e
            | .ok (obj, mem') => .ok (mem'.insertFuncAddr defn.prototype.name obj.baseAddr (MemoryState.derivePointer dl obj))
          else .ok mem) : Except ExecError MemoryState) = .ok m2 → MemoryState.WellFormed m2 := by
        intro m2 hm2
        split at hm2
        · cases ha : mem.allocate dl cfg 0 1 defn.prototype.name.toString dl.programAddrSpace .zeroed .func true with
          | error e => rw [ha] at hm2; cases hm2
          | ok p =>
            rw [ha] at hm2; obtain ⟨obj, m1⟩ := p; cases hm2
            exact MemoryState.insertFuncAddr_preserves_wf (MemoryState.allocate_preserves_wf hwf ha) _ _ _
        · cases hm2; exact hwf
      split at h
      · cases h
      · rename_i m2 hm2
        have hwf1 := hwfAfter m2 hm2
        cases hb : registerBlockAddrs dl cfg takenBlks defn.prototype.name defn.blocks m2 with
        | error e => rw [hb] at h; cases h
        | ok m3 => rw [hb] at h; exact ih (registerBlockAddrs_wf hwf1 hb) h
    | global gv =>
      dsimp only at h
      cases ha : mem.allocate dl cfg (dl.typeAllocSize gv.ty) (dl.globalAlign gv.ty gv.align gv.initializer.isSome)
          gv.name.toString gv.addrSpace
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
    cases h1 : initModulePass1 dl cfg (collectAddrTaken rmod.entities).1 (collectAddrTaken rmod.entities).2 (functionsFirst rmod.entities) {} ∅ ∅ with
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
