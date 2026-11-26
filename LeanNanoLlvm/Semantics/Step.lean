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

namespace LeanNanoLlvm.Semantics

open AST

/-! ### Shared Pure & Oracle-Backed Instruction Helpers -/

/-- Synthetic key in `funcAddrs` / `addrToFunc` for `blockaddress(@fn, %blk)`. -/
@[simp]
def blockAddrKey (fn : FunctionId) (blk : BlockId) : RawId :=
  .name s!"__bb__{fn.ToString}__{blk.ToString}"

/--
Deterministic pure leaf expression evaluator (shared by `Step.EvalExp` and `Exec.execExp`).
Returns `none` only for compound expressions and `.undef`.
-/
@[simp, simp_step]
def evalPureLeafExp? (dl : DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap Identifier RegisterValue) (mem : MemoryState)
    (ty : LlvmType) : Exp → Option (Except ExecError RegisterValue)
  | .identifier (.local_id id) =>
    some <| match regs.get? (.local_id id) with
      | some v => .ok v
      | none => .error (.staticError s!"unknown local id [%{id}]")
  | .identifier (.global_id id) =>
    some <|
      let as := match ty with | .ptr a => a | _ => 0
      match mem.globalAddrs.get? id with
      | some p => .ok (.ptr as (.value p))
      | none =>
        match mem.funcAddrs.get? id with
        | some p => .ok (.ptr as (.value p))
        | none => .error (.staticError s!"unknown global id [@{id}]")
  | .bool b =>
    some <| match ty with
      | .int 1 => .ok (.bv 1 (.value (BitVec.ofBool b)))
      | _ => .error (.staticError s!"invalid type for bool literal: expected i1, found {ty.print}")
  | .int x =>
    some <| match ty with
      | .int w => .ok (.bv w (.value (BitVec.ofInt w x)))
      | .byte w => .ok (RegisterValue.byteOfBitVec (BitVec.ofInt w x))
      | _ => .error (.staticError s!"invalid type for int literal: found {ty.print}")
  | .floatBits bits =>
    some <| match ty with
      | .float ft => .ok (.float ft (.value (IEEEFloat.ofNatBits bits)))
      | _ => .error (.staticError s!"invalid type for float bit literal: found {ty.print}")
  | .floatDec neg m e =>
    some <| match ty with
      | .float ft => .ok (.float ft (.value (IEEEFloat.ofDecimal ft.format cfg.roundingMode neg m e)))
      | _ => .error (.staticError s!"invalid type for float decimal literal: found {ty.print}")
  | .floatSpecial neg isInf quiet payload =>
    some <| match ty with
      | .float ft =>
        let flt :=
          if isInf then IEEEFloat.inf ft.format neg
          else if quiet then IEEEFloat.qNaN ft.format neg payload
          else IEEEFloat.sNaN ft.format neg (if payload == 0 then 1 else payload)
        .ok (.float ft (.value flt))
      | _ => .error (.staticError s!"invalid type for special float literal: found {ty.print}")
  | .blockAddress fn blk =>
    some <| match ty with
      | .ptr as =>
        match mem.funcAddrs.get? (.name s!"__bb__{fn.ToString}__{blk.ToString}") with
        | some p => .ok (.ptr as (.value p))
        | none => .ok (.ptr as (.value (Pointer.null dl as)))
      | _ => .error (.staticError s!"`blockaddress` requires pointer type, found {ty.print}")
  | .null =>
    some <| match ty with
      | .ptr as => .ok (.ptr as (.value (Pointer.null dl as)))
      | _ => .error (.staticError s!"`null` requires pointer type, found {ty.print}")
  | .zeroinitializer =>
    some (.ok (RegisterValue.nullOf dl ty))
  | .poison =>
    some (.ok (RegisterValue.poisonOf ty))
  | _ => none

/-- Apply input FastMathFlags (`nnan`/`ninf`/`nsz`) to a float scalar or vector (for `select` and `phi`). -/
def applyInputFMFExec (fmf : FastMathFlags) (ty : LlvmType) (val : RegisterValue)
    (o : OracleState) : Except ExecError (RegisterValue × OracleState) :=
  if !fmf.any then .ok (val, o)
  else
    let goElem (v : RegisterValue) (o0 : OracleState) : Except ExecError (RegisterValue × OracleState) :=
      match v with
      | .float ft (.value flt) =>
        let (flipZ, o1) := o0.nextBool
        .ok (.float ft (handleFMF fmf true flipZ flt), o1)
      | other => .ok (other, o0)
    match val with
    | .vector _ elems =>
      let rec goFMFList : List RegisterValue → OracleState → Except ExecError (List RegisterValue × OracleState)
        | [], o0 => .ok ([], o0)
        | e :: es, o0 =>
          match goElem e o0 with
          | .error err => .error err
          | .ok (r, o1) =>
            match goFMFList es o1 with
            | .error err => .error err
            | .ok (rs, o2) => .ok (r :: rs, o2)
      match goFMFList elems o with
      | .ok (rs, o') => .ok (.vector ty.scalarType rs, o')
      | .error err => .error err
    | other => goElem other o

@[simp, simp_step]
theorem applyInputFMFExec_none (ty : LlvmType) (val : RegisterValue) (o : OracleState) :
    applyInputFMFExec {} ty val o = .ok (val, o) := rfl

/-- Finish a value-producing instruction by writing to its local register ID. -/
@[simp, simp_step]
def finishRegInstr (st : MachineState) (frame : CallFrame) (callers : List CallFrame)
    (restCode : Code) (instrId : InstructionId) (val : RegisterValue) (mem' : MemoryState)
    (allocas' : List AllocId := frame.frameAllocas) : Config :=
  match instrId with
  | .id rid =>
    .running (st.withFramesAndMemory
      (frame.advance restCode (frame.registers.insert (.local_id rid) val) allocas' :: callers) mem')
  | .void _ => .staticError "Value-producing instruction requires a local register id"

/-- Finish a void instruction (`store`) without writing a register. -/
@[simp, simp_step]
def finishVoidInstr (st : MachineState) (frame : CallFrame) (callers : List CallFrame)
    (restCode : Code) (mem' : MemoryState) : Config :=
  .running (st.withFramesAndMemory
    (frame.advance restCode frame.registers frame.frameAllocas :: callers) mem')

/-- Finish a `call` result (LLVM permits discarding non-void call results when `instrId` is `.void`). -/
@[simp, simp_step]
def finishCallResult (st : MachineState) (frame : CallFrame) (callers : List CallFrame)
    (restCode : Code) (instrId : InstructionId) (retTy : LlvmRetType)
    (val : RegisterValue) (mem' : MemoryState) : Config :=
  let regs' := match retTy, instrId with
    | .ret _, .id rid => frame.registers.insert (.local_id rid) val
    | _, _ => frame.registers
  .running (st.withFramesAndMemory
    (frame.advance restCode regs' frame.frameAllocas :: callers) mem')

/-- Commit a list of parallel phi register updates simultaneously. -/
@[simp_step]
def commitPhiUpdates (regs : AssocMap Identifier RegisterValue) :
    List (RawId × RegisterValue) → AssocMap Identifier RegisterValue
  | [] => regs
  | (rid, val) :: rest => commitPhiUpdates (regs.insert (.local_id rid) val) rest

end LeanNanoLlvm.Semantics

namespace LeanNanoLlvm.AST

mutual
/-- Returns `true` if `ty` is or recursively contains a `.function` type (disallowed in `undef`). -/
@[simp]
def LlvmType.hasFunction : LlvmType → Bool
  | .function .. | .named _ => true
  | .vector _ elem => elem.hasFunction
  | .array _ elem => elem.hasFunction
  | .struct _ fields => LlvmType.hasFunctionList fields
  | _ => false

@[simp]
def LlvmType.hasFunctionList : List LlvmType → Bool
  | [] => false
  | t :: ts => t.hasFunction || LlvmType.hasFunctionList ts
end

end LeanNanoLlvm.AST

namespace LeanNanoLlvm.Semantics
open AST

/-! ### Relational Expression, Argument, and Phi Evaluation (No Oracle) -/

mutual
/--
Primary relational expression evaluator (no `OracleState`).
- Pure leaves delegate to `evalPureLeafExp?`.
- `.undef` uses relational `UndefValRel` (when `cfg.allowUndef = true`).
- `.convConst` quantifies existentially over oracle draws (and exposes provenance on `ptrtoint`).
-/
inductive EvalExp (dl : DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap Identifier RegisterValue) :
    MemoryState → LlvmType → Exp → Except ExecError (RegisterValue × MemoryState) → Prop where
  | leaf_ok {mem ty e v} :
      evalPureLeafExp? dl cfg regs mem ty e = some (.ok v) →
      EvalExp dl cfg regs mem ty e (.ok (v, mem))
  | leaf_err {mem ty e err} :
      evalPureLeafExp? dl cfg regs mem ty e = some (.error err) →
      EvalExp dl cfg regs mem ty e (.error err)
  | undef_ok {mem ty v} :
      cfg.allowUndef = true →
      UndefValRel dl cfg ty v →
      EvalExp dl cfg regs mem ty .undef (.ok (v, mem))
  | undef_err {mem ty msg} :
      (cfg.undefMode = .disabled ∨ ty.hasFunction = true) →
      EvalExp dl cfg regs mem ty .undef (.error (.staticError msg))
  | array_ok {mem n elemTy elems vals mem'} :
      elems.length = n →
      EvalExpList dl cfg regs mem elems (.ok (vals, mem')) →
      EvalExp dl cfg regs mem (.array n elemTy) (.array elems) (.ok (.array elemTy vals, mem'))
  | array_err {mem n elemTy elems err} :
      elems.length = n →
      EvalExpList dl cfg regs mem elems (.error err) →
      EvalExp dl cfg regs mem (.array n elemTy) (.array elems) (.error err)
  | array_len_err {mem n elemTy elems msg} :
      elems.length ≠ n →
      EvalExp dl cfg regs mem (.array n elemTy) (.array elems) (.error (.staticError msg))
  | array_ty_err {mem ty elems msg} :
      ty.asArray? = none →
      EvalExp dl cfg regs mem ty (.array elems) (.error (.staticError msg))
  | struct_ok {mem p fTys packed fields vals mem'} :
      fields.length = fTys.length →
      EvalExpList dl cfg regs mem fields (.ok (vals, mem')) →
      EvalExp dl cfg regs mem (.struct p fTys) (.struct packed fields) (.ok (.struct packed fTys vals, mem'))
  | struct_err {mem p fTys packed fields err} :
      fields.length = fTys.length →
      EvalExpList dl cfg regs mem fields (.error err) →
      EvalExp dl cfg regs mem (.struct p fTys) (.struct packed fields) (.error err)
  | struct_len_err {mem p fTys packed fields msg} :
      fields.length ≠ fTys.length →
      EvalExp dl cfg regs mem (.struct p fTys) (.struct packed fields) (.error (.staticError msg))
  | struct_ty_err {mem ty packed fields msg} :
      ty.asStruct? = none →
      EvalExp dl cfg regs mem ty (.struct packed fields) (.error (.staticError msg))
  | vector_ok {mem n elemTy elems vals mem'} :
      elems.length = n →
      EvalExpList dl cfg regs mem elems (.ok (vals, mem')) →
      EvalExp dl cfg regs mem (.vector n elemTy) (.vector elems) (.ok (.vector elemTy vals, mem'))
  | vector_err {mem n elemTy elems err} :
      elems.length = n →
      EvalExpList dl cfg regs mem elems (.error err) →
      EvalExp dl cfg regs mem (.vector n elemTy) (.vector elems) (.error err)
  | vector_len_err {mem n elemTy elems msg} :
      elems.length ≠ n →
      EvalExp dl cfg regs mem (.vector n elemTy) (.vector elems) (.error (.staticError msg))
  | vector_ty_err {mem ty elems msg} :
      ty.asVector? = none →
      EvalExp dl cfg regs mem ty (.vector elems) (.error (.staticError msg))
  | splat_ok {mem n elemTy eTy e sv mem'} :
      EvalExp dl cfg regs mem eTy e (.ok (sv, mem')) →
      EvalExp dl cfg regs mem (.vector n elemTy) (.splat (eTy, e)) (.ok (.vector elemTy (List.replicate n sv), mem'))
  | splat_err {mem n elemTy eTy e err} :
      EvalExp dl cfg regs mem eTy e (.error err) →
      EvalExp dl cfg regs mem (.vector n elemTy) (.splat (eTy, e)) (.error err)
  | splat_ty_err {mem ty p msg} :
      ty.asVector? = none →
      EvalExp dl cfg regs mem ty (.splat p) (.error (.staticError msg))
  | gepConst_ok {mem ty flags baseTy pTy pExp idxs baseVal m1 idxVals m2 res} :
      EvalExp dl cfg regs mem pTy pExp (.ok (baseVal, m1)) →
      EvalExpList dl cfg regs m1 idxs (.ok (idxVals, m2)) →
      evalGEPValuesPure dl m2 flags baseTy pTy baseVal idxVals = .ok res →
      EvalExp dl cfg regs mem ty (.gepConst flags baseTy (pTy, pExp) idxs) (.ok (res, m2))
  | gepConst_base_err {mem ty flags baseTy pTy pExp idxs err} :
      EvalExp dl cfg regs mem pTy pExp (.error err) →
      EvalExp dl cfg regs mem ty (.gepConst flags baseTy (pTy, pExp) idxs) (.error err)
  | gepConst_idx_err {mem ty flags baseTy pTy pExp idxs baseVal m1 err} :
      EvalExp dl cfg regs mem pTy pExp (.ok (baseVal, m1)) →
      EvalExpList dl cfg regs m1 idxs (.error err) →
      EvalExp dl cfg regs mem ty (.gepConst flags baseTy (pTy, pExp) idxs) (.error err)
  | gepConst_eval_err {mem ty flags baseTy pTy pExp idxs baseVal m1 idxVals m2 err} :
      EvalExp dl cfg regs mem pTy pExp (.ok (baseVal, m1)) →
      EvalExpList dl cfg regs m1 idxs (.ok (idxVals, m2)) →
      evalGEPValuesPure dl m2 flags baseTy pTy baseVal idxVals = .error err →
      EvalExp dl cfg regs mem ty (.gepConst flags baseTy (pTy, pExp) idxs) (.error err)
  | convConst_ok {mem ty op fromTy e toTy val m1 res m2} :
      EvalExp dl cfg regs mem fromTy e (.ok (val, m1)) →
      (∃ o o', evalConversionExec dl cfg m1 op fromTy val toTy o = .ok (res, m2, o')) →
      EvalExp dl cfg regs mem ty (.convConst op fromTy e toTy) (.ok (res, m2))
  | convConst_arg_err {mem ty op fromTy e toTy err} :
      EvalExp dl cfg regs mem fromTy e (.error err) →
      EvalExp dl cfg regs mem ty (.convConst op fromTy e toTy) (.error err)
  | convConst_eval_err {mem ty op fromTy e toTy val m1 err} :
      EvalExp dl cfg regs mem fromTy e (.ok (val, m1)) →
      (∃ o, evalConversionExec dl cfg m1 op fromTy val toTy o = .error err) →
      EvalExp dl cfg regs mem ty (.convConst op fromTy e toTy) (.error err)
  | binConst_ok {mem ty op cTy e1 e2 v1 m1 v2 m2 res} :
      EvalExp dl cfg regs mem cTy e1 (.ok (v1, m1)) →
      EvalExp dl cfg regs m1 cTy e2 (.ok (v2, m2)) →
      liftBinaryPure cTy.scalarType v1 v2 (evalIntBinaryScalarPure op) = .ok res →
      EvalExp dl cfg regs mem ty (.binConst op cTy e1 e2) (.ok (res, m2))
  | binConst_lhs_err {mem ty op cTy e1 e2 err} :
      EvalExp dl cfg regs mem cTy e1 (.error err) →
      EvalExp dl cfg regs mem ty (.binConst op cTy e1 e2) (.error err)
  | binConst_rhs_err {mem ty op cTy e1 e2 v1 m1 err} :
      EvalExp dl cfg regs mem cTy e1 (.ok (v1, m1)) →
      EvalExp dl cfg regs m1 cTy e2 (.error err) →
      EvalExp dl cfg regs mem ty (.binConst op cTy e1 e2) (.error err)
  | binConst_eval_err {mem ty op cTy e1 e2 v1 m1 v2 m2 err} :
      EvalExp dl cfg regs mem cTy e1 (.ok (v1, m1)) →
      EvalExp dl cfg regs m1 cTy e2 (.ok (v2, m2)) →
      liftBinaryPure cTy.scalarType v1 v2 (evalIntBinaryScalarPure op) = .error err →
      EvalExp dl cfg regs mem ty (.binConst op cTy e1 e2) (.error err)
  | insertElemConst_ok {mem ty vecTy vecE elemTy elemE idxTy idxE vecV m1 elemV m2 idxV m3 res} :
      EvalExp dl cfg regs mem vecTy vecE (.ok (vecV, m1)) →
      EvalExp dl cfg regs m1 elemTy elemE (.ok (elemV, m2)) →
      EvalExp dl cfg regs m2 idxTy idxE (.ok (idxV, m3)) →
      evalInsertElementPure vecV elemV idxV = .ok res →
      EvalExp dl cfg regs mem ty (.insertElemConst vecTy vecE elemTy elemE idxTy idxE) (.ok (res, m3))
  | insertElemConst_vec_err {mem ty vecTy vecE elemTy elemE idxTy idxE err} :
      EvalExp dl cfg regs mem vecTy vecE (.error err) →
      EvalExp dl cfg regs mem ty (.insertElemConst vecTy vecE elemTy elemE idxTy idxE) (.error err)
  | insertElemConst_elem_err {mem ty vecTy vecE elemTy elemE idxTy idxE vecV m1 err} :
      EvalExp dl cfg regs mem vecTy vecE (.ok (vecV, m1)) →
      EvalExp dl cfg regs m1 elemTy elemE (.error err) →
      EvalExp dl cfg regs mem ty (.insertElemConst vecTy vecE elemTy elemE idxTy idxE) (.error err)
  | insertElemConst_idx_err {mem ty vecTy vecE elemTy elemE idxTy idxE vecV m1 elemV m2 err} :
      EvalExp dl cfg regs mem vecTy vecE (.ok (vecV, m1)) →
      EvalExp dl cfg regs m1 elemTy elemE (.ok (elemV, m2)) →
      EvalExp dl cfg regs m2 idxTy idxE (.error err) →
      EvalExp dl cfg regs mem ty (.insertElemConst vecTy vecE elemTy elemE idxTy idxE) (.error err)
  | insertElemConst_eval_err {mem ty vecTy vecE elemTy elemE idxTy idxE vecV m1 elemV m2 idxV m3 err} :
      EvalExp dl cfg regs mem vecTy vecE (.ok (vecV, m1)) →
      EvalExp dl cfg regs m1 elemTy elemE (.ok (elemV, m2)) →
      EvalExp dl cfg regs m2 idxTy idxE (.ok (idxV, m3)) →
      evalInsertElementPure vecV elemV idxV = .error err →
      EvalExp dl cfg regs mem ty (.insertElemConst vecTy vecE elemTy elemE idxTy idxE) (.error err)

inductive EvalExpList (dl : DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap Identifier RegisterValue) :
    MemoryState → List (LlvmType × Exp) → Except ExecError (List RegisterValue × MemoryState) → Prop where
  | nil {mem} :
      EvalExpList dl cfg regs mem [] (.ok ([], mem))
  | cons_ok {mem t e rest v m1 vs m2} :
      EvalExp dl cfg regs mem t e (.ok (v, m1)) →
      EvalExpList dl cfg regs m1 rest (.ok (vs, m2)) →
      EvalExpList dl cfg regs mem ((t, e) :: rest) (.ok (v :: vs, m2))
  | cons_head_err {mem t e rest err} :
      EvalExp dl cfg regs mem t e (.error err) →
      EvalExpList dl cfg regs mem ((t, e) :: rest) (.error err)
  | cons_tail_err {mem t e rest v m1 err} :
      EvalExp dl cfg regs mem t e (.ok (v, m1)) →
      EvalExpList dl cfg regs m1 rest (.error err) →
      EvalExpList dl cfg regs mem ((t, e) :: rest) (.error err)
end

mutual
theorem EvalExp.preserves_wf {dl cfg regs mem ty e v mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : EvalExp dl cfg regs mem ty e (.ok (v, mem'))) :
    MemoryState.WellFormed mem' := by
  cases h with
  | leaf_ok _ => exact hwf
  | undef_ok _ _ => exact hwf
  | array_ok _ hl => exact EvalExpList.preserves_wf hwf hl
  | struct_ok _ hl => exact EvalExpList.preserves_wf hwf hl
  | vector_ok _ hl => exact EvalExpList.preserves_wf hwf hl
  | splat_ok he => exact EvalExp.preserves_wf hwf he
  | gepConst_ok hb hi _ => exact EvalExpList.preserves_wf (EvalExp.preserves_wf hwf hb) hi
  | convConst_ok ha hc =>
    obtain ⟨o, o', hev⟩ := hc
    exact evalConversionExec_preserves_wf (EvalExp.preserves_wf hwf ha) hev
  | binConst_ok h1 h2 _ => exact EvalExp.preserves_wf (EvalExp.preserves_wf hwf h1) h2
  | insertElemConst_ok h1 h2 h3 _ =>
    exact EvalExp.preserves_wf (EvalExp.preserves_wf (EvalExp.preserves_wf hwf h1) h2) h3

theorem EvalExpList.preserves_wf {dl cfg regs mem es vs mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : EvalExpList dl cfg regs mem es (.ok (vs, mem'))) :
    MemoryState.WellFormed mem' := by
  cases h with
  | nil => exact hwf
  | cons_ok h1 h2 => exact EvalExpList.preserves_wf (EvalExp.preserves_wf hwf h1) h2
end

/-- Relational evaluation of call arguments plus call-site `ValueAttr`s. -/
inductive EvalCallArgs (dl : DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap Identifier RegisterValue) :
    MemoryState → List (LlvmType × Exp × List ValueAttr) →
    Except ExecError (List RegisterValue × MemoryState) → Prop where
  | nil {mem} :
      EvalCallArgs dl cfg regs mem [] (.ok ([], mem))
  | cons_ok {mem ty e attrs rest rawV m1 v vs m2} :
      EvalExp dl cfg regs mem ty e (.ok (rawV, m1)) →
      applyValueAttrsPure dl m1 ty rawV attrs = .ok v →
      EvalCallArgs dl cfg regs m1 rest (.ok (vs, m2)) →
      EvalCallArgs dl cfg regs mem ((ty, e, attrs) :: rest) (.ok (v :: vs, m2))
  | cons_exp_err {mem ty e attrs rest err} :
      EvalExp dl cfg regs mem ty e (.error err) →
      EvalCallArgs dl cfg regs mem ((ty, e, attrs) :: rest) (.error err)
  | cons_attr_err {mem ty e attrs rest rawV m1 err} :
      EvalExp dl cfg regs mem ty e (.ok (rawV, m1)) →
      applyValueAttrsPure dl m1 ty rawV attrs = .error err →
      EvalCallArgs dl cfg regs mem ((ty, e, attrs) :: rest) (.error err)
  | cons_tail_err {mem ty e attrs rest rawV m1 v err} :
      EvalExp dl cfg regs mem ty e (.ok (rawV, m1)) →
      applyValueAttrsPure dl m1 ty rawV attrs = .ok v →
      EvalCallArgs dl cfg regs m1 rest (.error err) →
      EvalCallArgs dl cfg regs mem ((ty, e, attrs) :: rest) (.error err)

theorem EvalCallArgs.preserves_wf {dl cfg regs mem args vs mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : EvalCallArgs dl cfg regs mem args (.ok (vs, mem'))) :
    MemoryState.WellFormed mem' := by
  cases h with
  | nil => exact hwf
  | cons_ok he _ hrest => exact EvalCallArgs.preserves_wf (EvalExp.preserves_wf hwf he) hrest

/-- Relational parallel evaluation of leading `phi` instructions on a CFG edge from `predId`. -/
inductive EvalPhis (dl : DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap Identifier RegisterValue) (predId : BlockId) :
    MemoryState → Code → Except ExecError (List (RawId × RegisterValue) × MemoryState) → Prop where
  | nil {mem} :
      EvalPhis dl cfg regs predId mem [] (.ok ([], mem))
  | cons_ok {mem rid ty fmf incs md rest incExp b rawV m1 v1 v ups m2} :
      incs.find? (fun (_, b') => b' == predId) = some (incExp, b) →
      EvalExp dl cfg regs mem ty incExp (.ok (rawV, m1)) →
      (∃ o o', applyInputFMFExec fmf ty rawV o = .ok (v1, o')) →
      applyValueAttrsPure dl m1 ty v1 md = .ok v →
      EvalPhis dl cfg regs predId m1 rest (.ok (ups, m2)) →
      EvalPhis dl cfg regs predId mem ((.id rid, .phi ty fmf incs md) :: rest) (.ok ((rid, v) :: ups, m2))
  | cons_void_err {mem n ty fmf incs md rest msg} :
      EvalPhis dl cfg regs predId mem ((.void n, .phi ty fmf incs md) :: rest) (.error (.staticError msg))
  | cons_missing_pred {mem rid ty fmf incs md rest msg} :
      incs.find? (fun (_, b) => b == predId) = none →
      EvalPhis dl cfg regs predId mem ((.id rid, .phi ty fmf incs md) :: rest) (.error (.staticError msg))
  | cons_exp_err {mem rid ty fmf incs md rest incExp b err} :
      incs.find? (fun (_, b') => b' == predId) = some (incExp, b) →
      EvalExp dl cfg regs mem ty incExp (.error err) →
      EvalPhis dl cfg regs predId mem ((.id rid, .phi ty fmf incs md) :: rest) (.error err)
  | cons_fmf_err {mem rid ty fmf incs md rest incExp b rawV m1 err} :
      incs.find? (fun (_, b') => b' == predId) = some (incExp, b) →
      EvalExp dl cfg regs mem ty incExp (.ok (rawV, m1)) →
      (∃ o, applyInputFMFExec fmf ty rawV o = .error err) →
      EvalPhis dl cfg regs predId mem ((.id rid, .phi ty fmf incs md) :: rest) (.error err)
  | cons_md_err {mem rid ty fmf incs md rest incExp b rawV m1 v1 err} :
      incs.find? (fun (_, b') => b' == predId) = some (incExp, b) →
      EvalExp dl cfg regs mem ty incExp (.ok (rawV, m1)) →
      (∃ o o', applyInputFMFExec fmf ty rawV o = .ok (v1, o')) →
      applyValueAttrsPure dl m1 ty v1 md = .error err →
      EvalPhis dl cfg regs predId mem ((.id rid, .phi ty fmf incs md) :: rest) (.error err)
  | cons_tail_err {mem rid ty fmf incs md rest incExp b rawV m1 v1 v err} :
      incs.find? (fun (_, b') => b' == predId) = some (incExp, b) →
      EvalExp dl cfg regs mem ty incExp (.ok (rawV, m1)) →
      (∃ o o', applyInputFMFExec fmf ty rawV o = .ok (v1, o')) →
      applyValueAttrsPure dl m1 ty v1 md = .ok v →
      EvalPhis dl cfg regs predId m1 rest (.error err) →
      EvalPhis dl cfg regs predId mem ((.id rid, .phi ty fmf incs md) :: rest) (.error err)
  | cons_nonphi_err {mem iid instr rest msg} :
      (∀ ty fmf incs md, instr ≠ .phi ty fmf incs md) →
      EvalPhis dl cfg regs predId mem ((iid, instr) :: rest) (.error (.staticError msg))

theorem EvalPhis.preserves_wf {dl cfg regs predId mem phis ups mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : EvalPhis dl cfg regs predId mem phis (.ok (ups, mem'))) :
    MemoryState.WellFormed mem' := by
  cases h with
  | nil => exact hwf
  | cons_ok _ he _ _ hrest => exact EvalPhis.preserves_wf (EvalExp.preserves_wf hwf he) hrest

/-- Relational resolution of a `call` callee expression (direct `@fn` or indirect function pointer). -/
inductive EvalCallee (dl : DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap Identifier RegisterValue) :
    MemoryState → Exp → Except ExecError (FunctionId × MemoryState) → Prop where
  | direct {mem fid} :
      EvalCallee dl cfg regs mem (.identifier (.global_id fid)) (.ok (fid, mem))
  | indirect_ok {mem e as p m1 fid} :
      (∀ fid', e ≠ .identifier (.global_id fid')) →
      EvalExp dl cfg regs mem (.ptr dl.programAddrSpace) e (.ok (.ptr as (.value p), m1)) →
      m1.addrToFunc.get? p.addr.toNat = some fid →
      EvalCallee dl cfg regs mem e (.ok (fid, m1))
  | indirect_exp_err {mem e err} :
      (∀ fid', e ≠ .identifier (.global_id fid')) →
      EvalExp dl cfg regs mem (.ptr dl.programAddrSpace) e (.error err) →
      EvalCallee dl cfg regs mem e (.error err)
  | indirect_poison {mem e as m1 msg} :
      (∀ fid', e ≠ .identifier (.global_id fid')) →
      EvalExp dl cfg regs mem (.ptr dl.programAddrSpace) e (.ok (.ptr as .poison, m1)) →
      EvalCallee dl cfg regs mem e (.error (.immediateUB msg))
  | indirect_bad_addr {mem e as p m1 msg} :
      (∀ fid', e ≠ .identifier (.global_id fid')) →
      EvalExp dl cfg regs mem (.ptr dl.programAddrSpace) e (.ok (.ptr as (.value p), m1)) →
      m1.addrToFunc.get? p.addr.toNat = none →
      EvalCallee dl cfg regs mem e (.error (.immediateUB msg))
  | indirect_nonptr {mem e v m1 msg} :
      (∀ fid', e ≠ .identifier (.global_id fid')) →
      EvalExp dl cfg regs mem (.ptr dl.programAddrSpace) e (.ok (v, m1)) →
      (∀ as pv, v ≠ .ptr as pv) →
      EvalCallee dl cfg regs mem e (.error (.staticError msg))

theorem EvalCallee.preserves_wf {dl cfg regs mem e fid mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : EvalCallee dl cfg regs mem e (.ok (fid, mem'))) :
    MemoryState.WellFormed mem' := by
  cases h with
  | direct => exact hwf
  | indirect_ok _ he _ => exact EvalExp.preserves_wf hwf he

/-- Relational CFG edge transition to block `dest` (shared by `br`, `condBr`, and `switch`). -/
inductive StepJump (st : MachineState) (frame : CallFrame) (callers : List CallFrame)
    (mem : MemoryState) (dest : BlockId) : Config → Prop where
  | ok {nextBlk phis body ups mem'} :
      frame.defn.findBlock? dest = some nextBlk →
      splitPhis nextBlk.code = (phis, body) →
      EvalPhis st.dataLayout st.config frame.registers frame.curBlock mem phis (.ok (ups, mem')) →
      StepJump st frame callers mem dest
        (.running (st.withFramesAndMemory
          (frame.jumpTo nextBlk.id body nextBlk.terminator (commitPhiUpdates frame.registers ups) :: callers) mem'))
  | phi_err {nextBlk phis body err} :
      frame.defn.findBlock? dest = some nextBlk →
      splitPhis nextBlk.code = (phis, body) →
      EvalPhis st.dataLayout st.config frame.registers frame.curBlock mem phis (.error err) →
      StepJump st frame callers mem dest (Config.ofError err)
  | missing_block {msg} :
      frame.defn.findBlock? dest = none →
      StepJump st frame callers mem dest (.staticError msg)

/-- Relational evaluation of `llvm.assume` operand bundles. -/
inductive EvalAssumeBundles (dl : DataLayout) (cfg : SemanticsConfig)
    (regs : AssocMap Identifier RegisterValue) :
    MemoryState → List (String × List (LlvmType × Exp)) → Except ExecError MemoryState → Prop where
  | nil {mem} : EvalAssumeBundles dl cfg regs mem [] (.ok mem)
  | cons_skip {mem tag bargs rest res} :
      assumeBundleShouldEval tag = false →
      EvalAssumeBundles dl cfg regs mem rest res →
      EvalAssumeBundles dl cfg regs mem ((tag, bargs) :: rest) res
  | cons_ok {mem tag bargs rest vals m1 m2} :
      assumeBundleShouldEval tag = true →
      EvalExpList dl cfg regs mem bargs (.ok (vals, m1)) →
      evalAssumeBundlePure dl m1 tag vals = .ok () →
      EvalAssumeBundles dl cfg regs m1 rest (.ok m2) →
      EvalAssumeBundles dl cfg regs mem ((tag, bargs) :: rest) (.ok m2)
  | cons_eval_err {mem tag bargs rest err} :
      assumeBundleShouldEval tag = true →
      EvalExpList dl cfg regs mem bargs (.error err) →
      EvalAssumeBundles dl cfg regs mem ((tag, bargs) :: rest) (.error err)
  | cons_check_err {mem tag bargs rest vals m1 err} :
      assumeBundleShouldEval tag = true →
      EvalExpList dl cfg regs mem bargs (.ok (vals, m1)) →
      evalAssumeBundlePure dl m1 tag vals = .error err →
      EvalAssumeBundles dl cfg regs mem ((tag, bargs) :: rest) (.error err)
  | cons_tail_err {mem tag bargs rest vals m1 err} :
      assumeBundleShouldEval tag = true →
      EvalExpList dl cfg regs mem bargs (.ok (vals, m1)) →
      evalAssumeBundlePure dl m1 tag vals = .ok () →
      EvalAssumeBundles dl cfg regs m1 rest (.error err) →
      EvalAssumeBundles dl cfg regs mem ((tag, bargs) :: rest) (.error err)

theorem EvalAssumeBundles.preserves_wf {dl cfg regs mem bundles mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : EvalAssumeBundles dl cfg regs mem bundles (.ok mem')) :
    MemoryState.WellFormed mem' := by
  cases h with
  | nil => exact hwf
  | cons_skip _ hrest => exact EvalAssumeBundles.preserves_wf hwf hrest
  | cons_ok _ he _ hrest => exact EvalAssumeBundles.preserves_wf (EvalExpList.preserves_wf hwf he) hrest

/-- Relational return-value completion (frees frame allocas, applies callee & caller return attrs, pops frame). -/
inductive StepRet (st : MachineState) (frame : CallFrame) (callers : List CallFrame)
    (retTy : LlvmRetType) (retVal : RegisterValue) (m1 : MemoryState) : Config → Prop where
  | top_ok {retVal'} :
      callers = [] →
      applyRetFMFAndAttrsPure st.dataLayout (freeAllocaList m1 frame.frameAllocas)
        retTy {} frame.defn.prototype.retAttrs retVal = .ok retVal' →
      StepRet st frame callers retTy retVal m1 (.halted retVal' (freeAllocaList m1 frame.frameAllocas))
  | call_ok {caller restCallers retVal1 rd retVal2} :
      callers = caller :: restCallers →
      applyRetFMFAndAttrsPure st.dataLayout (freeAllocaList m1 frame.frameAllocas)
        retTy {} frame.defn.prototype.retAttrs retVal = .ok retVal1 →
      caller.returnDest? = some rd →
      (frame.defn.prototype.isNoReturn || rd.isNoReturn) = false →
      applyRetFMFAndAttrsPure st.dataLayout (freeAllocaList m1 frame.frameAllocas)
        rd.retTy rd.fmf rd.retAttrs retVal1 = .ok retVal2 →
      StepRet st frame callers retTy retVal m1
        (.running (st.withFramesAndMemory
          (((caller.withRegisters (match rd.retTy, rd.destId with
              | .ret _, .id rid => caller.registers.insert (.local_id rid) retVal2
              | _, _ => caller.registers)).withReturnDest none) :: restCallers)
          (freeAllocaList m1 frame.frameAllocas)))
  | noreturn_ub {caller restCallers retVal1 rd msg} :
      callers = caller :: restCallers →
      applyRetFMFAndAttrsPure st.dataLayout (freeAllocaList m1 frame.frameAllocas)
        retTy {} frame.defn.prototype.retAttrs retVal = .ok retVal1 →
      caller.returnDest? = some rd →
      (frame.defn.prototype.isNoReturn || rd.isNoReturn) = true →
      StepRet st frame callers retTy retVal m1 (.ub msg)
  | callee_attr_err {err} :
      applyRetFMFAndAttrsPure st.dataLayout (freeAllocaList m1 frame.frameAllocas)
        retTy {} frame.defn.prototype.retAttrs retVal = .error err →
      StepRet st frame callers retTy retVal m1 (Config.ofError err)
  | caller_attr_err {caller restCallers retVal1 rd err} :
      callers = caller :: restCallers →
      applyRetFMFAndAttrsPure st.dataLayout (freeAllocaList m1 frame.frameAllocas)
        retTy {} frame.defn.prototype.retAttrs retVal = .ok retVal1 →
      caller.returnDest? = some rd →
      (frame.defn.prototype.isNoReturn || rd.isNoReturn) = false →
      applyRetFMFAndAttrsPure st.dataLayout (freeAllocaList m1 frame.frameAllocas)
        rd.retTy rd.fmf rd.retAttrs retVal1 = .error err →
      StepRet st frame callers retTy retVal m1 (Config.ofError err)
  | missing_dest {caller restCallers retVal1 msg} :
      callers = caller :: restCallers →
      applyRetFMFAndAttrsPure st.dataLayout (freeAllocaList m1 frame.frameAllocas)
        retTy {} frame.defn.prototype.retAttrs retVal = .ok retVal1 →
      caller.returnDest? = none →
      StepRet st frame callers retTy retVal m1 (.staticError msg)

/-! ### Instruction-Indexed and Terminator-Indexed Small-Step Relations -/

/--
Relational small-step execution of a single instruction `instr` (indexed by `Instruction`
so dependent case analysis only considers rules for the concrete opcode).
-/
inductive StepInstr (st : MachineState) (frame : CallFrame) (callers : List CallFrame)
    (iid : InstructionId) (rest : Code) : Instruction → Option TraceEvent → Config → Prop where
  /- IntBinaryOp -/
  | intBinaryOp_ok {op ty e1 e2 v1 m1 v2 m2 res} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty e1 (.ok (v1, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 ty e2 (.ok (v2, m2)) →
      liftBinaryPure ty.scalarType v1 v2 (evalIntBinaryScalarPure op) = .ok res →
      StepInstr st frame callers iid rest (.intBinaryOp op ty e1 e2) none
        (finishRegInstr st frame callers rest iid res m2)
  | intBinaryOp_e1_err {op ty e1 e2 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty e1 (.error err) →
      StepInstr st frame callers iid rest (.intBinaryOp op ty e1 e2) none (Config.ofError err)
  | intBinaryOp_e2_err {op ty e1 e2 v1 m1 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty e1 (.ok (v1, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 ty e2 (.error err) →
      StepInstr st frame callers iid rest (.intBinaryOp op ty e1 e2) none (Config.ofError err)
  | intBinaryOp_eval_err {op ty e1 e2 v1 m1 v2 m2 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty e1 (.ok (v1, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 ty e2 (.ok (v2, m2)) →
      liftBinaryPure ty.scalarType v1 v2 (evalIntBinaryScalarPure op) = .error err →
      StepInstr st frame callers iid rest (.intBinaryOp op ty e1 e2) none (Config.ofError err)

  /- FloatUnaryOp -/
  | floatUnaryOp_ok {op ty e v m1 res} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty e (.ok (v, m1)) →
      (∃ o o', evalFloatUnaryExec op ty v o = .ok (res, o')) →
      StepInstr st frame callers iid rest (.floatUnaryOp op ty e) none
        (finishRegInstr st frame callers rest iid res m1)
  | floatUnaryOp_e_err {op ty e err} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty e (.error err) →
      StepInstr st frame callers iid rest (.floatUnaryOp op ty e) none (Config.ofError err)
  | floatUnaryOp_eval_err {op ty e v m1 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty e (.ok (v, m1)) →
      (∃ o, evalFloatUnaryExec op ty v o = .error err) →
      StepInstr st frame callers iid rest (.floatUnaryOp op ty e) none (Config.ofError err)

  /- FloatBinaryOp -/
  | floatBinaryOp_ok {op ty e1 e2 v1 m1 v2 m2 res} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty e1 (.ok (v1, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 ty e2 (.ok (v2, m2)) →
      (∃ o o', evalFloatBinaryExec st.config op ty v1 v2 o = .ok (res, o')) →
      StepInstr st frame callers iid rest (.floatBinaryOp op ty e1 e2) none
        (finishRegInstr st frame callers rest iid res m2)
  | floatBinaryOp_e1_err {op ty e1 e2 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty e1 (.error err) →
      StepInstr st frame callers iid rest (.floatBinaryOp op ty e1 e2) none (Config.ofError err)
  | floatBinaryOp_e2_err {op ty e1 e2 v1 m1 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty e1 (.ok (v1, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 ty e2 (.error err) →
      StepInstr st frame callers iid rest (.floatBinaryOp op ty e1 e2) none (Config.ofError err)
  | floatBinaryOp_eval_err {op ty e1 e2 v1 m1 v2 m2 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty e1 (.ok (v1, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 ty e2 (.ok (v2, m2)) →
      (∃ o, evalFloatBinaryExec st.config op ty v1 v2 o = .error err) →
      StepInstr st frame callers iid rest (.floatBinaryOp op ty e1 e2) none (Config.ofError err)

  /- ICmp -/
  | icmp_ok {ss pred ty e1 e2 v1 m1 v2 m2 res} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty e1 (.ok (v1, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 ty e2 (.ok (v2, m2)) →
      liftBinaryPure .i1 v1 v2 (evalICmpScalarPure st.dataLayout ss pred) = .ok res →
      StepInstr st frame callers iid rest (.icmp ss pred ty e1 e2) none
        (finishRegInstr st frame callers rest iid res m2)
  | icmp_e1_err {ss pred ty e1 e2 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty e1 (.error err) →
      StepInstr st frame callers iid rest (.icmp ss pred ty e1 e2) none (Config.ofError err)
  | icmp_e2_err {ss pred ty e1 e2 v1 m1 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty e1 (.ok (v1, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 ty e2 (.error err) →
      StepInstr st frame callers iid rest (.icmp ss pred ty e1 e2) none (Config.ofError err)
  | icmp_eval_err {ss pred ty e1 e2 v1 m1 v2 m2 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty e1 (.ok (v1, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 ty e2 (.ok (v2, m2)) →
      liftBinaryPure .i1 v1 v2 (evalICmpScalarPure st.dataLayout ss pred) = .error err →
      StepInstr st frame callers iid rest (.icmp ss pred ty e1 e2) none (Config.ofError err)

  /- FCmp -/
  | fcmp_ok {fmf pred ty e1 e2 v1 m1 v2 m2 res} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty e1 (.ok (v1, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 ty e2 (.ok (v2, m2)) →
      (∃ o o', evalFCmpExec st.config fmf pred v1 v2 o = .ok (res, o')) →
      StepInstr st frame callers iid rest (.fcmp fmf pred ty e1 e2) none
        (finishRegInstr st frame callers rest iid res m2)
  | fcmp_e1_err {fmf pred ty e1 e2 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty e1 (.error err) →
      StepInstr st frame callers iid rest (.fcmp fmf pred ty e1 e2) none (Config.ofError err)
  | fcmp_e2_err {fmf pred ty e1 e2 v1 m1 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty e1 (.ok (v1, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 ty e2 (.error err) →
      StepInstr st frame callers iid rest (.fcmp fmf pred ty e1 e2) none (Config.ofError err)
  | fcmp_eval_err {fmf pred ty e1 e2 v1 m1 v2 m2 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty e1 (.ok (v1, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 ty e2 (.ok (v2, m2)) →
      (∃ o, evalFCmpExec st.config fmf pred v1 v2 o = .error err) →
      StepInstr st frame callers iid rest (.fcmp fmf pred ty e1 e2) none (Config.ofError err)

  /- ConversionOp -/
  | conversionOp_ok {op fromTy e toTy v m1 res m2} :
      EvalExp st.dataLayout st.config frame.registers st.memory fromTy e (.ok (v, m1)) →
      (∃ o o', evalConversionExec st.dataLayout st.config m1 op fromTy v toTy o = .ok (res, m2, o')) →
      StepInstr st frame callers iid rest (.conversionOp op fromTy e toTy) none
        (finishRegInstr st frame callers rest iid res m2)
  | conversionOp_e_err {op fromTy e toTy err} :
      EvalExp st.dataLayout st.config frame.registers st.memory fromTy e (.error err) →
      StepInstr st frame callers iid rest (.conversionOp op fromTy e toTy) none (Config.ofError err)
  | conversionOp_eval_err {op fromTy e toTy v m1 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory fromTy e (.ok (v, m1)) →
      (∃ o, evalConversionExec st.dataLayout st.config m1 op fromTy v toTy o = .error err) →
      StepInstr st frame callers iid rest (.conversionOp op fromTy e toTy) none (Config.ofError err)

  /- Select -/
  | select_ok {fmf condTy cond valTy tv fv cV m1 tV m2 fV m3 rawRes res} :
      EvalExp st.dataLayout st.config frame.registers st.memory condTy cond (.ok (cV, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 valTy tv (.ok (tV, m2)) →
      EvalExp st.dataLayout st.config frame.registers m2 valTy fv (.ok (fV, m3)) →
      evalSelectPure cV tV fV = .ok rawRes →
      (∃ o o', applyInputFMFExec fmf valTy rawRes o = .ok (res, o')) →
      StepInstr st frame callers iid rest (.select fmf condTy cond valTy tv fv) none
        (finishRegInstr st frame callers rest iid res m3)
  | select_cond_err {fmf condTy cond valTy tv fv err} :
      EvalExp st.dataLayout st.config frame.registers st.memory condTy cond (.error err) →
      StepInstr st frame callers iid rest (.select fmf condTy cond valTy tv fv) none (Config.ofError err)
  | select_tv_err {fmf condTy cond valTy tv fv cV m1 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory condTy cond (.ok (cV, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 valTy tv (.error err) →
      StepInstr st frame callers iid rest (.select fmf condTy cond valTy tv fv) none (Config.ofError err)
  | select_fv_err {fmf condTy cond valTy tv fv cV m1 tV m2 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory condTy cond (.ok (cV, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 valTy tv (.ok (tV, m2)) →
      EvalExp st.dataLayout st.config frame.registers m2 valTy fv (.error err) →
      StepInstr st frame callers iid rest (.select fmf condTy cond valTy tv fv) none (Config.ofError err)
  | select_eval_err {fmf condTy cond valTy tv fv cV m1 tV m2 fV m3 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory condTy cond (.ok (cV, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 valTy tv (.ok (tV, m2)) →
      EvalExp st.dataLayout st.config frame.registers m2 valTy fv (.ok (fV, m3)) →
      evalSelectPure cV tV fV = .error err →
      StepInstr st frame callers iid rest (.select fmf condTy cond valTy tv fv) none (Config.ofError err)
  | select_fmf_err {fmf condTy cond valTy tv fv cV m1 tV m2 fV m3 rawRes err} :
      EvalExp st.dataLayout st.config frame.registers st.memory condTy cond (.ok (cV, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 valTy tv (.ok (tV, m2)) →
      EvalExp st.dataLayout st.config frame.registers m2 valTy fv (.ok (fV, m3)) →
      evalSelectPure cV tV fV = .ok rawRes →
      (∃ o, applyInputFMFExec fmf valTy rawRes o = .error err) →
      StepInstr st frame callers iid rest (.select fmf condTy cond valTy tv fv) none (Config.ofError err)

  /- Stray Phi -/
  | stray_phi {ty fmf incs md msg} :
      StepInstr st frame callers iid rest (.phi ty fmf incs md) none (.staticError msg)

  /- Alloca (relational via MemoryState.AllocSpec) -/
  | alloca_ok {allocTy numEl? align? addrSpace count m1 obj mem'} :
      (match numEl? with
        | none => count = 1 ∧ m1 = st.memory
        | some (nTy, nExp) => ∃ (w : Nat) (bv : BitVec w),
            EvalExp st.dataLayout st.config frame.registers st.memory nTy nExp (.ok (.bv w (.value bv), m1)) ∧
            count = bv.toNat) →
      MemoryState.AllocSpec m1 st.dataLayout st.config
        (st.dataLayout.typeAllocSize allocTy * count)
        (align?.getD (st.dataLayout.typeABIAlign allocTy))
        (match iid with | .id rid => rid.ToString | .void n => s!"alloca.{n}")
        addrSpace .uninitialized .stack false obj mem' →
      StepInstr st frame callers iid rest (.alloca allocTy numEl? align? addrSpace) none
        (finishRegInstr st frame callers rest iid
          (.ptr addrSpace (.value (MemoryState.derivePointer st.dataLayout obj)))
          mem' (obj.allocId :: frame.frameAllocas))
  | alloca_bad_size {allocTy numEl? align? addrSpace count m1 msg} :
      (match numEl? with
        | none => count = 1 ∧ m1 = st.memory
        | some (nTy, nExp) => ∃ (w : Nat) (bv : BitVec w),
            EvalExp st.dataLayout st.config frame.registers st.memory nTy nExp (.ok (.bv w (.value bv), m1)) ∧
            count = bv.toNat) →
      MemoryState.exceedsMaxObjectSize st.dataLayout (st.dataLayout.typeAllocSize allocTy * count) addrSpace = true →
      StepInstr st frame callers iid rest (.alloca allocTy numEl? align? addrSpace) none (.ub msg)
  | alloca_oom {allocTy numEl? align? addrSpace count m1} :
      (match numEl? with
        | none => count = 1 ∧ m1 = st.memory
        | some (nTy, nExp) => ∃ (w : Nat) (bv : BitVec w),
            EvalExp st.dataLayout st.config frame.registers st.memory nTy nExp (.ok (.bv w (.value bv), m1)) ∧
            count = bv.toNat) →
      ((st.config.maxMem ≠ 0 ∧ m1.usedMem + max 1 (st.dataLayout.typeAllocSize allocTy * count) > st.config.maxMem) ∨
       DataLayout.alignTo m1.nextAddr (max 1 (align?.getD (st.dataLayout.typeABIAlign allocTy))) +
         max 1 (st.dataLayout.typeAllocSize allocTy * count) ≥ 1 <<< st.dataLayout.getAddressSizeInBits addrSpace) →
      StepInstr st frame callers iid rest (.alloca allocTy numEl? align? addrSpace) none (.resourceError .outOfMemory)
  | alloca_count_err {allocTy nTy nExp align? addrSpace err} :
      EvalExp st.dataLayout st.config frame.registers st.memory nTy nExp (.error err) →
      StepInstr st frame callers iid rest (.alloca allocTy (some (nTy, nExp)) align? addrSpace) none (Config.ofError err)
  | alloca_count_poison {allocTy nTy nExp align? addrSpace w m1 msg} :
      EvalExp st.dataLayout st.config frame.registers st.memory nTy nExp (.ok (.bv w .poison, m1)) →
      StepInstr st frame callers iid rest (.alloca allocTy (some (nTy, nExp)) align? addrSpace) none (.ub msg)
  | alloca_count_nonint {allocTy nTy nExp align? addrSpace v m1 msg} :
      EvalExp st.dataLayout st.config frame.registers st.memory nTy nExp (.ok (v, m1)) →
      (∀ w iv, v ≠ .bv w iv) →
      StepInstr st frame callers iid rest (.alloca allocTy (some (nTy, nExp)) align? addrSpace) none (.staticError msg)

  /- Load (relational via BytesToValueRel; volatile emits TraceEvent.volatileLoad; supports !nonnull / !range / !noundef) -/
  | load_ok {ty ptrTy ptrExp align? isVol noundef md as p m1 mo offset rawVal val hasUndef} :
      EvalExp st.dataLayout st.config frame.registers st.memory ptrTy ptrExp (.ok (.ptr as (.value p), m1)) →
      m1.verifyMemAccess p (st.dataLayout.typeStoreSize ty) (align?.getD (st.dataLayout.typeABIAlign ty)) false = .ok (mo, offset) →
      BytesToValueRel st.dataLayout st.config
        (MemoryState.readObjectBytes mo offset (st.dataLayout.typeStoreSize ty)) ty rawVal hasUndef →
      applyValueAttrsPure st.dataLayout m1 ty rawVal md = .ok val →
      (noundef = true → hasUndef = false ∧ val.containsPoison = false) →
      StepInstr st frame callers iid rest (.load ty ptrTy ptrExp align? isVol noundef md)
        (if isVol then some (.volatileLoad mo.addrSpace p.addr.toNat
          (MemoryState.readObjectBytes mo offset (st.dataLayout.typeStoreSize ty))) else none)
        (finishRegInstr st frame callers rest iid val m1)
  | load_md_err {ty ptrTy ptrExp align? isVol noundef md as p m1 mo offset rawVal hasUndef err} :
      EvalExp st.dataLayout st.config frame.registers st.memory ptrTy ptrExp (.ok (.ptr as (.value p), m1)) →
      m1.verifyMemAccess p (st.dataLayout.typeStoreSize ty) (align?.getD (st.dataLayout.typeABIAlign ty)) false = .ok (mo, offset) →
      BytesToValueRel st.dataLayout st.config
        (MemoryState.readObjectBytes mo offset (st.dataLayout.typeStoreSize ty)) ty rawVal hasUndef →
      applyValueAttrsPure st.dataLayout m1 ty rawVal md = .error err →
      StepInstr st frame callers iid rest (.load ty ptrTy ptrExp align? isVol noundef md)
        (if isVol then some (.volatileLoad mo.addrSpace p.addr.toNat
          (MemoryState.readObjectBytes mo offset (st.dataLayout.typeStoreSize ty))) else none)
        (Config.ofError err)
  | load_noundef_ub {ty ptrTy ptrExp align? isVol md as p m1 mo offset rawVal val hasUndef msg} :
      EvalExp st.dataLayout st.config frame.registers st.memory ptrTy ptrExp (.ok (.ptr as (.value p), m1)) →
      m1.verifyMemAccess p (st.dataLayout.typeStoreSize ty) (align?.getD (st.dataLayout.typeABIAlign ty)) false = .ok (mo, offset) →
      BytesToValueRel st.dataLayout st.config
        (MemoryState.readObjectBytes mo offset (st.dataLayout.typeStoreSize ty)) ty rawVal hasUndef →
      applyValueAttrsPure st.dataLayout m1 ty rawVal md = .ok val →
      (hasUndef = true ∨ val.containsPoison = true) →
      StepInstr st frame callers iid rest (.load ty ptrTy ptrExp align? isVol true md)
        (if isVol then some (.volatileLoad mo.addrSpace p.addr.toNat
          (MemoryState.readObjectBytes mo offset (st.dataLayout.typeStoreSize ty))) else none)
        (.ub msg)
  | load_ptr_err {ty ptrTy ptrExp align? isVol noundef md err} :
      EvalExp st.dataLayout st.config frame.registers st.memory ptrTy ptrExp (.error err) →
      StepInstr st frame callers iid rest (.load ty ptrTy ptrExp align? isVol noundef md) none (Config.ofError err)
  | load_ptr_poison {ty ptrTy ptrExp align? isVol noundef md as m1 msg} :
      EvalExp st.dataLayout st.config frame.registers st.memory ptrTy ptrExp (.ok (.ptr as .poison, m1)) →
      StepInstr st frame callers iid rest (.load ty ptrTy ptrExp align? isVol noundef md) none (.ub msg)
  | load_ptr_nonptr {ty ptrTy ptrExp align? isVol noundef md v m1 msg} :
      EvalExp st.dataLayout st.config frame.registers st.memory ptrTy ptrExp (.ok (v, m1)) →
      (∀ as pv, v ≠ .ptr as pv) →
      StepInstr st frame callers iid rest (.load ty ptrTy ptrExp align? isVol noundef md) none (.staticError msg)
  | load_mem_err {ty ptrTy ptrExp align? isVol noundef md as p m1 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory ptrTy ptrExp (.ok (.ptr as (.value p), m1)) →
      m1.verifyMemAccess p (st.dataLayout.typeStoreSize ty) (align?.getD (st.dataLayout.typeABIAlign ty)) false = .error err →
      StepInstr st frame callers iid rest (.load ty ptrTy ptrExp align? isVol noundef md) none (Config.ofError err)

  /- Store (volatile emits TraceEvent.volatileStore) -/
  | store_ok {valTy valExp ptrTy ptrExp align? isVol val m1 as p m2 mo offset} :
      EvalExp st.dataLayout st.config frame.registers st.memory valTy valExp (.ok (val, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 ptrTy ptrExp (.ok (.ptr as (.value p), m2)) →
      m2.verifyMemAccess p (st.dataLayout.typeStoreSize valTy) (align?.getD (st.dataLayout.typeABIAlign valTy)) true = .ok (mo, offset) →
      StepInstr st frame callers iid rest (.store valTy valExp ptrTy ptrExp align? isVol)
        (if isVol then some (.volatileStore mo.addrSpace p.addr.toNat
          (valueToBytes st.dataLayout st.config val valTy)) else none)
        (finishVoidInstr st frame callers rest
          (m2.writeObjectBytes mo.allocId offset (valueToBytes st.dataLayout st.config val valTy)))
  | store_val_err {valTy valExp ptrTy ptrExp align? isVol err} :
      EvalExp st.dataLayout st.config frame.registers st.memory valTy valExp (.error err) →
      StepInstr st frame callers iid rest (.store valTy valExp ptrTy ptrExp align? isVol) none (Config.ofError err)
  | store_ptr_err {valTy valExp ptrTy ptrExp align? isVol val m1 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory valTy valExp (.ok (val, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 ptrTy ptrExp (.error err) →
      StepInstr st frame callers iid rest (.store valTy valExp ptrTy ptrExp align? isVol) none (Config.ofError err)
  | store_ptr_poison {valTy valExp ptrTy ptrExp align? isVol val m1 as m2 msg} :
      EvalExp st.dataLayout st.config frame.registers st.memory valTy valExp (.ok (val, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 ptrTy ptrExp (.ok (.ptr as .poison, m2)) →
      StepInstr st frame callers iid rest (.store valTy valExp ptrTy ptrExp align? isVol) none (.ub msg)
  | store_ptr_nonptr {valTy valExp ptrTy ptrExp align? isVol val m1 v m2 msg} :
      EvalExp st.dataLayout st.config frame.registers st.memory valTy valExp (.ok (val, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 ptrTy ptrExp (.ok (v, m2)) →
      (∀ as pv, v ≠ .ptr as pv) →
      StepInstr st frame callers iid rest (.store valTy valExp ptrTy ptrExp align? isVol) none (.staticError msg)
  | store_mem_err {valTy valExp ptrTy ptrExp align? isVol val m1 as p m2 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory valTy valExp (.ok (val, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 ptrTy ptrExp (.ok (.ptr as (.value p), m2)) →
      m2.verifyMemAccess p (st.dataLayout.typeStoreSize valTy) (align?.getD (st.dataLayout.typeABIAlign valTy)) true = .error err →
      StepInstr st frame callers iid rest (.store valTy valExp ptrTy ptrExp align? isVol) none (Config.ofError err)

  /- GetElementPtr -/
  | gep_ok {flags baseTy ptrTy ptrExp idxs baseVal m1 idxVals m2 res} :
      EvalExp st.dataLayout st.config frame.registers st.memory ptrTy ptrExp (.ok (baseVal, m1)) →
      EvalExpList st.dataLayout st.config frame.registers m1 idxs (.ok (idxVals, m2)) →
      evalGEPValuesPure st.dataLayout m2 flags baseTy ptrTy baseVal idxVals = .ok res →
      StepInstr st frame callers iid rest (.getelementptr flags baseTy ptrTy ptrExp idxs) none
        (finishRegInstr st frame callers rest iid res m2)
  | gep_base_err {flags baseTy ptrTy ptrExp idxs err} :
      EvalExp st.dataLayout st.config frame.registers st.memory ptrTy ptrExp (.error err) →
      StepInstr st frame callers iid rest (.getelementptr flags baseTy ptrTy ptrExp idxs) none (Config.ofError err)
  | gep_idx_err {flags baseTy ptrTy ptrExp idxs baseVal m1 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory ptrTy ptrExp (.ok (baseVal, m1)) →
      EvalExpList st.dataLayout st.config frame.registers m1 idxs (.error err) →
      StepInstr st frame callers iid rest (.getelementptr flags baseTy ptrTy ptrExp idxs) none (Config.ofError err)
  | gep_eval_err {flags baseTy ptrTy ptrExp idxs baseVal m1 idxVals m2 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory ptrTy ptrExp (.ok (baseVal, m1)) →
      EvalExpList st.dataLayout st.config frame.registers m1 idxs (.ok (idxVals, m2)) →
      evalGEPValuesPure st.dataLayout m2 flags baseTy ptrTy baseVal idxVals = .error err →
      StepInstr st frame callers iid rest (.getelementptr flags baseTy ptrTy ptrExp idxs) none (Config.ofError err)

  /- ExtractValue / InsertValue / ExtractElement / InsertElement / ShuffleVector -/
  | extractvalue_ok {aggTy aggExp idxs aggV m1 res} :
      EvalExp st.dataLayout st.config frame.registers st.memory aggTy aggExp (.ok (aggV, m1)) →
      extractValueAux aggV idxs = .ok res →
      StepInstr st frame callers iid rest (.extractvalue aggTy aggExp idxs) none
        (finishRegInstr st frame callers rest iid res m1)
  | extractvalue_e_err {aggTy aggExp idxs err} :
      EvalExp st.dataLayout st.config frame.registers st.memory aggTy aggExp (.error err) →
      StepInstr st frame callers iid rest (.extractvalue aggTy aggExp idxs) none (Config.ofError err)
  | extractvalue_eval_err {aggTy aggExp idxs aggV m1 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory aggTy aggExp (.ok (aggV, m1)) →
      extractValueAux aggV idxs = .error err →
      StepInstr st frame callers iid rest (.extractvalue aggTy aggExp idxs) none (Config.ofError err)

  | insertvalue_ok {aggTy aggExp valTy valExp idxs aggV m1 insV m2 res} :
      EvalExp st.dataLayout st.config frame.registers st.memory aggTy aggExp (.ok (aggV, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 valTy valExp (.ok (insV, m2)) →
      insertValueAux aggV insV idxs = .ok res →
      StepInstr st frame callers iid rest (.insertvalue aggTy aggExp valTy valExp idxs) none
        (finishRegInstr st frame callers rest iid res m2)
  | insertvalue_agg_err {aggTy aggExp valTy valExp idxs err} :
      EvalExp st.dataLayout st.config frame.registers st.memory aggTy aggExp (.error err) →
      StepInstr st frame callers iid rest (.insertvalue aggTy aggExp valTy valExp idxs) none (Config.ofError err)
  | insertvalue_val_err {aggTy aggExp valTy valExp idxs aggV m1 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory aggTy aggExp (.ok (aggV, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 valTy valExp (.error err) →
      StepInstr st frame callers iid rest (.insertvalue aggTy aggExp valTy valExp idxs) none (Config.ofError err)
  | insertvalue_eval_err {aggTy aggExp valTy valExp idxs aggV m1 insV m2 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory aggTy aggExp (.ok (aggV, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 valTy valExp (.ok (insV, m2)) →
      insertValueAux aggV insV idxs = .error err →
      StepInstr st frame callers iid rest (.insertvalue aggTy aggExp valTy valExp idxs) none (Config.ofError err)

  | extractelement_ok {vecTy vecExp idxTy idxExp vecV m1 idxV m2 res} :
      EvalExp st.dataLayout st.config frame.registers st.memory vecTy vecExp (.ok (vecV, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 idxTy idxExp (.ok (idxV, m2)) →
      evalExtractElementPure vecV idxV = .ok res →
      StepInstr st frame callers iid rest (.extractelement vecTy vecExp idxTy idxExp) none
        (finishRegInstr st frame callers rest iid res m2)
  | extractelement_vec_err {vecTy vecExp idxTy idxExp err} :
      EvalExp st.dataLayout st.config frame.registers st.memory vecTy vecExp (.error err) →
      StepInstr st frame callers iid rest (.extractelement vecTy vecExp idxTy idxExp) none (Config.ofError err)
  | extractelement_idx_err {vecTy vecExp idxTy idxExp vecV m1 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory vecTy vecExp (.ok (vecV, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 idxTy idxExp (.error err) →
      StepInstr st frame callers iid rest (.extractelement vecTy vecExp idxTy idxExp) none (Config.ofError err)
  | extractelement_eval_err {vecTy vecExp idxTy idxExp vecV m1 idxV m2 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory vecTy vecExp (.ok (vecV, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 idxTy idxExp (.ok (idxV, m2)) →
      evalExtractElementPure vecV idxV = .error err →
      StepInstr st frame callers iid rest (.extractelement vecTy vecExp idxTy idxExp) none (Config.ofError err)

  | insertelement_ok {vecTy vecExp valTy valExp idxTy idxExp vecV m1 valV m2 idxV m3 res} :
      EvalExp st.dataLayout st.config frame.registers st.memory vecTy vecExp (.ok (vecV, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 valTy valExp (.ok (valV, m2)) →
      EvalExp st.dataLayout st.config frame.registers m2 idxTy idxExp (.ok (idxV, m3)) →
      evalInsertElementPure vecV valV idxV = .ok res →
      StepInstr st frame callers iid rest (.insertelement vecTy vecExp valTy valExp idxTy idxExp) none
        (finishRegInstr st frame callers rest iid res m3)
  | insertelement_vec_err {vecTy vecExp valTy valExp idxTy idxExp err} :
      EvalExp st.dataLayout st.config frame.registers st.memory vecTy vecExp (.error err) →
      StepInstr st frame callers iid rest (.insertelement vecTy vecExp valTy valExp idxTy idxExp) none (Config.ofError err)
  | insertelement_val_err {vecTy vecExp valTy valExp idxTy idxExp vecV m1 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory vecTy vecExp (.ok (vecV, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 valTy valExp (.error err) →
      StepInstr st frame callers iid rest (.insertelement vecTy vecExp valTy valExp idxTy idxExp) none (Config.ofError err)
  | insertelement_idx_err {vecTy vecExp valTy valExp idxTy idxExp vecV m1 valV m2 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory vecTy vecExp (.ok (vecV, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 valTy valExp (.ok (valV, m2)) →
      EvalExp st.dataLayout st.config frame.registers m2 idxTy idxExp (.error err) →
      StepInstr st frame callers iid rest (.insertelement vecTy vecExp valTy valExp idxTy idxExp) none (Config.ofError err)
  | insertelement_eval_err {vecTy vecExp valTy valExp idxTy idxExp vecV m1 valV m2 idxV m3 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory vecTy vecExp (.ok (vecV, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 valTy valExp (.ok (valV, m2)) →
      EvalExp st.dataLayout st.config frame.registers m2 idxTy idxExp (.ok (idxV, m3)) →
      evalInsertElementPure vecV valV idxV = .error err →
      StepInstr st frame callers iid rest (.insertelement vecTy vecExp valTy valExp idxTy idxExp) none (Config.ofError err)

  | shufflevector_ok {vecTy e1 e2 mask v1 m1 v2 m2 res} :
      EvalExp st.dataLayout st.config frame.registers st.memory vecTy e1 (.ok (v1, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 vecTy e2 (.ok (v2, m2)) →
      evalShuffleVectorPure v1 v2 mask = .ok res →
      StepInstr st frame callers iid rest (.shufflevector vecTy e1 e2 mask) none
        (finishRegInstr st frame callers rest iid res m2)
  | shufflevector_e1_err {vecTy e1 e2 mask err} :
      EvalExp st.dataLayout st.config frame.registers st.memory vecTy e1 (.error err) →
      StepInstr st frame callers iid rest (.shufflevector vecTy e1 e2 mask) none (Config.ofError err)
  | shufflevector_e2_err {vecTy e1 e2 mask v1 m1 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory vecTy e1 (.ok (v1, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 vecTy e2 (.error err) →
      StepInstr st frame callers iid rest (.shufflevector vecTy e1 e2 mask) none (Config.ofError err)
  | shufflevector_eval_err {vecTy e1 e2 mask v1 m1 v2 m2 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory vecTy e1 (.ok (v1, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 vecTy e2 (.ok (v2, m2)) →
      evalShuffleVectorPure v1 v2 mask = .error err →
      StepInstr st frame callers iid rest (.shufflevector vecTy e1 e2 mask) none (Config.ofError err)

  /- Freeze (relational via FreezeRel) -/
  | freeze_ok {ty e val m1 frozen} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty e (.ok (val, m1)) →
      FreezeRel st.dataLayout st.config val frozen →
      StepInstr st frame callers iid rest (.freeze (ty, e)) none
        (finishRegInstr st frame callers rest iid frozen m1)
  | freeze_err {ty e err} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty e (.error err) →
      StepInstr st frame callers iid rest (.freeze (ty, e)) none (Config.ofError err)

  /- Bitinsert / Bitextract -/
  | bitinsert_ok {baseTy base valTy val offTy off vBase m1 vVal m2 vOff m3 res} :
      EvalExp st.dataLayout st.config frame.registers st.memory baseTy base (.ok (vBase, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 valTy val (.ok (vVal, m2)) →
      EvalExp st.dataLayout st.config frame.registers m2 offTy off (.ok (vOff, m3)) →
      evalBitInsertPure st.dataLayout baseTy valTy vBase vVal vOff = .ok res →
      StepInstr st frame callers iid rest (.bitinsert baseTy base valTy val offTy off) none
        (finishRegInstr st frame callers rest iid res m3)
  | bitinsert_err1 {baseTy base valTy val offTy off err} :
      EvalExp st.dataLayout st.config frame.registers st.memory baseTy base (.error err) →
      StepInstr st frame callers iid rest (.bitinsert baseTy base valTy val offTy off) none (Config.ofError err)
  | bitinsert_err2 {baseTy base valTy val offTy off vBase m1 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory baseTy base (.ok (vBase, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 valTy val (.error err) →
      StepInstr st frame callers iid rest (.bitinsert baseTy base valTy val offTy off) none (Config.ofError err)
  | bitinsert_err3 {baseTy base valTy val offTy off vBase m1 vVal m2 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory baseTy base (.ok (vBase, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 valTy val (.ok (vVal, m2)) →
      EvalExp st.dataLayout st.config frame.registers m2 offTy off (.error err) →
      StepInstr st frame callers iid rest (.bitinsert baseTy base valTy val offTy off) none (Config.ofError err)
  | bitinsert_eval_err {baseTy base valTy val offTy off vBase m1 vVal m2 vOff m3 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory baseTy base (.ok (vBase, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 valTy val (.ok (vVal, m2)) →
      EvalExp st.dataLayout st.config frame.registers m2 offTy off (.ok (vOff, m3)) →
      evalBitInsertPure st.dataLayout baseTy valTy vBase vVal vOff = .error err →
      StepInstr st frame callers iid rest (.bitinsert baseTy base valTy val offTy off) none (Config.ofError err)
  | bitextract_ok {retTy srcTy src offTy off vSrc m1 vOff m2 res} :
      EvalExp st.dataLayout st.config frame.registers st.memory srcTy src (.ok (vSrc, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 offTy off (.ok (vOff, m2)) →
      evalBitExtractPure st.dataLayout retTy vSrc vOff = .ok res →
      StepInstr st frame callers iid rest (.bitextract retTy srcTy src offTy off) none
        (finishRegInstr st frame callers rest iid res m2)
  | bitextract_err1 {retTy srcTy src offTy off err} :
      EvalExp st.dataLayout st.config frame.registers st.memory srcTy src (.error err) →
      StepInstr st frame callers iid rest (.bitextract retTy srcTy src offTy off) none (Config.ofError err)
  | bitextract_err2 {retTy srcTy src offTy off vSrc m1 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory srcTy src (.ok (vSrc, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 offTy off (.error err) →
      StepInstr st frame callers iid rest (.bitextract retTy srcTy src offTy off) none (Config.ofError err)
  | bitextract_eval_err {retTy srcTy src offTy off vSrc m1 vOff m2 err} :
      EvalExp st.dataLayout st.config frame.registers st.memory srcTy src (.ok (vSrc, m1)) →
      EvalExp st.dataLayout st.config frame.registers m1 offTy off (.ok (vOff, m2)) →
      evalBitExtractPure st.dataLayout retTy vSrc vOff = .error err →
      StepInstr st frame callers iid rest (.bitextract retTy srcTy src offTy off) none (Config.ofError err)

  /- Call (alloc libcalls via AllocLibcallSpec, non-alloc intrinsics, user-defined functions) -/
  | call_args_err {retTy fmf calleeExp args retAttrs bundles isNoRet err} :
      EvalCallArgs st.dataLayout st.config frame.registers st.memory args (.error err) →
      StepInstr st frame callers iid rest (.call retTy fmf calleeExp args retAttrs bundles isNoRet) none (Config.ofError err)
  | call_callee_err {retTy fmf calleeExp args retAttrs bundles isNoRet argVals m1 err} :
      EvalCallArgs st.dataLayout st.config frame.registers st.memory args (.ok (argVals, m1)) →
      EvalCallee st.dataLayout st.config frame.registers m1 calleeExp (.error err) →
      StepInstr st frame callers iid rest (.call retTy fmf calleeExp args retAttrs bundles isNoRet) none (Config.ofError err)
  | call_alloc_ok {retTy fmf calleeExp args retAttrs bundles isNoRet argVals m1 fid m2 rawRet m3 finalRet} :
      EvalCallArgs st.dataLayout st.config frame.registers st.memory args (.ok (argVals, m1)) →
      EvalCallee st.dataLayout st.config frame.registers m1 calleeExp (.ok (fid, m2)) →
      (st.allowLibcallsFor fid && isAllocLibcall fid.ToString) = true →
      AllocLibcallSpec st.dataLayout st.config m2 fid.ToString retTy argVals (.ok (rawRet, m3)) →
      applyRetFMFAndAttrsPure st.dataLayout m3 retTy fmf retAttrs rawRet = .ok finalRet →
      StepInstr st frame callers iid rest (.call retTy fmf calleeExp args retAttrs bundles isNoRet) none
        (finishCallResult st frame callers rest iid retTy finalRet m3)
  | call_alloc_retattr_err {retTy fmf calleeExp args retAttrs bundles isNoRet argVals m1 fid m2 rawRet m3 err} :
      EvalCallArgs st.dataLayout st.config frame.registers st.memory args (.ok (argVals, m1)) →
      EvalCallee st.dataLayout st.config frame.registers m1 calleeExp (.ok (fid, m2)) →
      (st.allowLibcallsFor fid && isAllocLibcall fid.ToString) = true →
      AllocLibcallSpec st.dataLayout st.config m2 fid.ToString retTy argVals (.ok (rawRet, m3)) →
      applyRetFMFAndAttrsPure st.dataLayout m3 retTy fmf retAttrs rawRet = .error err →
      StepInstr st frame callers iid rest (.call retTy fmf calleeExp args retAttrs bundles isNoRet) none (Config.ofError err)
  | call_alloc_err {retTy fmf calleeExp args retAttrs bundles isNoRet argVals m1 fid m2 err} :
      EvalCallArgs st.dataLayout st.config frame.registers st.memory args (.ok (argVals, m1)) →
      EvalCallee st.dataLayout st.config frame.registers m1 calleeExp (.ok (fid, m2)) →
      (st.allowLibcallsFor fid && isAllocLibcall fid.ToString) = true →
      AllocLibcallSpec st.dataLayout st.config m2 fid.ToString retTy argVals (.error err) →
      StepInstr st frame callers iid rest (.call retTy fmf calleeExp args retAttrs bundles isNoRet) none (Config.ofError err)
  | call_intrinsic_ok {retTy fmf calleeExp args retAttrs bundles isNoRet argVals m1 fid m2 rawRet m3 m4 finalRet} :
      EvalCallArgs st.dataLayout st.config frame.registers st.memory args (.ok (argVals, m1)) →
      EvalCallee st.dataLayout st.config frame.registers m1 calleeExp (.ok (fid, m2)) →
      (st.allowLibcallsFor fid && isAllocLibcall fid.ToString) = false →
      (∃ o o', evalNonAllocIntrinsicExec? st.dataLayout st.config m2 fid.ToString retTy fmf argVals o (st.allowLibcallsFor fid) = some (.ok (rawRet, m3, o'))) →
      EvalAssumeBundles st.dataLayout st.config frame.registers m3 (if fid.ToString == "llvm.assume" then bundles else []) (.ok m4) →
      applyRetFMFAndAttrsPure st.dataLayout m4 retTy fmf retAttrs rawRet = .ok finalRet →
      StepInstr st frame callers iid rest (.call retTy fmf calleeExp args retAttrs bundles isNoRet) none
        (finishCallResult st frame callers rest iid retTy finalRet m4)
  | call_intrinsic_bundle_err {retTy fmf calleeExp args retAttrs bundles isNoRet argVals m1 fid m2 rawRet m3 err} :
      EvalCallArgs st.dataLayout st.config frame.registers st.memory args (.ok (argVals, m1)) →
      EvalCallee st.dataLayout st.config frame.registers m1 calleeExp (.ok (fid, m2)) →
      (st.allowLibcallsFor fid && isAllocLibcall fid.ToString) = false →
      (∃ o o', evalNonAllocIntrinsicExec? st.dataLayout st.config m2 fid.ToString retTy fmf argVals o (st.allowLibcallsFor fid) = some (.ok (rawRet, m3, o'))) →
      EvalAssumeBundles st.dataLayout st.config frame.registers m3 (if fid.ToString == "llvm.assume" then bundles else []) (.error err) →
      StepInstr st frame callers iid rest (.call retTy fmf calleeExp args retAttrs bundles isNoRet) none (Config.ofError err)
  | call_intrinsic_retattr_err {retTy fmf calleeExp args retAttrs bundles isNoRet argVals m1 fid m2 rawRet m3 m4 err} :
      EvalCallArgs st.dataLayout st.config frame.registers st.memory args (.ok (argVals, m1)) →
      EvalCallee st.dataLayout st.config frame.registers m1 calleeExp (.ok (fid, m2)) →
      (st.allowLibcallsFor fid && isAllocLibcall fid.ToString) = false →
      (∃ o o', evalNonAllocIntrinsicExec? st.dataLayout st.config m2 fid.ToString retTy fmf argVals o (st.allowLibcallsFor fid) = some (.ok (rawRet, m3, o'))) →
      EvalAssumeBundles st.dataLayout st.config frame.registers m3 (if fid.ToString == "llvm.assume" then bundles else []) (.ok m4) →
      applyRetFMFAndAttrsPure st.dataLayout m4 retTy fmf retAttrs rawRet = .error err →
      StepInstr st frame callers iid rest (.call retTy fmf calleeExp args retAttrs bundles isNoRet) none (Config.ofError err)
  | call_intrinsic_err {retTy fmf calleeExp args retAttrs bundles isNoRet argVals m1 fid m2 err} :
      EvalCallArgs st.dataLayout st.config frame.registers st.memory args (.ok (argVals, m1)) →
      EvalCallee st.dataLayout st.config frame.registers m1 calleeExp (.ok (fid, m2)) →
      (st.allowLibcallsFor fid && isAllocLibcall fid.ToString) = false →
      (∃ o, evalNonAllocIntrinsicExec? st.dataLayout st.config m2 fid.ToString retTy fmf argVals o (st.allowLibcallsFor fid) = some (.error err)) →
      StepInstr st frame callers iid rest (.call retTy fmf calleeExp args retAttrs bundles isNoRet) none (Config.ofError err)
  | call_user_ok {retTy fmf calleeExp args retAttrs bundles isNoRet argVals m1 fid m2 calleeDef calleeFrame m3} :
      EvalCallArgs st.dataLayout st.config frame.registers st.memory args (.ok (argVals, m1)) →
      EvalCallee st.dataLayout st.config frame.registers m1 calleeExp (.ok (fid, m2)) →
      (st.allowLibcallsFor fid && isAllocLibcall fid.ToString) = false →
      (∀ o, evalNonAllocIntrinsicExec? st.dataLayout st.config m2 fid.ToString retTy fmf argVals o (st.allowLibcallsFor fid) = none) →
      st.functions.get? fid = some calleeDef →
      (st.config.maxStackDepth == 0 ∨ st.frames.length < st.config.maxStackDepth) →
      mkCallEntryFrameWithMem st.dataLayout st.config m2 retTy (args.map (fun a => a.2.2)) calleeDef argVals = .ok (calleeFrame, m3) →
      StepInstr st frame callers iid rest (.call retTy fmf calleeExp args retAttrs bundles isNoRet) none
        (.running (st.withFramesAndMemory
          (calleeFrame ::
            (frame.advance rest frame.registers frame.frameAllocas).withReturnDest
              (some { destId := iid, retTy := retTy, fmf := fmf, retAttrs := retAttrs, isNoReturn := isNoRet }) ::
            callers)
          m3))
  | call_user_entry_err {retTy fmf calleeExp args retAttrs bundles isNoRet argVals m1 fid m2 calleeDef err} :
      EvalCallArgs st.dataLayout st.config frame.registers st.memory args (.ok (argVals, m1)) →
      EvalCallee st.dataLayout st.config frame.registers m1 calleeExp (.ok (fid, m2)) →
      (st.allowLibcallsFor fid && isAllocLibcall fid.ToString) = false →
      (∀ o, evalNonAllocIntrinsicExec? st.dataLayout st.config m2 fid.ToString retTy fmf argVals o (st.allowLibcallsFor fid) = none) →
      st.functions.get? fid = some calleeDef →
      (st.config.maxStackDepth == 0 ∨ st.frames.length < st.config.maxStackDepth) →
      mkCallEntryFrameWithMem st.dataLayout st.config m2 retTy (args.map (fun a => a.2.2)) calleeDef argVals = .error err →
      StepInstr st frame callers iid rest (.call retTy fmf calleeExp args retAttrs bundles isNoRet) none (Config.ofError err)
  | call_user_overflow {retTy fmf calleeExp args retAttrs bundles isNoRet argVals m1 fid m2 calleeDef} :
      EvalCallArgs st.dataLayout st.config frame.registers st.memory args (.ok (argVals, m1)) →
      EvalCallee st.dataLayout st.config frame.registers m1 calleeExp (.ok (fid, m2)) →
      (st.allowLibcallsFor fid && isAllocLibcall fid.ToString) = false →
      (∀ o, evalNonAllocIntrinsicExec? st.dataLayout st.config m2 fid.ToString retTy fmf argVals o (st.allowLibcallsFor fid) = none) →
      st.functions.get? fid = some calleeDef →
      st.config.maxStackDepth ≠ 0 →
      st.frames.length ≥ st.config.maxStackDepth →
      StepInstr st frame callers iid rest (.call retTy fmf calleeExp args retAttrs bundles isNoRet) none (.resourceError .stackOverflow)
  | call_external_err {retTy fmf calleeExp args retAttrs bundles isNoRet argVals m1 fid m2 msg} :
      EvalCallArgs st.dataLayout st.config frame.registers st.memory args (.ok (argVals, m1)) →
      EvalCallee st.dataLayout st.config frame.registers m1 calleeExp (.ok (fid, m2)) →
      (st.allowLibcallsFor fid && isAllocLibcall fid.ToString) = false →
      (∀ o, evalNonAllocIntrinsicExec? st.dataLayout st.config m2 fid.ToString retTy fmf argVals o (st.allowLibcallsFor fid) = none) →
      st.functions.get? fid = none →
      StepInstr st frame callers iid rest (.call retTy fmf calleeExp args retAttrs bundles isNoRet) none (.staticError msg)

/-- Relational small-step execution of a block terminator (indexed by `Terminator`). -/
inductive StepTerm (st : MachineState) (frame : CallFrame) (callers : List CallFrame)
    (tid : InstructionId) : Terminator → Config → Prop where
  | retVoid_ok {c'} :
      frame.defn.retType? = some .void →
      StepRet st frame callers .void .void st.memory c' →
      StepTerm st frame callers tid .retVoid c'
  | retVoid_ty_err {msg} :
      frame.defn.retType? ≠ some .void →
      StepTerm st frame callers tid .retVoid (.staticError msg)
  | ret_ok {ty e retVal m1 c'} :
      frame.defn.retType? = some (.ret ty) →
      EvalExp st.dataLayout st.config frame.registers st.memory ty e (.ok (retVal, m1)) →
      StepRet st frame callers (.ret ty) retVal m1 c' →
      StepTerm st frame callers tid (.ret (ty, e)) c'
  | ret_exp_err {ty e err} :
      frame.defn.retType? = some (.ret ty) →
      EvalExp st.dataLayout st.config frame.registers st.memory ty e (.error err) →
      StepTerm st frame callers tid (.ret (ty, e)) (Config.ofError err)
  | ret_ty_err {ty e msg} :
      frame.defn.retType? ≠ some (.ret ty) →
      StepTerm st frame callers tid (.ret (ty, e)) (.staticError msg)
  | br_step {dest c'} :
      StepJump st frame callers st.memory dest c' →
      StepTerm st frame callers tid (.br dest) c'
  | condBr_ok {condExp tDest fDest b m1 c'} :
      EvalExp st.dataLayout st.config frame.registers st.memory .i1 condExp (.ok (.bv 1 (.value b), m1)) →
      StepJump st frame callers m1 (if b != 0 then tDest else fDest) c' →
      StepTerm st frame callers tid (.condBr condExp tDest fDest) c'
  | condBr_poison {condExp tDest fDest m1 msg} :
      EvalExp st.dataLayout st.config frame.registers st.memory .i1 condExp (.ok (.bv 1 .poison, m1)) →
      StepTerm st frame callers tid (.condBr condExp tDest fDest) (.ub msg)
  | condBr_err {condExp tDest fDest err} :
      EvalExp st.dataLayout st.config frame.registers st.memory .i1 condExp (.error err) →
      StepTerm st frame callers tid (.condBr condExp tDest fDest) (Config.ofError err)
  | condBr_nonbool {condExp tDest fDest v m1 msg} :
      EvalExp st.dataLayout st.config frame.registers st.memory .i1 condExp (.ok (v, m1)) →
      (∀ iv, v ≠ .bv 1 iv) →
      StepTerm st frame callers tid (.condBr condExp tDest fDest) (.staticError msg)
  | switch_ok {ty condExp defDest cases w bv m1 c'} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty condExp (.ok (.bv w (.value bv), m1)) →
      StepJump st frame callers m1
        (match cases.find? (fun (cv, _) => BitVec.ofInt w cv == bv) with
         | some (_, lbl) => lbl
         | none => defDest) c' →
      StepTerm st frame callers tid (.switch ty condExp defDest cases) c'
  | switch_poison {ty condExp defDest cases w m1 msg} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty condExp (.ok (.bv w .poison, m1)) →
      StepTerm st frame callers tid (.switch ty condExp defDest cases) (.ub msg)
  | switch_err {ty condExp defDest cases err} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty condExp (.error err) →
      StepTerm st frame callers tid (.switch ty condExp defDest cases) (Config.ofError err)
  | switch_nonint {ty condExp defDest cases v m1 msg} :
      EvalExp st.dataLayout st.config frame.registers st.memory ty condExp (.ok (v, m1)) →
      (∀ w iv, v ≠ .bv w iv) →
      StepTerm st frame callers tid (.switch ty condExp defDest cases) (.staticError msg)
  | indirectBr_ok {addrExp dests as p m1 dest c'} :
      EvalExp st.dataLayout st.config frame.registers st.memory (.ptr st.dataLayout.programAddrSpace) addrExp (.ok (.ptr as (.value p), m1)) →
      m1.addrToFunc.get? p.addr.toNat = some (blockAddrKey frame.defn.prototype.name dest) →
      dest ∈ dests →
      StepJump st frame callers m1 dest c' →
      StepTerm st frame callers tid (.indirectBr addrExp dests) c'
  | indirectBr_poison {addrExp dests as m1 msg} :
      EvalExp st.dataLayout st.config frame.registers st.memory (.ptr st.dataLayout.programAddrSpace) addrExp (.ok (.ptr as .poison, m1)) →
      StepTerm st frame callers tid (.indirectBr addrExp dests) (.ub msg)
  | indirectBr_invalid {addrExp dests as p m1 msg} :
      EvalExp st.dataLayout st.config frame.registers st.memory (.ptr st.dataLayout.programAddrSpace) addrExp (.ok (.ptr as (.value p), m1)) →
      (∀ dest ∈ dests, m1.addrToFunc.get? p.addr.toNat ≠ some (blockAddrKey frame.defn.prototype.name dest)) →
      StepTerm st frame callers tid (.indirectBr addrExp dests) (.ub msg)
  | indirectBr_err {addrExp dests err} :
      EvalExp st.dataLayout st.config frame.registers st.memory (.ptr st.dataLayout.programAddrSpace) addrExp (.error err) →
      StepTerm st frame callers tid (.indirectBr addrExp dests) (Config.ofError err)
  | indirectBr_nonptr {addrExp dests v m1 msg} :
      EvalExp st.dataLayout st.config frame.registers st.memory (.ptr st.dataLayout.programAddrSpace) addrExp (.ok (v, m1)) →
      (∀ as pv, v ≠ .ptr as pv) →
      StepTerm st frame callers tid (.indirectBr addrExp dests) (.staticError msg)
  | unreachable_ub {msg} :
      StepTerm st frame callers tid .unreachable (.ub msg)

/-! ### Primary Small-Step Relation (`Step`) -/

/--
Primary inductive small-step operational semantics of LLVM IR (`Step c ev c'`).
Cleanly delegates to `StepInstr` (when the current frame has remaining instructions) and
`StepTerm` (when the current frame reaches its block terminator).
-/
inductive Step : Config → Option TraceEvent → Config → Prop where
  | empty_stack {st msg} :
      st.frames = [] →
      Step (.running st) none (.staticError msg)
  | instr {st frame callers iid instr rest ev c'} :
      st.frames = frame :: callers →
      frame.remainingCode = (iid, instr) :: rest →
      StepInstr st frame callers iid rest instr ev c' →
      Step (.running st) ev c'
  | term {st frame callers tid term c'} :
      st.frames = frame :: callers →
      frame.remainingCode = [] →
      frame.terminator = (tid, term) →
      StepTerm st frame callers tid term c' →
      Step (.running st) none c'

/-! ### Multi-Step Execution, Behaviors, and Well-Formedness Preservation -/

/-- Reflexive-transitive closure of `Step`, accumulating emitted `TraceEvent`s in order. -/
inductive StarStep : Config → List TraceEvent → Config → Prop where
  | refl (c : Config) : StarStep c [] c
  | step {c1 c2 c3 : Config} {ev : Option TraceEvent} {tr : List TraceEvent} :
      Step c1 ev c2 → StarStep c2 tr c3 → StarStep c1 (ev.toList ++ tr) c3

theorem StarStep.single {c1 c2 : Config} {ev : Option TraceEvent}
    (h : Step c1 ev c2) : StarStep c1 ev.toList c2 := by
  simpa using StarStep.step h (StarStep.refl c2)

theorem StarStep.trans {c1 c2 c3 : Config} {tr1 tr2 : List TraceEvent}
    (h1 : StarStep c1 tr1 c2) (h2 : StarStep c2 tr2 c3) :
    StarStep c1 (tr1 ++ tr2) c3 := by
  induction h1 with
  | refl _ => exact h2
  | step hs _ ih =>
    rw [List.append_assoc]
    exact StarStep.step hs (ih h2)

/-- Transitive (one-or-more-step) closure of `Step`. -/
def PlusStep (c1 : Config) (tr : List TraceEvent) (c2 : Config) : Prop :=
  ∃ ev cm tr', Step c1 ev cm ∧ StarStep cm tr' c2 ∧ tr = ev.toList ++ tr'

theorem PlusStep.single {c1 c2 : Config} {ev : Option TraceEvent}
    (h : Step c1 ev c2) : PlusStep c1 ev.toList c2 :=
  ⟨ev, c2, [], h, StarStep.refl c2, by simp⟩

theorem StarStep.of_plusStep {c1 c2 : Config} {tr : List TraceEvent}
    (h : PlusStep c1 tr c2) : StarStep c1 tr c2 := by
  obtain ⟨ev, cm, tr', hs, hstar, rfl⟩ := h
  exact StarStep.step hs hstar

/-- Configuration well-formedness: any running or halted memory is `MemoryState.WellFormed`. -/
@[simp]
def Config.WellFormed : Config → Prop
  | .running st => MemoryState.WellFormed st.memory
  | .halted _ mem => MemoryState.WellFormed mem
  | _ => True

private theorem finishRegInstr_wf {st frame callers rest iid val mem' allocas'}
    (hwf : MemoryState.WellFormed mem') :
    Config.WellFormed (finishRegInstr st frame callers rest iid val mem' allocas') := by
  cases iid with
  | id _ => exact hwf
  | void _ => trivial

private theorem finishCallResult_wf {st frame callers rest iid retTy val mem'}
    (hwf : MemoryState.WellFormed mem') :
    Config.WellFormed (finishCallResult st frame callers rest iid retTy val mem') := hwf

private theorem configOfError_wf (e : ExecError) : Config.WellFormed (Config.ofError e) := by
  cases e <;> trivial

private theorem stepJump_wf {st frame callers mem dest c'}
    (hwf : MemoryState.WellFormed mem) (h : StepJump st frame callers mem dest c') :
    Config.WellFormed c' := by
  cases h with
  | ok _ _ hp => exact EvalPhis.preserves_wf hwf hp
  | phi_err _ _ _ => exact configOfError_wf _
  | missing_block _ => trivial

private theorem stepRet_wf {st frame callers retTy retVal m1 c'}
    (hwf : MemoryState.WellFormed m1) (h : StepRet st frame callers retTy retVal m1 c') :
    Config.WellFormed c' := by
  cases h with
  | top_ok _ _ => exact freeAllocaList_preserves_wf hwf _
  | call_ok _ _ _ _ _ => exact freeAllocaList_preserves_wf hwf _
  | noreturn_ub _ _ _ _ => trivial
  | callee_attr_err _ => exact configOfError_wf _
  | caller_attr_err _ _ _ _ _ => exact configOfError_wf _
  | missing_dest _ _ _ => trivial

theorem StepInstr.preserves_wf {st frame callers iid rest instr ev c'}
    (hwf : MemoryState.WellFormed st.memory)
    (h : StepInstr st frame callers iid rest instr ev c') :
    Config.WellFormed c' := by
  cases h with
  | intBinaryOp_ok h1 h2 _ => exact finishRegInstr_wf (EvalExp.preserves_wf (EvalExp.preserves_wf hwf h1) h2)
  | floatUnaryOp_ok h1 _ => exact finishRegInstr_wf (EvalExp.preserves_wf hwf h1)
  | floatBinaryOp_ok h1 h2 _ => exact finishRegInstr_wf (EvalExp.preserves_wf (EvalExp.preserves_wf hwf h1) h2)
  | icmp_ok h1 h2 _ => exact finishRegInstr_wf (EvalExp.preserves_wf (EvalExp.preserves_wf hwf h1) h2)
  | fcmp_ok h1 h2 _ => exact finishRegInstr_wf (EvalExp.preserves_wf (EvalExp.preserves_wf hwf h1) h2)
  | conversionOp_ok h1 hc =>
    obtain ⟨o, o', hev⟩ := hc
    exact finishRegInstr_wf (evalConversionExec_preserves_wf (EvalExp.preserves_wf hwf h1) hev)
  | select_ok h1 h2 h3 _ _ =>
    exact finishRegInstr_wf (EvalExp.preserves_wf (EvalExp.preserves_wf (EvalExp.preserves_wf hwf h1) h2) h3)
  | alloca_ok hcnt hspec =>
    rename_i allocTy numEl? align? addrSpace count m1 obj mem'
    have hm1 : MemoryState.WellFormed m1 := by
      cases numEl? with
      | none => rw [hcnt.2]; exact hwf
      | some p => obtain ⟨_, _, he, _⟩ := hcnt; exact EvalExp.preserves_wf hwf he
    exact finishRegInstr_wf (hspec.preserves_wf hm1)
  | load_ok h1 _ _ _ _ => exact finishRegInstr_wf (EvalExp.preserves_wf hwf h1)
  | store_ok h1 h2 _ =>
    exact MemoryState.writeObjectBytes_preserves_wf (EvalExp.preserves_wf (EvalExp.preserves_wf hwf h1) h2) _ _ _
  | gep_ok h1 h2 _ => exact finishRegInstr_wf (EvalExpList.preserves_wf (EvalExp.preserves_wf hwf h1) h2)
  | extractvalue_ok h1 _ => exact finishRegInstr_wf (EvalExp.preserves_wf hwf h1)
  | insertvalue_ok h1 h2 _ => exact finishRegInstr_wf (EvalExp.preserves_wf (EvalExp.preserves_wf hwf h1) h2)
  | extractelement_ok h1 h2 _ => exact finishRegInstr_wf (EvalExp.preserves_wf (EvalExp.preserves_wf hwf h1) h2)
  | insertelement_ok h1 h2 h3 _ =>
    exact finishRegInstr_wf (EvalExp.preserves_wf (EvalExp.preserves_wf (EvalExp.preserves_wf hwf h1) h2) h3)
  | shufflevector_ok h1 h2 _ => exact finishRegInstr_wf (EvalExp.preserves_wf (EvalExp.preserves_wf hwf h1) h2)
  | freeze_ok h1 _ => exact finishRegInstr_wf (EvalExp.preserves_wf hwf h1)
  | bitinsert_ok h1 h2 h3 _ =>
    exact finishRegInstr_wf (EvalExp.preserves_wf (EvalExp.preserves_wf (EvalExp.preserves_wf hwf h1) h2) h3)
  | bitextract_ok h1 h2 _ =>
    exact finishRegInstr_wf (EvalExp.preserves_wf (EvalExp.preserves_wf hwf h1) h2)
  | call_alloc_ok ha hc _ hspec _ =>
    exact finishCallResult_wf (AllocLibcallSpec.preserves_wf (EvalCallee.preserves_wf (EvalCallArgs.preserves_wf hwf ha) hc) hspec)
  | call_intrinsic_ok ha hc _ hint hb _ =>
    obtain ⟨o, o', hev⟩ := hint
    exact finishCallResult_wf (EvalAssumeBundles.preserves_wf (evalNonAllocIntrinsicExec?_preserves_wf (EvalCallee.preserves_wf (EvalCallArgs.preserves_wf hwf ha) hc) hev) hb)
  | call_user_ok ha hc _ _ _ _ hmk =>
    exact mkCallEntryFrameWithMem_preserves_wf (EvalCallee.preserves_wf (EvalCallArgs.preserves_wf hwf ha) hc) hmk
  | _ => first | exact configOfError_wf _ | trivial

theorem StepTerm.preserves_wf {st frame callers tid term c'}
    (hwf : MemoryState.WellFormed st.memory)
    (h : StepTerm st frame callers tid term c') :
    Config.WellFormed c' := by
  cases h with
  | retVoid_ok _ hr => exact stepRet_wf hwf hr
  | ret_ok _ he hr => exact stepRet_wf (EvalExp.preserves_wf hwf he) hr
  | br_step hj => exact stepJump_wf hwf hj
  | condBr_ok he hj => exact stepJump_wf (EvalExp.preserves_wf hwf he) hj
  | switch_ok he hj => exact stepJump_wf (EvalExp.preserves_wf hwf he) hj
  | indirectBr_ok he _ _ hj => exact stepJump_wf (EvalExp.preserves_wf hwf he) hj
  | _ => first | exact configOfError_wf _ | trivial

/-- Every small-step transition preserves `Config.WellFormed` (`MemoryState.WellFormed`). -/
theorem Step.preserves_wf {c ev c'} (hwf : Config.WellFormed c) (h : Step c ev c') :
    Config.WellFormed c' := by
  cases h with
  | empty_stack _ => trivial
  | instr _ _ hi => exact StepInstr.preserves_wf hwf hi
  | term _ _ _ ht => exact StepTerm.preserves_wf hwf ht

theorem StarStep.preserves_wf {c tr c'} (hwf : Config.WellFormed c) (h : StarStep c tr c') :
    Config.WellFormed c' := by
  induction h with
  | refl _ => exact hwf
  | step hs _ ih => exact ih (Step.preserves_wf hwf hs)

/-! ### Observable Program Behaviors (Termination, UB, Resource Abort, Divergence) -/

/-- Immediate Undefined Behavior is reachable along some execution path from `c`. -/
def CanUB (c : Config) : Prop :=
  ∃ tr msg, StarStep c tr (.ub msg)

/-- A resource exhaustion error (OOM on `alloca` or call stack overflow) is reachable from `c`. -/
def CanResourceError (c : Config) : Prop :=
  ∃ tr err, StarStep c tr (.resourceError err)

/-- A static (malformed IR) error is reachable from `c`. -/
def CanStaticError (c : Config) : Prop :=
  ∃ tr msg, StarStep c tr (.staticError msg)

/-- `CanAbort c`: execution can trigger Immediate UB or stack/alloca resource exhaustion. -/
def CanAbort (c : Config) : Prop :=
  CanUB c ∨ CanResourceError c

/-- `Terminates c tr retVal finalMem`: `c` halts normally emitting `tr`, returning `retVal`, ending in `finalMem`. -/
def Terminates (c : Config) (tr : List TraceEvent) (retVal : RegisterValue) (finalMem : MemoryState) : Prop :=
  StarStep c tr (.halted retVal finalMem)

/-- `Diverges c`: there exists an infinite small-step execution starting from `c`. -/
def Diverges (c : Config) : Prop :=
  ∃ (f : Nat → Config) (ev : Nat → Option TraceEvent),
    f 0 = c ∧ ∀ n, Step (f n) (ev n) (f (n + 1))

/-! ### Terminal Configuration & Deterministic-Step Inversion Lemmas -/

theorem Step.not_halted {v mem ev c'} : ¬ Step (.halted v mem) ev c' := by intro h; cases h
theorem Step.not_ub {msg ev c'} : ¬ Step (.ub msg) ev c' := by intro h; cases h
theorem Step.not_staticError {msg ev c'} : ¬ Step (.staticError msg) ev c' := by intro h; cases h
theorem Step.not_resourceError {err ev c'} : ¬ Step (.resourceError err) ev c' := by intro h; cases h

theorem StarStep.halted_inv {v mem tr c'} (h : StarStep (.halted v mem) tr c') :
    tr = [] ∧ c' = .halted v mem := by
  cases h with
  | refl _ => exact ⟨rfl, rfl⟩
  | step hs _ => exact False.elim (Step.not_halted hs)

theorem StarStep.ub_inv {msg tr c'} (h : StarStep (.ub msg) tr c') :
    tr = [] ∧ c' = .ub msg := by
  cases h with
  | refl _ => exact ⟨rfl, rfl⟩
  | step hs _ => exact False.elim (Step.not_ub hs)

theorem StarStep.staticError_inv {msg tr c'} (h : StarStep (.staticError msg) tr c') :
    tr = [] ∧ c' = .staticError msg := by
  cases h with
  | refl _ => exact ⟨rfl, rfl⟩
  | step hs _ => exact False.elim (Step.not_staticError hs)

theorem StarStep.resourceError_inv {err tr c'} (h : StarStep (.resourceError err) tr c') :
    tr = [] ∧ c' = .resourceError err := by
  cases h with
  | refl _ => exact ⟨rfl, rfl⟩
  | step hs _ => exact False.elim (Step.not_resourceError hs)

theorem not_canUB_halted {v mem} : ¬ CanUB (.halted v mem) := by
  rintro ⟨tr, msg, h⟩; obtain ⟨_, heq⟩ := StarStep.halted_inv h; cases heq

theorem not_canResourceError_halted {v mem} : ¬ CanResourceError (.halted v mem) := by
  rintro ⟨tr, err, h⟩; obtain ⟨_, heq⟩ := StarStep.halted_inv h; cases heq

theorem not_canAbort_halted {v mem} : ¬ CanAbort (.halted v mem) := by
  rintro (h | h)
  · exact not_canUB_halted h
  · exact not_canResourceError_halted h

theorem not_diverges_halted {v mem} : ¬ Diverges (.halted v mem) := by
  rintro ⟨f, ev, h0, hstep⟩; have h1 := hstep 0; rw [h0] at h1; exact Step.not_halted h1

theorem not_diverges_ub {msg} : ¬ Diverges (.ub msg) := by
  rintro ⟨f, ev, h0, hstep⟩; have h1 := hstep 0; rw [h0] at h1; exact Step.not_ub h1

theorem not_diverges_staticError {msg} : ¬ Diverges (.staticError msg) := by
  rintro ⟨f, ev, h0, hstep⟩; have h1 := hstep 0; rw [h0] at h1; exact Step.not_staticError h1

theorem not_diverges_resourceError {err} : ¬ Diverges (.resourceError err) := by
  rintro ⟨f, ev, h0, hstep⟩; have h1 := hstep 0; rw [h0] at h1; exact Step.not_resourceError h1

theorem Diverges.of_step {c ev c'} (hs : Step c ev c') (hd : Diverges c') : Diverges c := by
  obtain ⟨f, evf, h0, hstep⟩ := hd
  refine ⟨fun n => match n with | 0 => c | k + 1 => f k,
          fun n => match n with | 0 => ev | k + 1 => evf k, rfl, ?_⟩
  intro n
  cases n with
  | zero => simpa [h0] using hs
  | succ k => exact hstep k

theorem Diverges.step_inv {c} (hd : Diverges c) : ∃ ev c', Step c ev c' ∧ Diverges c' := by
  obtain ⟨f, evf, h0, hstep⟩ := hd
  have hs0 : Step c (evf 0) (f 1) := h0 ▸ hstep 0
  exact ⟨evf 0, f 1, hs0, ⟨fun n => f (n + 1), fun n => evf (n + 1), rfl, fun n => hstep (n + 1)⟩⟩

theorem CanAbort.of_starStep {c1 tr c2} (hstar : StarStep c1 tr c2) (ha : CanAbort c2) :
    CanAbort c1 := by
  rcases ha with ⟨tr', msg, h⟩ | ⟨tr', err, h⟩
  · exact Or.inl ⟨tr ++ tr', msg, StarStep.trans hstar h⟩
  · exact Or.inr ⟨tr ++ tr', err, StarStep.trans hstar h⟩

/-- Coinductive construction of `Diverges` from a single-step progress invariant. -/
theorem Diverges.of_progress {P : Config → Prop}
    (hprog : ∀ c, P c → ∃ ev c', Step c ev c' ∧ P c')
    {c0 : Config} (h0 : P c0) : Diverges c0 := by
  let stepEv : ∀ s : { c : Config // P c }, Option TraceEvent :=
    fun s => Classical.choose (hprog s.1 s.2)
  let stepNext : ∀ s : { c : Config // P c }, { c : Config // P c } :=
    fun s =>
      let h1 := Classical.choose_spec (hprog s.1 s.2)
      ⟨Classical.choose h1, (Classical.choose_spec h1).2⟩
  let stepProof : ∀ s : { c : Config // P c }, Step s.1 (stepEv s) (stepNext s).1 :=
    fun s =>
      let h1 := Classical.choose_spec (hprog s.1 s.2)
      (Classical.choose_spec h1).1
  let seq : Nat → { c : Config // P c } :=
    Nat.rec ⟨c0, h0⟩ (fun _ prev => stepNext prev)
  exact ⟨fun n => (seq n).1, fun n => stepEv (seq n), rfl, fun n => stepProof (seq n)⟩

/-- Coinductive construction of `Diverges` from a `PlusStep` (≥ 1 step) progress invariant. -/
theorem Diverges.of_plusStep_progress {P : Config → Prop}
    (hprog : ∀ c, P c → ∃ tr c', PlusStep c tr c' ∧ P c')
    {c0 : Config} (h0 : P c0) : Diverges c0 := by
  let Q : Config → Prop := fun c => ∃ tr cEnd, StarStep c tr cEnd ∧ P cEnd
  refine Diverges.of_progress (P := Q) ?_ ⟨[], c0, StarStep.refl c0, h0⟩
  rintro c ⟨tr, cEnd, hstar, hp⟩
  cases hstar with
  | refl _ =>
    obtain ⟨tr', cEnd', ⟨ev, cm, tr2, hs, hrest, _⟩, hp'⟩ := hprog c hp
    exact ⟨ev, cm, hs, tr2, cEnd', hrest, hp'⟩
  | step hs hrest =>
    exact ⟨_, _, hs, _, cEnd, hrest, hp⟩

theorem StarStep.of_det_step {st : MachineState} {ev0 : Option TraceEvent} {c1 : Config}
    (hdet : ∀ ev c', Step (.running st) ev c' ↔ ev = ev0 ∧ c' = c1)
    {tr : List TraceEvent} {v : RegisterValue} {m : MemoryState} :
    StarStep (.running st) tr (.halted v m) ↔
      ∃ tr', tr = ev0.toList ++ tr' ∧ StarStep c1 tr' (.halted v m) := by
  constructor
  · intro h
    cases h with
    | step hs hrest =>
      obtain ⟨rfl, rfl⟩ := (hdet _ _).mp hs
      exact ⟨_, rfl, hrest⟩
  · rintro ⟨tr', rfl, hrest⟩
    exact StarStep.step ((hdet ev0 c1).mpr ⟨rfl, rfl⟩) hrest

theorem CanUB.of_det_step {st : MachineState} {ev0 : Option TraceEvent} {c1 : Config}
    (hdet : ∀ ev c', Step (.running st) ev c' ↔ ev = ev0 ∧ c' = c1) :
    CanUB (.running st) ↔ CanUB c1 := by
  constructor
  · rintro ⟨tr, msg, h⟩
    cases h with
    | step hs hrest => obtain ⟨rfl, rfl⟩ := (hdet _ _).mp hs; exact ⟨_, msg, hrest⟩
  · rintro ⟨tr, msg, h⟩
    exact ⟨ev0.toList ++ tr, msg, StarStep.step ((hdet ev0 c1).mpr ⟨rfl, rfl⟩) h⟩

theorem CanResourceError.of_det_step {st : MachineState} {ev0 : Option TraceEvent} {c1 : Config}
    (hdet : ∀ ev c', Step (.running st) ev c' ↔ ev = ev0 ∧ c' = c1) :
    CanResourceError (.running st) ↔ CanResourceError c1 := by
  constructor
  · rintro ⟨tr, err, h⟩
    cases h with
    | step hs hrest => obtain ⟨rfl, rfl⟩ := (hdet _ _).mp hs; exact ⟨_, err, hrest⟩
  · rintro ⟨tr, err, h⟩
    exact ⟨ev0.toList ++ tr, err, StarStep.step ((hdet ev0 c1).mpr ⟨rfl, rfl⟩) h⟩

theorem CanAbort.of_det_step {st : MachineState} {ev0 : Option TraceEvent} {c1 : Config}
    (hdet : ∀ ev c', Step (.running st) ev c' ↔ ev = ev0 ∧ c' = c1) :
    CanAbort (.running st) ↔ CanAbort c1 := by
  simp only [CanAbort, CanUB.of_det_step hdet, CanResourceError.of_det_step hdet]

theorem Diverges.of_det_step {st : MachineState} {ev0 : Option TraceEvent} {c1 : Config}
    (hdet : ∀ ev c', Step (.running st) ev c' ↔ ev = ev0 ∧ c' = c1) :
    Diverges (.running st) ↔ Diverges c1 := by
  constructor
  · intro hd
    obtain ⟨ev, c', hs, hd'⟩ := Diverges.step_inv hd
    obtain ⟨rfl, rfl⟩ := (hdet _ _).mp hs
    exact hd'
  · intro hd
    exact Diverges.of_step ((hdet ev0 c1).mpr ⟨rfl, rfl⟩) hd

/-! ### Fast Indexed Inversion Lemmas (O(1) per opcode!) -/

theorem Step.instr_iff {st frame callers iid instr rest ev c'}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = (iid, instr) :: rest) :
    Step (.running st) ev c' ↔ StepInstr st frame callers iid rest instr ev c' := by
  constructor
  · intro hs
    cases hs with
    | empty_stack he => rw [hf] at he; cases he
    | instr hf' hc' hi => rw [hf] at hf'; cases hf'; rw [hc] at hc'; cases hc'; exact hi
    | term hf' hc' _ _ => rw [hf] at hf'; cases hf'; rw [hc] at hc'; cases hc'
  · exact Step.instr hf hc

theorem Step.term_iff {st frame callers tid term ev c'}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = [])
    (ht : frame.terminator = (tid, term)) :
    Step (.running st) ev c' ↔ ev = none ∧ StepTerm st frame callers tid term c' := by
  constructor
  · intro hs
    cases hs with
    | empty_stack he => rw [hf] at he; cases he
    | instr hf' hc' _ => rw [hf] at hf'; cases hf'; rw [hc] at hc'; cases hc'
    | term hf' hc' ht' hst =>
      rw [hf] at hf'; cases hf'; rw [ht] at ht'; cases ht'
      exact ⟨rfl, hst⟩
  · rintro ⟨rfl, hst⟩
    exact Step.term hf hc ht hst

theorem EvalExp.leaf_iff {dl cfg regs mem ty e v}
    (h : evalPureLeafExp? dl cfg regs mem ty e = some (.ok v))
    (res : Except ExecError (RegisterValue × MemoryState)) :
    EvalExp dl cfg regs mem ty e res ↔ res = .ok (v, mem) := by
  constructor
  · intro he
    cases he with
    | leaf_ok h' => rw [h] at h'; cases h'; rfl
    | leaf_err h' => rw [h] at h'; cases h'
    | _ => simp [evalPureLeafExp?] at h
  · rintro rfl; exact EvalExp.leaf_ok h

theorem EvalExp.undef_iff {dl cfg regs mem ty} (hallow : cfg.allowUndef = true)
    (hnoFn : ty.hasFunction = false)
    (res : Except ExecError (RegisterValue × MemoryState)) :
    EvalExp dl cfg regs mem ty .undef res ↔ ∃ v, res = .ok (v, mem) ∧ UndefValRel dl cfg ty v := by
  constructor
  · intro he
    cases he with
    | leaf_ok h' => simp [evalPureLeafExp?] at h'
    | leaf_err h' => simp [evalPureLeafExp?] at h'
    | undef_ok _ hu => exact ⟨_, rfl, hu⟩
    | undef_err hbad =>
      rcases hbad with hd | hfn
      · simp [SemanticsConfig.allowUndef, hd] at hallow
      · rw [hnoFn] at hfn; cases hfn
  · rintro ⟨v, rfl, hu⟩
    exact EvalExp.undef_ok hallow hu

/-- Deterministic inversion for `intBinaryOp` with pure leaf operands. -/
theorem Step.intBinaryOp_leaf_iff {st frame callers iid op ty e1 e2 rest v1 v2}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = (iid, .intBinaryOp op ty e1 e2) :: rest)
    (h1 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty e1 = some (.ok v1))
    (h2 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty e2 = some (.ok v2))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔
      ev = none ∧
      c' = match liftBinaryPure ty.scalarType v1 v2 (evalIntBinaryScalarPure op) with
           | .ok res => finishRegInstr st frame callers rest iid res st.memory
           | .error err => Config.ofError err := by
  rw [Step.instr_iff hf hc]
  constructor
  · intro hi
    cases hi with
    | intBinaryOp_ok he1 he2 hbin =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
      rw [hbin]; exact ⟨rfl, rfl⟩
    | intBinaryOp_e1_err he1 => have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
    | intBinaryOp_e2_err he1 he2 =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
    | intBinaryOp_eval_err he1 he2 hbin =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
      rw [hbin]; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    cases hbin : liftBinaryPure ty.scalarType v1 v2 (evalIntBinaryScalarPure op) with
    | ok res => exact StepInstr.intBinaryOp_ok (EvalExp.leaf_ok h1) (EvalExp.leaf_ok h2) hbin
    | error err => exact StepInstr.intBinaryOp_eval_err (EvalExp.leaf_ok h1) (EvalExp.leaf_ok h2) hbin

/-- Deterministic inversion for `icmp` with pure leaf operands. -/
theorem Step.icmp_leaf_iff {st frame callers iid ss pred ty e1 e2 rest v1 v2}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = (iid, .icmp ss pred ty e1 e2) :: rest)
    (h1 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty e1 = some (.ok v1))
    (h2 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty e2 = some (.ok v2))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔
      ev = none ∧
      c' = match liftBinaryPure .i1 v1 v2 (evalICmpScalarPure st.dataLayout ss pred) with
           | .ok res => finishRegInstr st frame callers rest iid res st.memory
           | .error err => Config.ofError err := by
  rw [Step.instr_iff hf hc]
  constructor
  · intro hi
    cases hi with
    | icmp_ok he1 he2 hcmp =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
      rw [hcmp]; exact ⟨rfl, rfl⟩
    | icmp_e1_err he1 => have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
    | icmp_e2_err he1 he2 =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
    | icmp_eval_err he1 he2 hcmp =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
      rw [hcmp]; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    cases hcmp : liftBinaryPure .i1 v1 v2 (evalICmpScalarPure st.dataLayout ss pred) with
    | ok res => exact StepInstr.icmp_ok (EvalExp.leaf_ok h1) (EvalExp.leaf_ok h2) hcmp
    | error err => exact StepInstr.icmp_eval_err (EvalExp.leaf_ok h1) (EvalExp.leaf_ok h2) hcmp

/-- Deterministic inversion for `select` (no FMF) with pure leaf operands. -/
theorem Step.select_leaf_iff {st frame callers iid condTy cond valTy tv fv rest cV tV fV}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = (iid, .select {} condTy cond valTy tv fv) :: rest)
    (h1 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory condTy cond = some (.ok cV))
    (h2 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory valTy tv = some (.ok tV))
    (h3 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory valTy fv = some (.ok fV))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔
      ev = none ∧
      c' = match evalSelectPure cV tV fV with
           | .ok res => finishRegInstr st frame callers rest iid res st.memory
           | .error err => Config.ofError err := by
  rw [Step.instr_iff hf hc]
  constructor
  · intro hi
    cases hi with
    | select_ok he1 he2 he3 hsel hfmf =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
      have hv3 := (EvalExp.leaf_iff h3 _).mp he3; cases hv3
      obtain ⟨o, o', hfo⟩ := hfmf
      simp only [applyInputFMFExec_none, Except.ok.injEq, Prod.mk.injEq] at hfo
      obtain ⟨rfl, _⟩ := hfo
      rw [hsel]; exact ⟨rfl, rfl⟩
    | select_cond_err he1 => have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
    | select_tv_err he1 he2 =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
    | select_fv_err he1 he2 he3 =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
      have hv3 := (EvalExp.leaf_iff h3 _).mp he3; cases hv3
    | select_eval_err he1 he2 he3 hsel =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
      have hv3 := (EvalExp.leaf_iff h3 _).mp he3; cases hv3
      rw [hsel]; exact ⟨rfl, rfl⟩
    | select_fmf_err _ _ _ _ hfmf =>
      obtain ⟨o, hfo⟩ := hfmf; simp [applyInputFMFExec_none] at hfo
  · rintro ⟨rfl, rfl⟩
    cases hsel : evalSelectPure cV tV fV with
    | ok res =>
      exact StepInstr.select_ok (EvalExp.leaf_ok h1) (EvalExp.leaf_ok h2) (EvalExp.leaf_ok h3) hsel
        ⟨default, default, rfl⟩
    | error err =>
      exact StepInstr.select_eval_err (EvalExp.leaf_ok h1) (EvalExp.leaf_ok h2) (EvalExp.leaf_ok h3) hsel

/-- Deterministic inversion for `store` with pure leaf operands and concrete pointer. -/
theorem Step.store_leaf_iff {st frame callers iid valTy valExp ptrTy ptrExp align? isVol rest val as p}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = (iid, .store valTy valExp ptrTy ptrExp align? isVol) :: rest)
    (h1 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory valTy valExp = some (.ok val))
    (h2 : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ptrTy ptrExp = some (.ok (.ptr as (.value p))))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔
      match st.memory.verifyMemAccess p (st.dataLayout.typeStoreSize valTy)
              (align?.getD (st.dataLayout.typeABIAlign valTy)) true with
      | .ok (mo, offset) =>
        ev = (if isVol then some (.volatileStore mo.addrSpace p.addr.toNat
                (valueToBytes st.dataLayout st.config val valTy)) else none) ∧
        c' = finishVoidInstr st frame callers rest
               (st.memory.writeObjectBytes mo.allocId offset (valueToBytes st.dataLayout st.config val valTy))
      | .error err =>
        ev = none ∧ c' = Config.ofError err := by
  rw [Step.instr_iff hf hc]
  constructor
  · intro hi
    cases hi with
    | store_ok he1 he2 hver =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
      rw [hver]; exact ⟨rfl, rfl⟩
    | store_val_err he1 => have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
    | store_ptr_err he1 he2 =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
    | store_ptr_poison he1 he2 =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
    | store_ptr_nonptr he1 he2 hnp =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
      exact False.elim (hnp _ _ rfl)
    | store_mem_err he1 he2 hver =>
      have hv1 := (EvalExp.leaf_iff h1 _).mp he1; cases hv1
      have hv2 := (EvalExp.leaf_iff h2 _).mp he2; cases hv2
      rw [hver]; exact ⟨rfl, rfl⟩
  · intro hrhs
    cases hver : st.memory.verifyMemAccess p (st.dataLayout.typeStoreSize valTy)
        (align?.getD (st.dataLayout.typeABIAlign valTy)) true with
    | ok pair =>
      rw [hver] at hrhs; obtain ⟨rfl, rfl⟩ := hrhs
      exact StepInstr.store_ok (EvalExp.leaf_ok h1) (EvalExp.leaf_ok h2) hver
    | error err =>
      rw [hver] at hrhs; obtain ⟨rfl, rfl⟩ := hrhs
      exact StepInstr.store_mem_err (EvalExp.leaf_ok h1) (EvalExp.leaf_ok h2) hver

/-- Deterministic inversion for top-level `ret ty e` with a pure leaf operand. -/
theorem Step.ret_top_leaf_iff {st frame tid ty e v}
    (hf : st.frames = [frame])
    (hc : frame.remainingCode = [])
    (hretTy : frame.defn.retType? = some (.ret ty))
    (hterm : frame.terminator = (tid, .ret (ty, e)))
    (he : evalPureLeafExp? st.dataLayout st.config frame.registers st.memory ty e = some (.ok v))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔
      ev = none ∧
      c' = match applyRetFMFAndAttrsPure st.dataLayout (freeAllocaList st.memory frame.frameAllocas)
                   (.ret ty) {} frame.defn.prototype.retAttrs v with
           | .ok v' => .halted v' (freeAllocaList st.memory frame.frameAllocas)
           | .error err => Config.ofError err := by
  rw [Step.term_iff hf hc hterm]
  constructor
  · rintro ⟨rfl, ht⟩
    cases ht with
    | ret_ok _ he' hr =>
      have hv := (EvalExp.leaf_iff he _).mp he'; cases hv
      cases hr with
      | top_ok _ hattr => rw [hattr]; exact ⟨rfl, rfl⟩
      | call_ok hne _ _ _ _ => cases hne
      | noreturn_ub hne _ _ _ => cases hne
      | callee_attr_err hattr => rw [hattr]; exact ⟨rfl, rfl⟩
      | caller_attr_err hne _ _ _ _ => cases hne
      | missing_dest hne _ _ => cases hne
    | ret_exp_err _ he' => have hv := (EvalExp.leaf_iff he _).mp he'; cases hv
    | ret_ty_err hne => exact False.elim (hne hretTy)
  · rintro ⟨rfl, rfl⟩
    refine ⟨rfl, ?_⟩
    cases hattr : applyRetFMFAndAttrsPure st.dataLayout (freeAllocaList st.memory frame.frameAllocas)
        (.ret ty) {} frame.defn.prototype.retAttrs v with
    | ok v' => exact StepTerm.ret_ok hretTy (EvalExp.leaf_ok he) (StepRet.top_ok rfl hattr)
    | error err => exact StepTerm.ret_ok hretTy (EvalExp.leaf_ok he) (StepRet.callee_attr_err hattr)

/-- Deterministic inversion for top-level `ret void`. -/
theorem Step.retVoid_top_iff {st frame tid}
    (hf : st.frames = [frame])
    (hc : frame.remainingCode = [])
    (hretTy : frame.defn.retType? = some .void)
    (hterm : frame.terminator = (tid, .retVoid))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔
      ev = none ∧
      c' = .halted .void (freeAllocaList st.memory frame.frameAllocas) := by
  have hattr : applyRetFMFAndAttrsPure st.dataLayout (freeAllocaList st.memory frame.frameAllocas)
      .void {} frame.defn.prototype.retAttrs .void = .ok .void := rfl
  rw [Step.term_iff hf hc hterm]
  constructor
  · rintro ⟨rfl, ht⟩
    cases ht with
    | retVoid_ok _ hr =>
      cases hr with
      | top_ok _ hattr' => rw [hattr] at hattr'; cases hattr'; exact ⟨rfl, rfl⟩
      | call_ok hne _ _ _ _ => cases hne
      | noreturn_ub hne _ _ _ => cases hne
      | callee_attr_err hattr' => rw [hattr] at hattr'; cases hattr'
      | caller_attr_err hne _ _ _ _ => cases hne
      | missing_dest hne _ _ => cases hne
    | retVoid_ty_err hne => exact False.elim (hne hretTy)
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, StepTerm.retVoid_ok hretTy (StepRet.top_ok rfl hattr)⟩

/-- Deterministic inversion for `unreachable`. -/
theorem Step.unreachable_iff {st frame callers tid}
    (hf : st.frames = frame :: callers)
    (hc : frame.remainingCode = [])
    (hterm : frame.terminator = (tid, .unreachable))
    (ev : Option TraceEvent) (c' : Config) :
    Step (.running st) ev c' ↔ ev = none ∧ ∃ msg, c' = .ub msg := by
  rw [Step.term_iff hf hc hterm]
  constructor
  · rintro ⟨rfl, ht⟩
    cases ht with
    | unreachable_ub => exact ⟨rfl, _, rfl⟩
  · rintro ⟨rfl, msg, rfl⟩
    exact ⟨rfl, StepTerm.unreachable_ub⟩

end LeanNanoLlvm.Semantics
