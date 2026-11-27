import LeanNanoLlvm.Util.Config
import LeanNanoLlvm.Util.Oracle
import LeanNanoLlvm.Util.AssocMap
import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.DataLayout
import LeanNanoLlvm.AST.Print
import LeanNanoLlvm.Semantics.Display
import LeanNanoLlvm.Semantics.FreezeUndef
import LeanNanoLlvm.Semantics.GEP

/-!
# Value operations

The deterministic operations shared by the relational and executable semantics: lifting scalar
operations over vectors, parameter and return attributes, integer and comparison operations,
aggregate and vector element access, conversions, and `bitinsert`/`bitextract`.
-/

namespace LeanNanoLlvm.Semantics

open AST

def liftUnaryPure (resElemTy : LlvmType) (v : RegisterValue)
    (f : RegisterValue → Except ExecError RegisterValue) : Except ExecError RegisterValue :=
  match v with
  | .vector _ elems => do
    let rec go : List RegisterValue → Except ExecError (List RegisterValue)
      | [] => .ok []
      | e :: es => do
        let r ← f e
        let rs ← go es
        .ok (r :: rs)
    .ok (.vector resElemTy (← go elems))
  | _ => f v

def liftBinaryPure (resElemTy : LlvmType) (v1 v2 : RegisterValue)
    (f : RegisterValue → RegisterValue → Except ExecError RegisterValue) : Except ExecError RegisterValue :=
  match v1, v2 with
  | .vector _ es1, .vector _ es2 =>
    if es1.length != es2.length then
      .error (.staticError s!"Vector length mismatch: {es1.length} vs {es2.length}")
    else do
      let rec go : List RegisterValue → List RegisterValue → Except ExecError (List RegisterValue)
        | x :: xs, y :: ys => do
          let r ← f x y
          let rs ← go xs ys
          .ok (r :: rs)
        | _, _ => .ok []
      .ok (.vector resElemTy (← go es1 es2))
  | _, _ => f v1 v2

/-- Parameter attributes checked on an argument when the call is made. For `byval` arguments
`llubi` first copies the pointee and checks the attributes on the copy, which satisfies them by
construction, so they are not applied to the source pointer. -/
def byvalDeferredAttrs (attrs : List ValueAttr) : List ValueAttr :=
  if attrs.any (fun | .byval _ => true | _ => false) then [] else attrs

@[simp] theorem byvalDeferredAttrs_nil : byvalDeferredAttrs [] = [] := rfl

def applySingleAttrPure (dl : DataLayout) (mem : MemoryState) (ty : LlvmType)
    (val : RegisterValue) (attr : ValueAttr) : Except ExecError RegisterValue :=
  match attr with
  | .noundef =>
    if val.containsPoison then
      .error (.immediateUB s!"The value {val.llubiString mem dl} violates noundef attribute.")
    else .ok val
  | .nonnull =>
    liftUnaryPure ty.scalarType val fun
      | .ptr as (.value p) =>
        if p.isNull dl as then .ok (.ptr as .poison) else .ok (.ptr as (.value p))
      | other => .ok other
  | .align a =>
    liftUnaryPure ty.scalarType val fun
      | .ptr as (.value p) =>
        if a > 1 && p.addr.toNat % a != 0 then .ok (.ptr as .poison)
        else .ok (.ptr as (.value p))
      | other => .ok other
  | .range lo hi =>
    liftUnaryPure ty.scalarType val fun
      | .bv w (.value bv) =>
        let v := bv.toNat
        let loN := (BitVec.ofInt w lo).toNat
        let hiN := (BitVec.ofInt w hi).toNat
        let ok := if loN ≤ hiN then loN ≤ v && v < hiN else v ≥ loN || v < hiN
        if ok then .ok (.bv w (.value bv)) else .ok (.bv w .poison)
      | other => .ok other
  | .rangeList rs =>
    liftUnaryPure ty.scalarType val fun
      | .bv w (.value bv) =>
        let v := bv.toNat
        let ok := rs.any fun (lo, hi) =>
          let loN := (BitVec.ofInt w lo).toNat
          let hiN := (BitVec.ofInt w hi).toNat
          if loN ≤ hiN then loN ≤ v && v < hiN else v ≥ loN || v < hiN
        if ok then .ok (.bv w (.value bv)) else .ok (.bv w .poison)
      | other => .ok other
  | .nofpclass mask =>
    let rec go : RegisterValue → RegisterValue
      | .float ft (.value flt) =>
        if (flt.fpClassBit &&& mask) != 0 then .float ft .poison else .float ft (.value flt)
      | .vector elemTy elems => .vector elemTy (elems.map go)
      | .struct packed fieldTys fields => .struct packed fieldTys (fields.map go)
      | .array elemTy elems => .array elemTy (elems.map go)
      | other => other
    .ok (go val)
  | .dereferenceable bytes =>
    match val with
    | .ptr _ .poison =>
      .error (.immediateUB s!"The value poison violates dereferenceable({bytes}) attribute.")
    | .ptr as (.value p) =>
      if p.isNull dl as then
        .error (.immediateUB s!"The value {val.llubiString mem dl} violates dereferenceable({bytes}) attribute.")
      else match mem.resolveObject? p with
        | none =>
          .error (.immediateUB s!"The value {val.llubiString mem dl} violates dereferenceable({bytes}) attribute.")
        | some mo =>
          if mo.state == .freed || mem.isInaccessible mo.allocId || bytes > mo.size || p.addr.toNat < mo.baseAddr ||
             p.addr.toNat - mo.baseAddr > mo.size - bytes then
            .error (.immediateUB s!"The value {val.llubiString mem dl} violates dereferenceable({bytes}) attribute.")
          else .ok (.ptr as (.value p))
    | other => .ok other
  | .dereferenceableOrNull bytes =>
    match val with
    | .ptr _ .poison =>
      .error (.immediateUB s!"The value poison violates dereferenceable_or_null({bytes}) attribute.")
    | .ptr as (.value p) =>
      if p.isNull dl as then .ok (.ptr as (.value p))
      else match mem.resolveObject? p with
        | none =>
          .error (.immediateUB s!"The value {val.llubiString mem dl} violates dereferenceable_or_null({bytes}) attribute.")
        | some mo =>
          if mo.state == .freed || mem.isInaccessible mo.allocId || bytes > mo.size || p.addr.toNat < mo.baseAddr ||
             p.addr.toNat - mo.baseAddr > mo.size - bytes then
            .error (.immediateUB s!"The value {val.llubiString mem dl} violates dereferenceable_or_null({bytes}) attribute.")
          else .ok (.ptr as (.value p))
    | other => .ok other
  | .byval _ => .ok val
  | .sret ty =>
    match val with
    | .ptr as (.value p) =>
      if p.isNull dl as then .ok (.ptr as .poison)
      else match mem.resolveObject? p with
        | none => .ok (.ptr as .poison)
        | some mo =>
          let sz := dl.typeStoreSize ty
          if mo.state == .freed || mem.isInaccessible mo.allocId || sz > mo.size || p.addr.toNat < mo.baseAddr ||
             p.addr.toNat - mo.baseAddr > mo.size - sz then
            .ok (.ptr as .poison)
          else .ok (.ptr as (.value p))
    | other => .ok other
  | .noalias => .ok val
  | .readonly => .ok val

def applyValueAttrsPure (dl : DataLayout) (mem : MemoryState) (ty : LlvmType)
    (val : RegisterValue) : List ValueAttr → Except ExecError RegisterValue
  | [] => .ok val
  | a :: rest => do
    let v' ← applySingleAttrPure dl mem ty val a
    applyValueAttrsPure dl mem ty v' rest

@[simp_llvm]
def evalIntBinaryScalarPure (op : IntBinaryOp) (v1 v2 : RegisterValue) :
    Except ExecError RegisterValue :=
  match v1, v2 with
  | .bv w1 b1, .bv w2 b2 =>
    if h : w1 = w2 then
      let b1' : IntW w2 := h ▸ b1
      match op with
      | .add nuw nsw => .ok (.bv w2 (add b1' b2 { nuw := nuw, nsw := nsw }))
      | .sub nuw nsw => .ok (.bv w2 (sub b1' b2 { nuw := nuw, nsw := nsw }))
      | .mul nuw nsw => .ok (.bv w2 (mul b1' b2 { nuw := nuw, nsw := nsw }))
      | .shl nuw nsw => .ok (.bv w2 (shl b1' b2 { nuw := nuw, nsw := nsw }))
      | .udiv exact =>
        match evalDivRemUB false false exact b1' b2 with
        | .ok res => .ok (.bv w2 res)
        | .error e => .error e
      | .sdiv exact =>
        match evalDivRemUB true false exact b1' b2 with
        | .ok res => .ok (.bv w2 res)
        | .error e => .error e
      | .lshr exact => .ok (.bv w2 (lshr b1' b2 { exact := exact }))
      | .ashr exact => .ok (.bv w2 (ashr b1' b2 { exact := exact }))
      | .urem =>
        match evalDivRemUB false true false b1' b2 with
        | .ok res => .ok (.bv w2 res)
        | .error e => .error e
      | .srem =>
        match evalDivRemUB true true false b1' b2 with
        | .ok res => .ok (.bv w2 res)
        | .error e => .error e
      | .and => .ok (.bv w2 (and b1' b2))
      | .or disjoint => .ok (.bv w2 (or b1' b2 { disjoint := disjoint }))
      | .xor => .ok (.bv w2 (xor b1' b2))
    else
      .error (.staticError s!"Mismatched integer widths in binary op: {w1} vs {w2}")
  | _, _ => .error (.staticError s!"Expected integer values for int binary op, got {v1}, {v2}")

def evalICmpScalarPure (dl : DataLayout) (samesign : Bool) (pred : ICmpPred) (v1 v2 : RegisterValue) :
    Except ExecError RegisterValue :=
  match v1, v2 with
  | .bv w1 b1, .bv w2 b2 =>
    if h : w1 = w2 then
      .ok (.bv 1 (icmp samesign pred (h ▸ b1) b2))
    else
      .error (.staticError s!"Mismatched integer widths in icmp: {w1} vs {w2}")
  | .ptr as1 p1, .ptr _ p2 =>
    match p1, p2 with
    | .value a, .value b =>
      if h : a.addrWidth = b.addrWidth then
        let idxW := dl.getIndexSizeInBits as1
        let aAddr := (h ▸ a.addr).truncate idxW
        let bAddr := b.addr.truncate idxW
        .ok (.bv 1 (icmp samesign pred (.value aAddr) (.value bAddr)))
      else
        .error (.staticError s!"Mismatched pointer widths in icmp: {a.addrWidth} vs {b.addrWidth}")
    | _, _ => .ok (.bv 1 .poison)
  | _, _ => .error (.staticError s!"Expected integer or pointer values in icmp, got {v1}, {v2}")

def extractValueAux (v : RegisterValue) : List Nat → Except ExecError RegisterValue
  | [] => .ok v
  | idx :: rest =>
    match v with
    | .struct _ _ fields =>
      match fields[idx]? with
      | some f => extractValueAux f rest
      | none => .error (.staticError s!"extractvalue index {idx} out of bounds")
    | .array _ elems =>
      match elems[idx]? with
      | some e => extractValueAux e rest
      | none => .error (.staticError s!"extractvalue index {idx} out of bounds")
    | _ => .error (.staticError s!"extractvalue on non-aggregate value {v}")

def insertValueAux (v newVal : RegisterValue) : List Nat → Except ExecError RegisterValue
  | [] => .ok newVal
  | idx :: rest =>
    match v with
    | .struct packed fTys fields =>
      match fields[idx]? with
      | some oldF => do
        let updated ← insertValueAux oldF newVal rest
        .ok (.struct packed fTys (fields.set idx updated))
      | none => .error (.staticError s!"insertvalue index {idx} out of bounds")
    | .array elemTy elems =>
      match elems[idx]? with
      | some oldE => do
        let updated ← insertValueAux oldE newVal rest
        .ok (.array elemTy (elems.set idx updated))
      | none => .error (.staticError s!"insertvalue index {idx} out of bounds")
    | _ => .error (.staticError s!"insertvalue on non-aggregate value {v}")

def evalSelectPure (cVal tVal fVal : RegisterValue) : Except ExecError RegisterValue :=
  match cVal with
  | .bv 1 .poison =>
    match tVal with
    | .bv w _ => .ok (.bv w .poison)
    | .byte w _ => .ok (.byte w (List.replicate w .poison))
    | .float ft _ => .ok (.float ft .poison)
    | .ptr as _ => .ok (.ptr as .poison)
    | .vector eTy es => .ok (.vector eTy (List.replicate es.length (RegisterValue.poisonOf eTy)))
    | .array eTy es => .ok (.array eTy (List.replicate es.length (RegisterValue.poisonOf eTy)))
    | .struct p ts _ => .ok (.struct p ts (ts.map RegisterValue.poisonOf))
    | .void => .ok .void
  | .bv 1 (.value b) =>
    if b != 0 then .ok tVal else .ok fVal
  | .vector _ condElems =>
    match tVal, fVal with
    | .vector eTy tElems, .vector _ fElems =>
      if condElems.length != tElems.length || tElems.length != fElems.length then
        .error (.staticError "Vector length mismatch in select")
      else
        let out := (List.range condElems.length).map fun i =>
          let ci := condElems.getD i (.bv 1 .poison)
          let ti := tElems.getD i (RegisterValue.poisonOf eTy)
          let fi := fElems.getD i (RegisterValue.poisonOf eTy)
          match ci with
          | .bv 1 (.value b) => if b != 0 then ti else fi
          | _ => RegisterValue.poisonOf eTy
        .ok (.vector eTy out)
    | _, _ => .error (.staticError "Expected vector operands for vector select")
  | other => .error (.staticError s!"Expected i1 or <N x i1> condition in select, got {other}")

def evalExtractElementPure (vecVal idxVal : RegisterValue) : Except ExecError RegisterValue :=
  match vecVal with
  | .vector elemTy elems =>
    match idxVal with
    | .bv _ .poison => .ok (RegisterValue.poisonOf elemTy)
    | .bv _ (.value idxBV) =>
      let idx := idxBV.toNat
      if idx < elems.length then .ok (elems.getD idx (RegisterValue.poisonOf elemTy))
      else .ok (RegisterValue.poisonOf elemTy)
    | other => .error (.staticError s!"Expected integer index in extractelement, got {other}")
  | other => .error (.staticError s!"Expected vector in extractelement, got {other}")

def evalInsertElementPure (vecVal elemVal idxVal : RegisterValue) : Except ExecError RegisterValue :=
  match vecVal with
  | .vector elemTy elems =>
    match idxVal with
    | .bv _ .poison =>
      .ok (.vector elemTy (List.replicate elems.length (RegisterValue.poisonOf elemTy)))
    | .bv _ (.value idxBV) =>
      let idx := idxBV.toNat
      if idx < elems.length then .ok (.vector elemTy (elems.set idx elemVal))
      else .ok (.vector elemTy (List.replicate elems.length (RegisterValue.poisonOf elemTy)))
    | other => .error (.staticError s!"Expected integer index in insertelement, got {other}")
  | other => .error (.staticError s!"Expected vector in insertelement, got {other}")

def evalShuffleVectorPure (v1 v2 : RegisterValue) (mask : List (Option Nat)) :
    Except ExecError RegisterValue :=
  match v1, v2 with
  | .vector elemTy es1, .vector _ es2 =>
    let n := es1.length
    let out := mask.map fun
      | none => RegisterValue.poisonOf elemTy
      | some idx =>
        if idx < n then es1.getD idx (RegisterValue.poisonOf elemTy)
        else if idx < 2 * n then es2.getD (idx - n) (RegisterValue.poisonOf elemTy)
        else RegisterValue.poisonOf elemTy
    .ok (.vector elemTy out)
  | _, _ => .error (.staticError "Expected vector operands in shufflevector")

private def evalPtrToIntElem (dstW : Nat) (v : RegisterValue) (m : MemoryState) :
    Except ExecError (RegisterValue × MemoryState) :=
  match v with
  | .ptr _ .poison => .ok (.bv dstW .poison, m)
  | .ptr _ (.value p) =>
    let m1 := m.exposeProvenance p.prov
    let resized := if dstW ≥ p.addrWidth then p.addr.zeroExtend dstW else p.addr.truncate dstW
    .ok (.bv dstW (.value resized), m1)
  | other => .error (.staticError s!"Expected pointer in ptrtoint, got {other}")

private def evalPtrToIntList (dstW : Nat) :
    List RegisterValue → MemoryState → Except ExecError (List RegisterValue × MemoryState)
  | [], m => .ok ([], m)
  | e :: es, m =>
    match evalPtrToIntElem dstW e m with
    | .error err => .error err
    | .ok (r, m1) =>
      match evalPtrToIntList dstW es m1 with
      | .error err => .error err
      | .ok (rs, m2) => .ok (r :: rs, m2)

private theorem evalPtrToIntElem_wf {dstW v m r m'} (hwf : MemoryState.WellFormed m)
    (h : evalPtrToIntElem dstW v m = .ok (r, m')) : MemoryState.WellFormed m' := by
  unfold evalPtrToIntElem at h
  cases v with
  | ptr _ pv =>
    cases pv with
    | poison => cases h; exact hwf
    | value p => cases h; exact MemoryState.exposeProvenance_preserves_wf hwf p.prov
  | _ => cases h

private theorem evalPtrToIntList_wf {dstW es m rs m'} (hwf : MemoryState.WellFormed m)
    (h : evalPtrToIntList dstW es m = .ok (rs, m')) : MemoryState.WellFormed m' := by
  induction es generalizing m rs with
  | nil => unfold evalPtrToIntList at h; cases h; exact hwf
  | cons e rest ih =>
    unfold evalPtrToIntList at h
    cases h1 : evalPtrToIntElem dstW e m with
    | error err => rw [h1] at h; cases h
    | ok p1 =>
      rw [h1] at h
      obtain ⟨r1, m1⟩ := p1
      dsimp only at h
      have hm1 := evalPtrToIntElem_wf hwf h1
      cases h2 : evalPtrToIntList dstW rest m1 with
      | error err => rw [h2] at h; cases h
      | ok p2 =>
        rw [h2] at h
        obtain ⟨rs2, m2⟩ := p2
        cases h
        exact ih hm1 h2

/-- Map an oracle-threading function over a list, left to right. -/
def mapListOracle (f : RegisterValue → OracleState → Except ExecError (RegisterValue × OracleState)) :
    List RegisterValue → OracleState → Except ExecError (List RegisterValue × OracleState)
  | [], o => .ok ([], o)
  | e :: es, o => do
    let (r, o1) ← f e o
    let (rs, o2) ← mapListOracle f es o1
    return (r :: rs, o2)

/-- Map an oracle-threading function over two lists pairwise, left to right (stopping at the
shorter list). -/
def mapList2Oracle
    (f : RegisterValue → RegisterValue → OracleState → Except ExecError (RegisterValue × OracleState)) :
    List RegisterValue → List RegisterValue → OracleState →
      Except ExecError (List RegisterValue × OracleState)
  | x :: xs, y :: ys, o => do
    let (r, o1) ← f x y o
    let (rs, o2) ← mapList2Oracle f xs ys o1
    return (r :: rs, o2)
  | _, _, o => .ok ([], o)

/-- Conversions that do not modify `MemoryState` (everything except `ptrtoint`). -/
def evalConversionNoMem (dl : DataLayout) (cfg : SemanticsConfig) (mem : MemoryState)
    (op : ConversionOp) (fromTy : LlvmType) (val : RegisterValue) (toTy : LlvmType)
    (o : OracleState) : Except ExecError (RegisterValue × OracleState) :=
  match op with
  | .bitcast =>
    if dl.typeSizeInBits fromTy != dl.typeSizeInBits toTy then
      .error (.staticError s!"bitcast size mismatch: {fromTy.print} ({dl.typeSizeInBits fromTy}b) to {toTy.print} ({dl.typeSizeInBits toTy}b)")
    else
      let bs := valueToBytes dl cfg val fromTy
      match bytesToValue dl cfg bs toTy (drawPtrTags val o) with
      | (v, _, o') => .ok (v, o')
  | .trunc nuw nsw =>
    match toTy.scalarType with
    | .int toW => do
      let v ← liftUnaryPure (.int toW) val fun
        | .bv _ iv => .ok (.bv toW (trunc toW iv { nuw := nuw, nsw := nsw }))
        | other => .error (.staticError s!"Expected integer in trunc, got {other}")
      .ok (v, o)
    | _ => .error (.staticError s!"Expected integer target type in trunc, got {toTy.print}")
  | .zext nneg =>
    match toTy.scalarType with
    | .int toW => do
      let v ← liftUnaryPure (.int toW) val fun
        | .bv _ iv => .ok (.bv toW (zext toW iv { nneg := nneg }))
        | other => .error (.staticError s!"Expected integer in zext, got {other}")
      .ok (v, o)
    | _ => .error (.staticError s!"Expected integer target type in zext, got {toTy.print}")
  | .sext =>
    match toTy.scalarType with
    | .int toW => do
      let v ← liftUnaryPure (.int toW) val fun
        | .bv _ iv => .ok (.bv toW (sext toW iv))
        | other => .error (.staticError s!"Expected integer in sext, got {other}")
      .ok (v, o)
    | _ => .error (.staticError s!"Expected integer target type in sext, got {toTy.print}")
  | .fptrunc fmf | .fpext fmf =>
    match toTy.scalarType with
    | .float dstFt =>
      let goElem (v : RegisterValue) (o0 : OracleState) : Except ExecError (RegisterValue × OracleState) :=
        match v with
        | .float _ fw =>
          match evalFPConv dstFt cfg fmf fw o0 with
          | (r, o1) => .ok (.float dstFt r, o1)
        | other => .error (.staticError s!"Expected float in fptrunc/fpext, got {other}")
      match val with
      | .vector _ elems =>
        match mapListOracle goElem elems o with
        | .ok (rs, o') => .ok (.vector (.float dstFt) rs, o')
        | .error e => .error e
      | _ => goElem val o
    | _ => .error (.staticError s!"Expected float target type in fptrunc/fpext, got {toTy.print}")
  | .fptoui =>
    match toTy.scalarType with
    | .int dstW => do
      let v ← liftUnaryPure (.int dstW) val fun
        | .float _ fw => .ok (.bv dstW (evalFPToInt dstW false fw))
        | other => .error (.staticError s!"Expected float in fptoui, got {other}")
      .ok (v, o)
    | _ => .error (.staticError s!"Expected integer target type in fptoui, got {toTy.print}")
  | .fptosi =>
    match toTy.scalarType with
    | .int dstW => do
      let v ← liftUnaryPure (.int dstW) val fun
        | .float _ fw => .ok (.bv dstW (evalFPToInt dstW true fw))
        | other => .error (.staticError s!"Expected float in fptosi, got {other}")
      .ok (v, o)
    | _ => .error (.staticError s!"Expected integer target type in fptosi, got {toTy.print}")
  | .uitofp nneg fmf =>
    match toTy.scalarType with
    | .float dstFt =>
      let goElem (v : RegisterValue) (o0 : OracleState) : Except ExecError (RegisterValue × OracleState) :=
        match v with
        | .bv _ iv =>
          match evalIntToFP dstFt cfg false nneg fmf iv o0 with
          | (r, o1) => .ok (.float dstFt r, o1)
        | other => .error (.staticError s!"Expected integer in uitofp, got {other}")
      match val with
      | .vector _ elems =>
        match mapListOracle goElem elems o with
        | .ok (rs, o') => .ok (.vector (.float dstFt) rs, o')
        | .error e => .error e
      | _ => goElem val o
    | _ => .error (.staticError s!"Expected float target type in uitofp, got {toTy.print}")
  | .sitofp fmf =>
    match toTy.scalarType with
    | .float dstFt =>
      let goElem (v : RegisterValue) (o0 : OracleState) : Except ExecError (RegisterValue × OracleState) :=
        match v with
        | .bv _ iv =>
          match evalIntToFP dstFt cfg true false fmf iv o0 with
          | (r, o1) => .ok (.float dstFt r, o1)
        | other => .error (.staticError s!"Expected integer in sitofp, got {other}")
      match val with
      | .vector _ elems =>
        match mapListOracle goElem elems o with
        | .ok (rs, o') => .ok (.vector (.float dstFt) rs, o')
        | .error e => .error e
      | _ => goElem val o
    | _ => .error (.staticError s!"Expected float target type in sitofp, got {toTy.print}")
  | .ptrtoaddr =>
    match toTy.scalarType with
    | .int dstW => do
      let v ← liftUnaryPure (.int dstW) val fun
        | .ptr _ .poison => .ok (.bv dstW .poison)
        | .ptr _ (.value p) =>
          let resized := if dstW ≥ p.addrWidth then p.addr.zeroExtend dstW else p.addr.truncate dstW
          .ok (.bv dstW (.value resized))
        | other => .error (.staticError s!"Expected pointer in ptrtoaddr, got {other}")
      .ok (v, o)
    | _ => .error (.staticError s!"Expected integer target type in ptrtoaddr, got {toTy.print}")
  | .inttoptr =>
    match toTy.scalarType with
    | .ptr as =>
      let pw := dl.getPointerSizeInBits as
      let (wid, o1) := o.freshId
      let prov := mem.getWildcardProvenance wid
      do
        let v ← liftUnaryPure (.ptr as) val fun
          | .bv _ .poison => .ok (.ptr as .poison)
          | .bv w (.value bv) =>
            let addr := if pw ≥ w then bv.zeroExtend pw else bv.truncate pw
            .ok (.ptr as (.value { prov := prov, addrWidth := pw, addr := addr }))
          | other => .error (.staticError s!"Expected integer in inttoptr, got {other}")
        .ok (v, o1)
    | _ => .error (.staticError s!"Expected pointer target type in inttoptr, got {toTy.print}")
  | .addrspacecast =>
    match toTy.scalarType with
    | .ptr dstAs =>
      let dstW := dl.getPointerSizeInBits dstAs
      do
        let v ← liftUnaryPure (.ptr dstAs) val fun
          | .ptr _ .poison => .ok (.ptr dstAs .poison)
          | .ptr _ (.value p) =>
            let addr := if dstW ≥ p.addrWidth then p.addr.zeroExtend dstW else p.addr.truncate dstW
            .ok (.ptr dstAs (.value { prov := p.prov, addrWidth := dstW, addr := addr }))
          | other => .error (.staticError s!"Expected pointer in addrspacecast, got {other}")
        .ok (v, o)
    | _ => .error (.staticError s!"Expected pointer target type in addrspacecast, got {toTy.print}")
  | .ptrtoint => .error (.staticError "Internal error: ptrtoint handled by evalConversionExec")

/-- Full conversion evaluator (handles `ptrtoint` provenance exposure + all other casts). -/
def evalConversionExec (dl : DataLayout) (cfg : SemanticsConfig) (mem : MemoryState)
    (op : ConversionOp) (fromTy : LlvmType) (val : RegisterValue) (toTy : LlvmType)
    (o : OracleState) : Except ExecError (RegisterValue × MemoryState × OracleState) :=
  match op with
  | .ptrtoint =>
    match toTy.scalarType with
    | .int dstW =>
      match val with
      | .vector _ elems =>
        match evalPtrToIntList dstW elems mem with
        | .ok (rs, m') => .ok (.vector (.int dstW) rs, m', o)
        | .error e => .error e
      | _ =>
        match evalPtrToIntElem dstW val mem with
        | .ok (r, m') => .ok (r, m', o)
        | .error e => .error e
    | _ => .error (.staticError s!"Expected integer target type in ptrtoint, got {toTy.print}")
  | _ =>
    match evalConversionNoMem dl cfg mem op fromTy val toTy o with
    | .ok (v, o') => .ok (v, mem, o')
    | .error e => .error e

/-- Pure float unary op (`fneg`) over scalar or vector with oracle draws. -/
def evalFloatUnaryExec (op : FloatUnaryOp) (ty : LlvmType) (val : RegisterValue) (o : OracleState) :
    Except ExecError (RegisterValue × OracleState) :=
  let goElem (v : RegisterValue) (o0 : OracleState) : Except ExecError (RegisterValue × OracleState) :=
    match v with
    | .float ft fw =>
      let r := evalFloatUnaryOp op fw o0
      .ok (.float ft r.1, r.2)
    | _ => .error (.staticError s!"Expected float value for fneg, got {v}")
  match val with
  | .vector _ elems =>
    let rec goList : List RegisterValue → OracleState → Except ExecError (List RegisterValue × OracleState)
      | [], o0 => .ok ([], o0)
      | e :: es, o0 => do
        let (r, o1) ← goElem e o0
        let (rs, o2) ← goList es o1
        .ok (r :: rs, o2)
    match goList elems o with
    | .ok (rs, o') => .ok (.vector ty.scalarType rs, o')
    | .error e => .error e
  | _ => goElem val o

/-- Pure float binary op (`fadd`/`fsub`/`fmul`/`fdiv`/`frem`) over scalar or vector with oracle draws. -/
def evalFloatBinaryExec (cfg : SemanticsConfig) (op : FloatBinaryOp) (ty : LlvmType)
    (v1 v2 : RegisterValue) (o : OracleState) :
    Except ExecError (RegisterValue × OracleState) :=
  let goElem (a b : RegisterValue) (o0 : OracleState) : Except ExecError (RegisterValue × OracleState) :=
    match a, b with
    | .float ft1 fw1, .float ft2 fw2 =>
      if h : ft1 = ft2 then
        let r := evalFloatBinaryOp cfg op (h ▸ fw1) fw2 o0
        .ok (.float ft2 r.1, r.2)
      else .error (.staticError s!"Mismatched float types: {ft1.print} vs {ft2.print}")
    | _, _ => .error (.staticError s!"Expected float values for FP binary op, got {a}, {b}")
  match v1, v2 with
  | .vector _ es1, .vector _ es2 =>
    if es1.length != es2.length then
      .error (.staticError s!"Vector length mismatch: {es1.length} vs {es2.length}")
    else
      let rec goList : List RegisterValue → List RegisterValue → OracleState →
          Except ExecError (List RegisterValue × OracleState)
        | x :: xs, y :: ys, o0 => do
          let (r, o1) ← goElem x y o0
          let (rs, o2) ← goList xs ys o1
          .ok (r :: rs, o2)
        | _, _, o0 => .ok ([], o0)
      match goList es1 es2 o with
      | .ok (rs, o') => .ok (.vector ty.scalarType rs, o')
      | .error e => .error e
  | _, _ => goElem v1 v2 o

/-- Pure `fcmp` over scalar or vector with oracle draws. -/
def evalFCmpExec (cfg : SemanticsConfig) (fmf : FastMathFlags) (pred : FCmpPred)
    (v1 v2 : RegisterValue) (o : OracleState) :
    Except ExecError (RegisterValue × OracleState) :=
  let goElem (a b : RegisterValue) (o0 : OracleState) : Except ExecError (RegisterValue × OracleState) :=
    match a, b with
    | .float ft1 fw1, .float ft2 fw2 =>
      if h : ft1 = ft2 then
        let r := evalFCmpO cfg fmf pred (h ▸ fw1) fw2 o0
        .ok (.bv 1 r.1, r.2)
      else .error (.staticError s!"Mismatched float types in fcmp: {ft1.print} vs {ft2.print}")
    | _, _ => .error (.staticError s!"Expected float values in fcmp, got {a}, {b}")
  match v1, v2 with
  | .vector _ es1, .vector _ es2 =>
    if es1.length != es2.length then
      .error (.staticError s!"Vector length mismatch: {es1.length} vs {es2.length}")
    else
      let rec goList : List RegisterValue → List RegisterValue → OracleState →
          Except ExecError (List RegisterValue × OracleState)
        | x :: xs, y :: ys, o0 => do
          let (r, o1) ← goElem x y o0
          let (rs, o2) ← goList xs ys o1
          .ok (r :: rs, o2)
        | _, _, o0 => .ok ([], o0)
      match goList es1 es2 o with
      | .ok (rs, o') => .ok (.vector .i1 rs, o')
      | .error e => .error e
  | _, _ => goElem v1 v2 o

/-- `evalConversionExec` preserves `MemoryState.WellFormed`. -/
theorem evalConversionExec_preserves_wf {dl cfg mem op fromTy val toTy o res mem' o'}
    (hwf : MemoryState.WellFormed mem)
    (h : evalConversionExec dl cfg mem op fromTy val toTy o = .ok (res, mem', o')) :
    MemoryState.WellFormed mem' := by
  unfold evalConversionExec at h
  split at h
  · split at h
    · split at h
      · split at h
        · cases h; exact evalPtrToIntList_wf hwf ‹_›
        · cases h
      · split at h
        · cases h; exact evalPtrToIntElem_wf hwf ‹_›
        · cases h
    · cases h
  · split at h
    · cases h; exact hwf
    · cases h

/-- Convert a scalar `RegisterValue` into LSB-first `List MemBit` of length `numBits`. -/
private def scalarToMemBits (dl : DataLayout) (ty : LlvmType) (val : RegisterValue) : List MemBit :=
  let numBits := dl.typeSizeInBits ty
  match val with
  | .bv _ .poison | .float _ .poison | .ptr _ .poison =>
    List.replicate numBits .poison
  | .bv _ (.value bv) =>
    (List.range numBits).map fun i => .concrete (bv.getLsbD i) none
  | .float _ (.value flt) =>
    (List.range numBits).map fun i => .concrete (flt.bits.getLsbD i) none
  | .ptr _ (.value p) =>
    (List.range numBits).map fun i => .concrete (p.addr.getLsbD i) (some (p.prov, i))
  | .byte _ bs =>
    (List.range numBits).map fun i => bs.getD i .poison
  | _ => List.replicate numBits .poison

/-- Convert an LSB-first `List MemBit` slice of length `numBits` into a scalar `RegisterValue` of type `ty`. -/
private def memBitsToScalar (dl : DataLayout) (ty : LlvmType) (slice : List MemBit) : RegisterValue :=
  let numBits := dl.typeSizeInBits ty
  match ty with
  | .byte w => .byte w ((List.range w).map fun i => slice.getD i .poison)
  | _ =>
    let rec go (i : Nat) : List MemBit → Nat → Bool → Bool → Option Provenance →
        Nat × Bool × Bool × Option Provenance
      | [], acc, isP, pOk, pAcc => (acc, isP, pOk, pAcc)
      | .poison :: rest, acc, _, _, _ => go (i + 1) rest acc true false none
      | .undef :: rest, acc, _, _, _ => go (i + 1) rest acc true false none
      | .concrete b provBit :: rest, acc, isP, pOk, pAcc =>
        let (pOk', pAcc') :=
          if !pOk then (false, none)
          else match provBit with
            | none => (false, none)
            | some (p, bitPos) =>
              if bitPos != i then (false, none)
              else match pAcc with
                | none => (true, some p)
                | some p0 => if p0 == p then (true, some p0) else (false, none)
        let acc' := if b then acc + (1 <<< i) else acc
        go (i + 1) rest acc' isP pOk' pAcc'
    match go 0 slice 0 false true none with
    | (valBits, isPoison, provOk, provAcc) =>
      if isPoison then RegisterValue.poisonOf ty
      else match ty with
        | .int w => .bv w (.value (BitVec.ofNat w valBits))
        | .float ft => .float ft (.value (IEEEFloat.ofNatBits valBits))
        | .ptr as =>
          let prov := if provOk then provAcc.getD .nullary else .nullary
          .ptr as (.value { prov := prov, addrWidth := numBits, addr := BitVec.ofNat numBits valBits })
        | _ => RegisterValue.poisonOf ty

/-- Pure scalar `bitinsert` evaluator. -/
private def evalBitInsertScalarPure (dl : DataLayout) (baseTy valTy : LlvmType)
    (base val off : RegisterValue) : RegisterValue :=
  match baseTy, base, off with
  | .byte w, .byte _ baseBits, .bv _ (.value offBV) =>
    let offBits := offBV.toNat
    let numBits := dl.typeSizeInBits valTy
    if offBits + numBits > w then RegisterValue.poisonOf baseTy
    else
      let valBits := scalarToMemBits dl valTy val
      let newBits := (List.range w).map fun i =>
        if offBits ≤ i && i < offBits + numBits then
          valBits.getD (i - offBits) .poison
        else
          baseBits.getD i .poison
      .byte w newBits
  | _, _, _ => RegisterValue.poisonOf baseTy

/-- Pure scalar/vector `bitinsert` evaluator. -/
def evalBitInsertPure (dl : DataLayout) (baseTy valTy : LlvmType)
    (base val off : RegisterValue) : Except ExecError RegisterValue :=
  match baseTy, base, val, off with
  | .vector n elemBaseTy, .vector _ bs, .vector _ vs, .vector _ os =>
    let elemValTy := valTy.scalarType
    let res := (List.range n).map fun i =>
      evalBitInsertScalarPure dl elemBaseTy elemValTy
        (bs.getD i (RegisterValue.poisonOf elemBaseTy))
        (vs.getD i (RegisterValue.poisonOf elemValTy))
        (os.getD i (.bv 32 .poison))
    .ok (.vector elemBaseTy res)
  | _, _, _, _ =>
    .ok (evalBitInsertScalarPure dl baseTy valTy base val off)

/-- Pure scalar `bitextract` evaluator. -/
private def evalBitExtractScalarPure (dl : DataLayout) (retTy : LlvmType)
    (src off : RegisterValue) : RegisterValue :=
  match src, off with
  | .byte w srcBits, .bv _ (.value offBV) =>
    let offBits := offBV.toNat
    let numBits := dl.typeSizeInBits retTy
    if offBits + numBits > w then RegisterValue.poisonOf retTy
    else
      let slice := (List.range numBits).map fun i => srcBits.getD (offBits + i) .poison
      memBitsToScalar dl retTy slice
  | _, _ => RegisterValue.poisonOf retTy

/-- Pure scalar/vector `bitextract` evaluator. -/
def evalBitExtractPure (dl : DataLayout) (retTy : LlvmType)
    (src off : RegisterValue) : Except ExecError RegisterValue :=
  match retTy, src, off with
  | .vector n elemRetTy, .vector _ ss, .vector _ os =>
    let res := (List.range n).map fun i =>
      evalBitExtractScalarPure dl elemRetTy
        (ss.getD i (.byte 0 []))
        (os.getD i (.bv 32 .poison))
    .ok (.vector elemRetTy res)
  | _, _, _ =>
    .ok (evalBitExtractScalarPure dl retTy src off)

attribute [simp_llvm] liftUnaryPure liftBinaryPure evalIntBinaryScalarPure
attribute [simp_step] applyValueAttrsPure

end LeanNanoLlvm.Semantics
