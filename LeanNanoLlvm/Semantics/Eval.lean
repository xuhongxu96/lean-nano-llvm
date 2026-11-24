import LeanNanoLlvm.Semantics.Semantics
import LeanNanoLlvm.Semantics.FloatOps
import LeanNanoLlvm.Semantics.Memory
import LeanNanoLlvm.Semantics.State
import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.DataLayout
import LeanNanoLlvm.AST.Print

namespace LeanNanoLlvm.Semantics

open Std
open AST

/-! ### Oracle & Configuration Helpers -/

@[simp_llvm]
def drawNat : NanoLlvmM Nat :=
  StateT.lift (do
    let o ← get
    let (v, o') := o.nextNat
    set o'
    pure v)

@[simp_llvm]
def drawBool : NanoLlvmM Bool :=
  StateT.lift (do
    let o ← get
    let (v, o') := o.nextBool
    set o'
    pure v)

@[simp_llvm]
def drawBitVec (w : Nat) : NanoLlvmM (BitVec w) :=
  StateT.lift (do
    let o ← get
    let (v, o') := o.nextBitVec w
    set o'
    pure v)

@[simp_llvm]
def throwUB {α : Type} (msg : String) : NanoLlvmM α :=
  throw (.immediateUB msg)

@[simp_llvm]
def throwStatic {α : Type} (msg : String) : NanoLlvmM α :=
  throw (.staticError msg)

@[simp_llvm]
def expectConcreteWidth {φ : Nat} : Width φ → NanoLlvmM Nat
  | .concrete w => pure w
  | .mvar i => throwStatic s!"symbolic width {Width.print (.mvar i)} is not executable; instantiate widths first"

mutual
def concretizeRetType {φ : Nat} : LlvmRetType φ → NanoLlvmM (LlvmRetType 0)
  | .void => pure .void
  | .ret ty => return .ret (← concretizeType ty)

def concretizeType {φ : Nat} : LlvmType φ → NanoLlvmM (LlvmType 0)
  | .int w => return .int (.concrete (← expectConcreteWidth w))
  | .float ft => pure (.float ft)
  | .ptr as => pure (.ptr as)
  | .vector n elem => return .vector n (← concretizeType elem)
  | .array n elem => return .array n (← concretizeType elem)
  | .struct packed fields => return .struct packed (← concretizeTypeList fields)
  | .function ret args isVarArg =>
      return .function (← concretizeRetType ret) (← concretizeTypeList args) isVarArg

def concretizeTypeList {φ : Nat} : List (LlvmType φ) → NanoLlvmM (List (LlvmType 0))
  | [] => pure []
  | t :: ts => return (← concretizeType t) :: (← concretizeTypeList ts)
end

/- Generate an `undef` value of concrete type `ty`, respecting `st.config.undefMode`. -/
mutual
def genUndefValue (ty : LlvmType 0) : NanoLlvmM RegisterValue := do
  let st ← get
  match st.config.undefMode with
  | .disabled =>
    throwStatic "Encountered `undef` value while `undefMode` is disabled"
  | .zero =>
    pure (RegisterValue.nullOf st.dataLayout ty)
  | .nondet =>
    match ty with
    | .int (.concrete w) => return .bv w (.value (← drawBitVec w))
    | .float ft => return .float ft (.value (IEEEFloat.ofBits (← drawBitVec ft.bitWidth)))
    | .ptr as =>
      let pw := st.dataLayout.getPointerSizeInBits as
      let addr ← drawBitVec pw
      pure (.ptr as (.value { prov := .nullary, addrWidth := pw, addr := addr }))
    | .vector n elem =>
      let elems ← genUndefRepeat elem n
      pure (.vector elem elems)
    | .array n elem =>
      let elems ← genUndefRepeat elem n
      pure (.array elem elems)
    | .struct packed fields =>
      let vals ← genUndefList fields
      pure (.struct packed fields vals)
    | .function .. => throwStatic "Cannot generate `undef` of function type"
termination_by (sizeOf ty, 0)

def genUndefRepeat (elem : LlvmType 0) (n : Nat) : NanoLlvmM (List RegisterValue) :=
  match n with
  | 0 => pure []
  | n' + 1 => do
    let v ← genUndefValue elem
    let vs ← genUndefRepeat elem n'
    pure (v :: vs)
termination_by (sizeOf elem, n + 1)

def genUndefList (tys : List (LlvmType 0)) : NanoLlvmM (List RegisterValue) :=
  match tys with
  | [] => pure []
  | t :: ts => do
    let v ← genUndefValue t
    let vs ← genUndefList ts
    pure (v :: vs)
termination_by (sizeOf tys, 0)
end

@[simp_llvm]
def genUndef {w : Nat} : NanoLlvmM (BitVec w) := do
  let st ← get
  match st.config.undefMode with
  | .disabled => throwStatic "Encountered `undef` value while `undefMode` is disabled"
  | .zero => pure (BitVec.ofNat w 0)
  | .nondet => drawBitVec w

/-! ### Scalar & Vector Helpers -/

@[simp_llvm]
def evalIntBinaryOp {w : Nat} (op : IntBinaryOp) (x y : IntW w) : IntW w :=
  match op with
  | .add nuw nsw => add x y { nuw := nuw, nsw := nsw }
  | .sub nuw nsw => sub x y { nuw := nuw, nsw := nsw }
  | .mul nuw nsw => mul x y { nuw := nuw, nsw := nsw }
  | .shl nuw nsw => shl x y { nuw := nuw, nsw := nsw }
  | .udiv exact  => udiv x y { exact := exact }
  | .sdiv exact  => sdiv x y { exact := exact }
  | .lshr exact  => lshr x y { exact := exact }
  | .ashr exact  => ashr x y { exact := exact }
  | .urem        => urem x y
  | .srem        => srem x y
  | .and         => Semantics.and x y
  | .or disjoint => Semantics.or x y { disjoint := disjoint }
  | .xor         => xor x y

/-- UB-faithful integer binary operation (`udiv`/`sdiv`/`urem`/`srem` raise Immediate UB per `llubi`). -/
@[simp_llvm]
def evalIntBinaryOpM {w : Nat} (op : IntBinaryOp) (x y : IntW w) : NanoLlvmM (IntW w) :=
  match op with
  | .udiv exact =>
    match evalDivRemUB false false exact x y with
    | .ok r => pure r
    | .error e => throw e
  | .sdiv exact =>
    match evalDivRemUB true false exact x y with
    | .ok r => pure r
    | .error e => throw e
  | .urem =>
    match evalDivRemUB false true false x y with
    | .ok r => pure r
    | .error e => throw e
  | .srem =>
    match evalDivRemUB true true false x y with
    | .ok r => pure r
    | .error e => throw e
  | _ => pure (evalIntBinaryOp op x y)

@[simp_llvm]
def evalConversionOp {fromW toW : Nat} (op : ConversionOp) (v : IntW fromW) : IntW toW :=
  match op with
  | .trunc nuw nsw => trunc toW v { nuw := nuw, nsw := nsw }
  | .zext nneg     => zext toW v { nneg := nneg }
  | .sext          => sext toW v
  | _              => .poison

/-- Lift a scalar unary operation to work on either a scalar or a fixed vector `<N x T>`. -/
def liftUnary (resElemTy : LlvmType 0) (v : RegisterValue)
    (f : RegisterValue → NanoLlvmM RegisterValue) : NanoLlvmM RegisterValue :=
  match v with
  | .vector _ elems => do
    let res ← elems.mapM f
    pure (.vector resElemTy res)
  | scalar => f scalar

/-- Lift a scalar binary operation to work on either scalars or fixed vectors `<N x T>`. -/
def liftBinary (resElemTy : LlvmType 0) (v1 v2 : RegisterValue)
    (f : RegisterValue → RegisterValue → NanoLlvmM RegisterValue) : NanoLlvmM RegisterValue :=
  match v1, v2 with
  | .vector _ es1, .vector _ es2 => do
    if es1.length != es2.length then
      throwStatic s!"Mismatched vector lengths: {es1.length} vs {es2.length}"
    let res ← (es1.zip es2).mapM fun (a, b) => f a b
    pure (.vector resElemTy res)
  | s1, s2 => f s1 s2

/-! ### Value Attributes (`nonnull`, `align`, `range`, `nofpclass`, `dereferenceable`, `noundef`) -/

def applySingleAttr (ty : LlvmType 0) (val : RegisterValue) (attr : ValueAttr 0) :
    NanoLlvmM RegisterValue := do
  let st ← get
  let dl := st.dataLayout
  match attr with
  | .noundef =>
    if val.containsPoison then
      throwUB "Value violates `noundef` attribute (contains poison)"
    pure val
  | .nonnull =>
    liftUnary ty.scalarType val fun
      | .ptr as (.value p) =>
        if p.isNull dl as then pure (.ptr as .poison) else pure (.ptr as (.value p))
      | other => pure other
  | .align a =>
    liftUnary ty.scalarType val fun
      | .ptr as (.value p) =>
        if a > 1 && p.addr.toNat % a != 0 then pure (.ptr as .poison)
        else pure (.ptr as (.value p))
      | other => pure other
  | .range lo hi =>
    liftUnary ty.scalarType val fun
      | .bv w (.value bv) =>
        let iv := bv.toInt
        if lo ≤ iv && iv < hi then pure (.bv w (.value bv)) else pure (.bv w .poison)
      | other => pure other
  | .nofpclass mask =>
    liftUnary ty.scalarType val fun
      | .float ft (.value flt) =>
        if (flt.fpClassBit &&& mask) != 0 then pure (.float ft .poison)
        else pure (.float ft (.value flt))
      | other => pure other
  | .dereferenceable bytes =>
    match val with
    | .ptr as (.value p) =>
      if p.isNull dl as then pure (.ptr as .poison)
      else match st.memory.resolveObject? p with
        | none => pure (.ptr as .poison)
        | some mo =>
          if mo.state == .freed || bytes > mo.size || p.addr.toNat < mo.baseAddr ||
             p.addr.toNat - mo.baseAddr > mo.size - bytes then
            pure (.ptr as .poison)
          else pure (.ptr as (.value p))
    | other => pure other
  | .dereferenceableOrNull bytes =>
    match val with
    | .ptr as (.value p) =>
      if p.isNull dl as then pure (.ptr as (.value p))
      else match st.memory.resolveObject? p with
        | none => pure (.ptr as .poison)
        | some mo =>
          if mo.state == .freed || bytes > mo.size || p.addr.toNat < mo.baseAddr ||
             p.addr.toNat - mo.baseAddr > mo.size - bytes then
            pure (.ptr as .poison)
          else pure (.ptr as (.value p))
    | other => pure other
  | .byval _ => pure val

def applyValueAttrs (ty : LlvmType 0) (val : RegisterValue) (attrs : List (ValueAttr 0)) :
    NanoLlvmM RegisterValue :=
  attrs.foldlM (applySingleAttr ty) val

/-! ### FP, ICmp, FCmp, Conversion, and GEP Evaluators -/

def evalFloatUnaryScalar (op : FloatUnaryOp) (v : RegisterValue) : NanoLlvmM RegisterValue := do
  match v with
  | .float ft fw =>
    let flipZ ← drawBool
    pure (.float ft (evalFloatUnaryOp op flipZ fw))
  | _ => throwStatic s!"Expected float value for fneg, got {v}"

def evalFloatBinaryScalar (op : FloatBinaryOp) (v1 v2 : RegisterValue) : NanoLlvmM RegisterValue := do
  let st ← get
  match v1, v2 with
  | .float ft1 fw1, .float ft2 fw2 =>
    if h : ft1 = ft2 then
      let flipL ← drawBool
      let flipR ← drawBool
      let denormL ← drawBool
      let denormR ← drawBool
      let nanSign ← drawBool
      let nanPick ← drawNat
      let res := evalFloatBinaryOp st.config op flipL flipR denormL denormR nanSign nanPick (h ▸ fw1) fw2
      pure (.float ft2 res)
    else
      throwStatic s!"Mismatched float types: {ft1.print} vs {ft2.print}"
  | _, _ => throwStatic s!"Expected float values for FP binary op, got {v1}, {v2}"

def evalICmpScalar (samesign : Bool) (pred : ICmpPred) (v1 v2 : RegisterValue) :
    NanoLlvmM RegisterValue := do
  match v1, v2 with
  | .bv w1 b1, .bv w2 b2 =>
    if h : w1 = w2 then
      pure (.bv 1 (icmp samesign pred (h ▸ b1) b2))
    else
      throwStatic s!"Mismatched integer widths in icmp: {w1} vs {w2}"
  | .ptr _ p1, .ptr _ p2 =>
    match p1, p2 with
    | .value a, .value b =>
      if h : a.addrWidth = b.addrWidth then
        pure (.bv 1 (icmp samesign pred (.value (h ▸ a.addr)) (.value b.addr)))
      else
        throwStatic s!"Mismatched pointer widths in icmp: {a.addrWidth} vs {b.addrWidth}"
    | _, _ => pure (.bv 1 .poison)
  | _, _ => throwStatic s!"Expected integer or pointer values in icmp, got {v1}, {v2}"

def evalFCmpScalar (fmf : FastMathFlags) (pred : FCmpPred) (v1 v2 : RegisterValue) :
    NanoLlvmM RegisterValue := do
  let st ← get
  match v1, v2 with
  | .float ft1 fw1, .float ft2 fw2 =>
    if h : ft1 = ft2 then
      let flipL ← drawBool
      let flipR ← drawBool
      let denormL ← drawBool
      let denormR ← drawBool
      let res := evalFCmp st.config fmf pred flipL flipR denormL denormR (h ▸ fw1) fw2
      pure (.bv 1 res)
    else
      throwStatic s!"Mismatched float types in fcmp: {ft1.print} vs {ft2.print}"
  | _, _ => throwStatic s!"Expected float values in fcmp, got {v1}, {v2}"

def evalConversionM (op : ConversionOp) (fromTy : LlvmType 0) (val : RegisterValue)
    (toTy : LlvmType 0) : NanoLlvmM RegisterValue := do
  let st ← get
  let dl := st.dataLayout
  match op with
  | .bitcast =>
    -- Matches `llubi::visitBitCastInst`: store to bytes and read back as target type.
    if dl.typeSizeInBits fromTy != dl.typeSizeInBits toTy then
      throwStatic s!"bitcast size mismatch: {fromTy.print} ({dl.typeSizeInBits fromTy}b) to {toTy.print} ({dl.typeSizeInBits toTy}b)"
    let bs := valueToBytes dl st.config val fromTy
    let res ← StateT.lift (do
      let o ← get
      let (v, _, o') := bytesToValue dl st.config bs toTy o
      set o'
      pure v)
    pure res
  | .trunc nuw nsw =>
    match toTy.scalarType with
    | .int (.concrete toW) =>
      liftUnary (.int (.concrete toW)) val fun
        | .bv _ iv => pure (.bv toW (trunc toW iv { nuw := nuw, nsw := nsw }))
        | other => throwStatic s!"Expected integer in trunc, got {other}"
    | _ => throwStatic s!"Expected integer target type in trunc, got {toTy.print}"
  | .zext nneg =>
    match toTy.scalarType with
    | .int (.concrete toW) =>
      liftUnary (.int (.concrete toW)) val fun
        | .bv _ iv => pure (.bv toW (zext toW iv { nneg := nneg }))
        | other => throwStatic s!"Expected integer in zext, got {other}"
    | _ => throwStatic s!"Expected integer target type in zext, got {toTy.print}"
  | .sext =>
    match toTy.scalarType with
    | .int (.concrete toW) =>
      liftUnary (.int (.concrete toW)) val fun
        | .bv _ iv => pure (.bv toW (sext toW iv))
        | other => throwStatic s!"Expected integer in sext, got {other}"
    | _ => throwStatic s!"Expected integer target type in sext, got {toTy.print}"
  | .fptrunc fmf | .fpext fmf =>
    match toTy.scalarType with
    | .float dstFt =>
      liftUnary (.float dstFt) val fun
        | .float _ fw => do
          let flipIn ← drawBool
          let denormIn ← drawBool
          let nanSign ← drawBool
          let nanPick ← drawNat
          pure (.float dstFt (evalFPConv dstFt st.config fmf flipIn denormIn nanSign nanPick fw))
        | other => throwStatic s!"Expected float in fptrunc/fpext, got {other}"
    | _ => throwStatic s!"Expected float target type in fptrunc/fpext, got {toTy.print}"
  | .fptoui =>
    match toTy.scalarType with
    | .int (.concrete dstW) =>
      liftUnary (.int (.concrete dstW)) val fun
        | .float _ fw => pure (.bv dstW (evalFPToInt dstW false fw))
        | other => throwStatic s!"Expected float in fptoui, got {other}"
    | _ => throwStatic s!"Expected integer target type in fptoui, got {toTy.print}"
  | .fptosi =>
    match toTy.scalarType with
    | .int (.concrete dstW) =>
      liftUnary (.int (.concrete dstW)) val fun
        | .float _ fw => pure (.bv dstW (evalFPToInt dstW true fw))
        | other => throwStatic s!"Expected float in fptosi, got {other}"
    | _ => throwStatic s!"Expected integer target type in fptosi, got {toTy.print}"
  | .uitofp nneg fmf =>
    match toTy.scalarType with
    | .float dstFt =>
      liftUnary (.float dstFt) val fun
        | .bv _ iv => do
          let flipZ ← drawBool
          pure (.float dstFt (evalIntToFP dstFt st.config false nneg fmf flipZ iv))
        | other => throwStatic s!"Expected integer in uitofp, got {other}"
    | _ => throwStatic s!"Expected float target type in uitofp, got {toTy.print}"
  | .sitofp fmf =>
    match toTy.scalarType with
    | .float dstFt =>
      liftUnary (.float dstFt) val fun
        | .bv _ iv => do
          let flipZ ← drawBool
          pure (.float dstFt (evalIntToFP dstFt st.config true false fmf flipZ iv))
        | other => throwStatic s!"Expected integer in sitofp, got {other}"
    | _ => throwStatic s!"Expected float target type in sitofp, got {toTy.print}"
  | .ptrtoint =>
    match toTy.scalarType with
    | .int (.concrete dstW) =>
      liftUnary (.int (.concrete dstW)) val fun
        | .ptr _ .poison => pure (.bv dstW .poison)
        | .ptr _ (.value p) => do
          let curSt ← get
          set { curSt with memory := curSt.memory.exposeProvenance p.prov }
          let resized :=
            if dstW ≥ p.addrWidth then p.addr.zeroExtend dstW else p.addr.truncate dstW
          pure (.bv dstW (.value resized))
        | other => throwStatic s!"Expected pointer in ptrtoint, got {other}"
    | _ => throwStatic s!"Expected integer target type in ptrtoint, got {toTy.print}"
  | .ptrtoaddr =>
    -- Unlike ptrtoint, ptrtoaddr does NOT expose provenance (matches `llubi::visitPtrToAddr`).
    match toTy.scalarType with
    | .int (.concrete dstW) =>
      liftUnary (.int (.concrete dstW)) val fun
        | .ptr _ .poison => pure (.bv dstW .poison)
        | .ptr _ (.value p) =>
          let resized :=
            if dstW ≥ p.addrWidth then p.addr.zeroExtend dstW else p.addr.truncate dstW
          pure (.bv dstW (.value resized))
        | other => throwStatic s!"Expected pointer in ptrtoaddr, got {other}"
    | _ => throwStatic s!"Expected integer target type in ptrtoaddr, got {toTy.print}"
  | .inttoptr =>
    match toTy.scalarType with
    | .ptr as =>
      let pw := dl.getPointerSizeInBits as
      liftUnary (.ptr as) val fun
        | .bv _ .poison => pure (.ptr as .poison)
        | .bv w (.value bv) => do
          let curSt ← get
          let prov := curSt.memory.getWildcardProvenance
          let addr := if pw ≥ w then bv.zeroExtend pw else bv.truncate pw
          pure (.ptr as (.value { prov := prov, addrWidth := pw, addr := addr }))
        | other => throwStatic s!"Expected integer in inttoptr, got {other}"
    | _ => throwStatic s!"Expected pointer target type in inttoptr, got {toTy.print}"
  | .addrspacecast =>
    match toTy.scalarType with
    | .ptr dstAs =>
      let dstW := dl.getPointerSizeInBits dstAs
      liftUnary (.ptr dstAs) val fun
        | .ptr _ .poison => pure (.ptr dstAs .poison)
        | .ptr _ (.value p) =>
          let addr := if dstW ≥ p.addrWidth then p.addr.zeroExtend dstW else p.addr.truncate dstW
          pure (.ptr dstAs (.value { prov := p.prov, addrWidth := dstW, addr := addr }))
        | other => throwStatic s!"Expected pointer in addrspacecast, got {other}"
    | _ => throwStatic s!"Expected pointer target type in addrspacecast, got {toTy.print}"

/-- Compute GEP result for concrete base type, base pointer (or vector of pointers), and evaluated index values. -/
def evalGEPValues (flags : GEPFlags) (baseTy : LlvmType 0) (ptrTy : LlvmType 0)
    (basePtrVal : RegisterValue) (idxVals : List RegisterValue) : NanoLlvmM RegisterValue := do
  let st ← get
  let dl := st.dataLayout
  let addrSpace := match ptrTy.scalarType with
    | .ptr as => as
    | _ => 0
  let idxW := dl.getIndexSizeInBits addrSpace
  let mut curRes : RegisterValue := basePtrVal
  let mut accOff : List (PoisonOr (BitVec idxW)) :=
    match basePtrVal with
    | .vector _ es => List.replicate es.length (.value (BitVec.ofNat idxW 0))
    | _ => [.value (BitVec.ofNat idxW 0)]
  let mut curTy : Option (LlvmType 0) := none
  let mut isFirst := true

  let applyScaled (idxVal : RegisterValue) (scale : Nat)
      (res : RegisterValue) (acc : List (PoisonOr (BitVec idxW))) :
      NanoLlvmM (RegisterValue × List (PoisonOr (BitVec idxW))) := do
    match res, idxVal with
    | .vector _ ptrs, .vector _ idxs =>
      if ptrs.length != idxs.length then
        throwStatic "Mismatched vector lengths in getelementptr"
      let mut newPtrs : List RegisterValue := []
      let mut newAcc : List (PoisonOr (BitVec idxW)) := []
      for i in [:ptrs.length] do
        let pOpt := match ptrs.getD i (.ptr addrSpace .poison) with
          | .ptr _ po => po
          | _ => .poison
        let iOpt := canonicalizeGEPIndex idxW flags (idxs.getD i (.bv idxW .poison))
        let aOpt := acc.getD i .poison
        let (p', a') := computeScaledPtrAdd st.memory flags pOpt iOpt scale aOpt
        newPtrs := newPtrs ++ [.ptr addrSpace p']
        newAcc := newAcc ++ [a']
      pure (.vector (.ptr addrSpace) newPtrs, newAcc)
    | .vector _ ptrs, scalarIdx =>
      let iOpt := canonicalizeGEPIndex idxW flags scalarIdx
      let mut newPtrs : List RegisterValue := []
      let mut newAcc : List (PoisonOr (BitVec idxW)) := []
      for i in [:ptrs.length] do
        let pOpt := match ptrs.getD i (.ptr addrSpace .poison) with
          | .ptr _ po => po
          | _ => .poison
        let aOpt := acc.getD i .poison
        let (p', a') := computeScaledPtrAdd st.memory flags pOpt iOpt scale aOpt
        newPtrs := newPtrs ++ [.ptr addrSpace p']
        newAcc := newAcc ++ [a']
      pure (.vector (.ptr addrSpace) newPtrs, newAcc)
    | scalarPtr, .vector _ idxs =>
      -- Splat scalar pointer to vector of index length
      let pOpt := match scalarPtr with
        | .ptr _ po => po
        | _ => .poison
      let a0 := acc.headD .poison
      let mut newPtrs : List RegisterValue := []
      let mut newAcc : List (PoisonOr (BitVec idxW)) := []
      for idx in idxs do
        let iOpt := canonicalizeGEPIndex idxW flags idx
        let (p', a') := computeScaledPtrAdd st.memory flags pOpt iOpt scale a0
        newPtrs := newPtrs ++ [.ptr addrSpace p']
        newAcc := newAcc ++ [a']
      pure (.vector (.ptr addrSpace) newPtrs, newAcc)
    | scalarPtr, scalarIdx =>
      let pOpt := match scalarPtr with
        | .ptr _ po => po
        | _ => .poison
      let iOpt := canonicalizeGEPIndex idxW flags scalarIdx
      let a0 := acc.headD .poison
      let (p', a') := computeScaledPtrAdd st.memory flags pOpt iOpt scale a0
      pure (.ptr addrSpace p', [a'])

  for idxVal in idxVals do
    if isFirst then
      let stride := dl.typeAllocSize baseTy
      let (r', a') ← applyScaled idxVal stride curRes accOff
      curRes := r'
      accOff := a'
      curTy := some baseTy
      isFirst := false
    else
      match curTy with
      | some (.struct packed fieldTys) =>
        -- Struct GEP index must be a constant integer (or splat vector of constant int)
        let fieldIdx? : Option Nat := match idxVal with
          | .bv _ (.value bv) => some bv.toNat
          | .vector _ ((.bv _ (.value bv)) :: _) => some bv.toNat
          | _ => none
        match fieldIdx? with
        | none => throwStatic "Invalid struct index in getelementptr"
        | some fi =>
          match dl.structFieldOffset? packed fieldTys fi, fieldTys[fi]? with
          | some byteOff, some fTy =>
            let offVal := RegisterValue.bv idxW (.value (BitVec.ofNat idxW byteOff))
            let (r', a') ← applyScaled offVal 1 curRes accOff
            curRes := r'
            accOff := a'
            curTy := some fTy
          | _, _ => throwStatic s!"Struct index {fi} out of bounds in getelementptr"
      | some (.array _ elemTy) =>
        let stride := dl.typeAllocSize elemTy
        let (r', a') ← applyScaled idxVal stride curRes accOff
        curRes := r'
        accOff := a'
        curTy := some elemTy
      | some (.vector _ elemTy) =>
        let stride := dl.typeAllocSize elemTy
        let (r', a') ← applyScaled idxVal stride curRes accOff
        curRes := r'
        accOff := a'
        curTy := some elemTy
      | some other =>
        throwStatic s!"Cannot index into non-aggregate type {other.print} in getelementptr"
      | none =>
        throwStatic "Internal error in getelementptr type traversal"
  pure curRes

/-! ### Expression Evaluation -/

/- Evaluate any typed LLVM expression or constant expression to a `RegisterValue`. -/
mutual
def evalTypedExp {φ : Nat} (ty : LlvmType 0) (exp : Exp φ) : NanoLlvmM RegisterValue := do
  let st ← get
  let dl := st.dataLayout
  match exp with
  | .identifier (.local_id id) =>
    match st.registers.get? (.local_id id) with
    | some val => pure val
    | none => throwStatic s!"unknown local id [%{id}]"
  | .identifier (.global_id id) =>
    match st.memory.globalAddrs.get? id with
    | some p =>
      let as := match ty with | .ptr a => a | _ => 0
      pure (.ptr as (.value p))
    | none =>
      match st.memory.funcAddrs.get? id with
      | some p =>
        let as := match ty with | .ptr a => a | _ => 0
        pure (.ptr as (.value p))
      | none => throwStatic s!"unknown global id [@{id}]"
  | .bool b =>
    match ty with
    | .int (.concrete 1) => pure (.bv 1 (.value (BitVec.ofBool b)))
    | _ => throwStatic s!"invalid type for bool literal: expected i1, found {ty.print}"
  | .int x =>
    match ty with
    | .int (.concrete w) => pure (.bv w (.value (BitVec.ofInt w x)))
    | _ => throwStatic s!"invalid type for int literal: found {ty.print}"
  | .floatBits bits =>
    match ty with
    | .float ft => pure (.float ft (.value (IEEEFloat.ofNatBits bits)))
    | _ => throwStatic s!"invalid type for float bit literal: found {ty.print}"
  | .floatDec neg m e =>
    match ty with
    | .float ft => pure (.float ft (.value (IEEEFloat.ofDecimal ft.format st.config.roundingMode neg m e)))
    | _ => throwStatic s!"invalid type for float decimal literal: found {ty.print}"
  | .null =>
    match ty with
    | .ptr as => pure (.ptr as (.value (Pointer.null dl as)))
    | _ => throwStatic s!"`null` requires pointer type, found {ty.print}"
  | .zeroinitializer =>
    pure (RegisterValue.nullOf dl ty)
  | .undef _ =>
    genUndefValue ty
  | .poison =>
    pure (RegisterValue.poisonOf ty)
  | .array elems =>
    match ty with
    | .array n elemTy =>
      if elems.length != n then
        throwStatic s!"array constant length mismatch: expected {n}, got {elems.length}"
      let vals ← evalTypedExpList elems
      pure (.array elemTy vals)
    | _ => throwStatic s!"array constant requires array type, found {ty.print}"
  | .struct packed fields =>
    match ty with
    | .struct _ fTys =>
      if fields.length != fTys.length then
        throwStatic s!"struct constant field count mismatch: expected {fTys.length}, got {fields.length}"
      let vals ← evalTypedExpList fields
      pure (.struct packed fTys vals)
    | _ => throwStatic s!"struct constant requires struct type, found {ty.print}"
  | .vector elems =>
    match ty with
    | .vector n elemTy =>
      if elems.length != n then
        throwStatic s!"vector constant length mismatch: expected {n}, got {elems.length}"
      let vals ← evalTypedExpList elems
      pure (.vector elemTy vals)
    | _ => throwStatic s!"vector constant requires vector type, found {ty.print}"
  | .splat (eTy, e) =>
    match ty with
    | .vector n elemTy =>
      let ct ← concretizeType eTy
      let sv ← evalTypedExp ct e
      pure (.vector elemTy (List.replicate n sv))
    | _ => throwStatic s!"splat constant requires vector type, found {ty.print}"
  | .gepConst flags baseTy (pTy, pExp) idxs =>
    let cBase ← concretizeType baseTy
    let cPtrTy ← concretizeType pTy
    let baseVal ← evalTypedExp cPtrTy pExp
    let idxVals ← evalTypedExpList idxs
    evalGEPValues flags cBase cPtrTy baseVal idxVals
  | .convConst op fromTy v toTy =>
    let cFrom ← concretizeType fromTy
    let cTo ← concretizeType toTy
    let val ← evalTypedExp cFrom v
    evalConversionM op cFrom val cTo
  | .binConst op cTy v1 v2 =>
    let ct ← concretizeType cTy
    let val1 ← evalTypedExp ct v1
    let val2 ← evalTypedExp ct v2
    liftBinary ct.scalarType val1 val2 fun a b =>
      match a, b with
      | .bv w1 x1, .bv w2 x2 =>
        if h : w1 = w2 then return .bv w2 (← evalIntBinaryOpM op (h ▸ x1) x2)
        else throwStatic "Mismatched integer widths in constant binary expression"
      | _, _ => throwStatic "Expected integers in constant binary expression"
termination_by sizeOf exp

def evalTypedExpList {φ : Nat} (exps : List (LlvmType φ × Exp φ)) : NanoLlvmM (List RegisterValue) :=
  match exps with
  | [] => pure []
  | (t, e) :: rest => do
    let ct ← concretizeType t
    let v ← evalTypedExp ct e
    let vs ← evalTypedExpList rest
    pure (v :: vs)
termination_by sizeOf exps
end

/-- Backwards-compatible integer expression evaluator (used in proofs with `simp_llvm`). -/
@[simp_llvm]
def evalExp {φ : Nat} {w : Nat} : Exp φ → NanoLlvmM (IntW w)
  | .identifier id => do
    let st ← get
    match st.registers.get? id with
    | some val => match val with
      | .bv w' val =>
        if h : w = w' then pure (h ▸ val)
        else throwStatic s!"invalid width: expected [{w}], found [{w'}]"
      | _ => throwStatic s!"unsupported non-integer value for integer expression"
    | none => throwStatic s!"unknown id [{id.print}]"
  | .bool b =>
    if w = 1 then pure (pure b.toNat)
    else throwStatic s!"invalid width: expected [{w}], found [1] (bool)"
  | .int x => pure (pure (BitVec.ofInt w x))
  | .null => throwStatic s!"`null` cannot be evaluated as integer"
  | .zeroinitializer => pure (pure (BitVec.ofNat w 0))
  | .undef _rawid => do
    pure (.value (← genUndef))
  | .poison => pure .poison
  | e => do
    let v ← evalTypedExp (.int (.concrete w)) e
    match v with
    | .bv w' iv =>
      if h : w = w' then pure (h ▸ iv)
      else throwStatic s!"invalid width: expected [{w}], found [{w'}]"
    | _ => throwStatic s!"expected integer value"

/-! ### Aggregate, Vector, and Memory Instruction Helpers -/

def extractValueAux (v : RegisterValue) : List Nat → NanoLlvmM RegisterValue
  | [] => pure v
  | idx :: rest =>
    match v with
    | .struct _ _ fields =>
      match fields[idx]? with
      | some f => extractValueAux f rest
      | none => throwStatic s!"extractvalue index {idx} out of bounds"
    | .array _ elems =>
      match elems[idx]? with
      | some e => extractValueAux e rest
      | none => throwStatic s!"extractvalue index {idx} out of bounds"
    | _ => throwStatic s!"extractvalue on non-aggregate value {v}"

def insertValueAux (v newVal : RegisterValue) : List Nat → NanoLlvmM RegisterValue
  | [] => pure newVal
  | idx :: rest =>
    match v with
    | .struct packed fTys fields =>
      match fields[idx]? with
      | some oldF => do
        let updated ← insertValueAux oldF newVal rest
        pure (.struct packed fTys (fields.set idx updated))
      | none => throwStatic s!"insertvalue index {idx} out of bounds"
    | .array elemTy elems =>
      match elems[idx]? with
      | some oldE => do
        let updated ← insertValueAux oldE newVal rest
        pure (.array elemTy (elems.set idx updated))
      | none => throwStatic s!"insertvalue index {idx} out of bounds"
    | _ => throwStatic s!"insertvalue on non-aggregate value {v}"

/-- Perform a verified memory transfer (`memcpy` / `memmove`). -/
def execMemTransfer (destVal srcVal lenVal : RegisterValue) (isMemMove isLibCall : Bool) :
    NanoLlvmM Unit := do
  let st ← get
  let len ← match lenVal with
    | .bv _ .poison => throwUB "memcpy/memmove with poison length"
    | .bv _ (.value bv) => pure bv.toNat
    | _ => throwStatic "Expected integer length in memcpy/memmove"
  if len == 0 then return ()
  let dstPtr ← match destVal with
    | .ptr _ .poison => throwUB "memcpy/memmove with poison destination pointer"
    | .ptr _ (.value p) => pure p
    | _ => throwStatic "Expected destination pointer in memcpy/memmove"
  let srcPtr ← match srcVal with
    | .ptr _ .poison => throwUB "memcpy/memmove with poison source pointer"
    | .ptr _ (.value p) => pure p
    | _ => throwStatic "Expected source pointer in memcpy/memmove"
  let (srcMO, srcOff) ← match st.memory.verifyMemAccess srcPtr len 1 false with
    | .ok r => pure r
    | .error e => throw e
  let (dstMO, dstOff) ← match st.memory.verifyMemAccess dstPtr len 1 true with
    | .ok r => pure r
    | .error e => throw e
  if !isMemMove && srcMO.allocId == dstMO.allocId then
    let srcEnd := srcOff + len
    let dstEnd := dstOff + len
    if srcOff < dstEnd && dstOff < srcEnd && (isLibCall || srcOff != dstOff) then
      throwUB "memcpy with overlapping source and destination"
  let copied := MemoryState.readObjectBytes srcMO srcOff len
  set { st with memory := st.memory.writeObjectBytes dstMO.allocId dstOff copied }

/-- Perform a verified `memset`. -/
def execMemSet (destVal fillVal lenVal : RegisterValue) : NanoLlvmM Unit := do
  let st ← get
  let len ← match lenVal with
    | .bv _ .poison => throwUB "memset with poison length"
    | .bv _ (.value bv) => pure bv.toNat
    | _ => throwStatic "Expected integer length in memset"
  if len == 0 then return ()
  let dstPtr ← match destVal with
    | .ptr _ .poison => throwUB "memset with poison destination pointer"
    | .ptr _ (.value p) => pure p
    | _ => throwStatic "Expected destination pointer in memset"
  let (dstMO, dstOff) ← match st.memory.verifyMemAccess dstPtr len 1 true with
    | .ok r => pure r
    | .error e => throw e
  let fillByte := match fillVal with
    | .bv _ .poison => MemByte.poison
    | .bv _ (.value bv) => MemByte.concrete (UInt8.ofNat (bv.toNat &&& 0xFF))
    | _ => MemByte.poison
  let filled := Array.replicate len fillByte
  set { st with memory := st.memory.writeObjectBytes dstMO.allocId dstOff filled }

/-! ### Built-in LLVM Intrinsics & C Memory Libcalls (mirrors `llubi`) -/

def evalIntrinsicOrLibcall? (name : String) (retTy : LlvmRetType 0) (fmf : FastMathFlags)
    (argVals : List RegisterValue) : NanoLlvmM (Option RegisterValue) := do
  let st ← get
  let dl := st.dataLayout
  -- Memory lifetime intrinsics
  if name.startsWith "llvm.lifetime.start" then
    match argVals.getLast? with
    | some (.ptr _ (.value p)) =>
      set { st with memory := st.memory.lifetimeStart st.config p }
    | _ => pure () -- poison ptr is a no-op per `loadstore_le.ll` line 39
    return some .void
  if name.startsWith "llvm.lifetime.end" then
    match argVals.getLast? with
    | some (.ptr _ (.value p)) =>
      set { st with memory := st.memory.lifetimeEnd p }
    | _ => pure ()
    return some .void
  -- Memory transfer intrinsics
  if name.startsWith "llvm.memcpy" then
    match argVals with
    | dst :: src :: len :: _ => execMemTransfer dst src len false false; return some .void
    | _ => throwStatic "llvm.memcpy requires at least 3 arguments"
  if name.startsWith "llvm.memmove" then
    match argVals with
    | dst :: src :: len :: _ => execMemTransfer dst src len true false; return some .void
    | _ => throwStatic "llvm.memmove requires at least 3 arguments"
  if name.startsWith "llvm.memset" then
    match argVals with
    | dst :: val :: len :: _ => execMemSet dst val len; return some .void
    | _ => throwStatic "llvm.memset requires at least 3 arguments"
  -- C heap library calls (`malloc`, `calloc`, `free`, `memcpy`, `memmove`, `memset`)
  if name == "malloc" then
    match argVals with
    | [.bv _ .poison] => throwUB "malloc called with poison size"
    | [.bv _ (.value sz)] =>
      let as := match retTy with | .ret (.ptr a) => a | _ => 0
      let maxAlign := if dl.getPointerABIAlign as ≥ 8 then 16 else 8
      match st.memory.allocate dl st.config sz.toNat maxAlign "malloc" as .uninitialized .heap with
      | .ok (obj, mem') =>
        set { st with memory := mem' }
        return some (.ptr as (.value (MemoryState.derivePointer dl obj)))
      | .error .outOfMemory =>
        return some (.ptr as (.value (Pointer.null dl as)))
      | .error e => throw e
    | _ => throwStatic "malloc expects 1 integer argument"
  if name == "calloc" then
    match argVals with
    | [.bv w1 (.value cnt), .bv w2 (.value sz)] =>
      let as := match retTy with | .ret (.ptr a) => a | _ => 0
      let maxAlign := if dl.getPointerABIAlign as ≥ 8 then 16 else 8
      let total := cnt.toNat * sz.toNat
      let maxW := max w1 w2
      if total ≥ (1 <<< maxW) then
        return some (.ptr as (.value (Pointer.null dl as)))
      match st.memory.allocate dl st.config total maxAlign "calloc" as .zeroed .heap with
      | .ok (obj, mem') =>
        set { st with memory := mem' }
        return some (.ptr as (.value (MemoryState.derivePointer dl obj)))
      | .error .outOfMemory =>
        return some (.ptr as (.value (Pointer.null dl as)))
      | .error e => throw e
    | _ => throwUB "calloc called with poison/invalid arguments"
  if name == "free" then
    match argVals with
    | [.ptr _ .poison] => throwUB "free called with poison pointer"
    | [.ptr as (.value p)] =>
      if p.isNull dl as then return some .void
      match st.memory.resolveObject? p with
      | none => throwUB "freeing pointer with invalid/nullary provenance"
      | some mo =>
        if p.addr.toNat != mo.baseAddr then
          throwUB s!"freeing non-base pointer {p} (base=0x{String.ofList (Nat.toDigits 16 mo.baseAddr)})"
        if mo.state == .freed then
          throwUB s!"double-free of allocation '{mo.name}'"
        if !mo.isHeap then
          throwUB s!"freeing non-heap allocation '{mo.name}'"
        set { st with memory := st.memory.freeObject mo.allocId }
        return some .void
    | _ => throwStatic "free expects 1 pointer argument"
  if name == "memcpy" then
    match argVals with
    | [dst, src, len] => execMemTransfer dst src len false true; return some dst
    | _ => throwStatic "memcpy expects 3 arguments"
  if name == "memmove" then
    match argVals with
    | [dst, src, len] => execMemTransfer dst src len true true; return some dst
    | _ => throwStatic "memmove expects 3 arguments"
  if name == "memset" then
    match argVals with
    | [dst, val, len] => execMemSet dst val len; return some dst
    | _ => throwStatic "memset expects 3 arguments"
  -- Misc intrinsics
  if name == "llvm.assume" then
    match argVals with
    | [.bv 1 (.value b)] =>
      if b == 0 then throwUB "llvm.assume(false) violated" else return some .void
    | [.bv 1 .poison] => throwUB "llvm.assume(poison) violated"
    | _ => throwStatic "llvm.assume expects i1 argument"
  if name == "llvm.donothing" then
    return some .void
  if name.startsWith "llvm.ssa.copy" || name.startsWith "llvm.expect" then
    match argVals with
    | v :: _ => return some v
    | [] => throwStatic s!"{name} requires at least 1 argument"
  -- Integer arithmetic & bit-manipulation intrinsics
  if name.startsWith "llvm.abs" then
    match argVals with
    | [v, .bv 1 (.value isIntMinPoison)] =>
      let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
      let r ← liftUnary resElemTy v fun
        | .bv w .poison => pure (.bv w .poison)
        | .bv w (.value x) =>
          if isIntMinPoison != 0 && x == BitVec.intMin w then pure (.bv w .poison)
          else pure (.bv w (.value (if x.msb then -x else x)))
        | other => throwStatic s!"Expected int in llvm.abs, got {other}"
      return some r
    | _ => throwStatic "llvm.abs expects (int, i1)"
  if name.startsWith "llvm.smax" || name.startsWith "llvm.smin" ||
     name.startsWith "llvm.umax" || name.startsWith "llvm.umin" then
    match argVals with
    | [v1, v2] =>
      let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
      let r ← liftBinary resElemTy v1 v2 fun a b =>
        match a, b with
        | .bv w1 (.value x), .bv w2 (.value y) =>
          if h : w1 = w2 then
            let x' : BitVec w2 := h ▸ x
            let pickX :=
              if name.startsWith "llvm.smax" then BitVec.sle y x'
              else if name.startsWith "llvm.smin" then BitVec.sle x' y
              else if name.startsWith "llvm.umax" then y ≤ x'
              else x' ≤ y
            pure (.bv w2 (.value (if pickX then x' else y)))
          else throwStatic "width mismatch in min/max intrinsic"
        | .bv w _, _ => pure (.bv w .poison)
        | _, _ => throwStatic "Expected int in min/max intrinsic"
      return some r
    | _ => throwStatic s!"{name} expects 2 arguments"
  if name.startsWith "llvm.ctlz" || name.startsWith "llvm.cttz" then
    match argVals with
    | [v, .bv 1 (.value isZeroPoison)] =>
      let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
      let isLeading := name.startsWith "llvm.ctlz"
      let r ← liftUnary resElemTy v fun
        | .bv w .poison => pure (.bv w .poison)
        | .bv w (.value x) =>
          if isZeroPoison != 0 && x == 0 then pure (.bv w .poison)
          else pure (.bv w (.value (if isLeading then bvCtlz x else bvCttz x)))
        | other => throwStatic s!"Expected int in ctlz/cttz, got {other}"
      return some r
    | _ => throwStatic s!"{name} expects (int, i1)"
  if name.startsWith "llvm.ctpop" || name.startsWith "llvm.bitreverse" || name.startsWith "llvm.bswap" then
    match argVals with
    | [v] =>
      let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
      let r ← liftUnary resElemTy v fun
        | .bv w .poison => pure (.bv w .poison)
        | .bv w (.value x) =>
          let res :=
            if name.startsWith "llvm.ctpop" then bvCtpop x
            else if name.startsWith "llvm.bitreverse" then bvBitReverse x
            else bvBSwap x
          pure (.bv w (.value res))
        | other => throwStatic s!"Expected int in {name}, got {other}"
      return some r
    | _ => throwStatic s!"{name} expects 1 argument"
  if name.startsWith "llvm.fshl" || name.startsWith "llvm.fshr" then
    match argVals with
    | [.bv w1 (.value a), .bv w2 (.value b), .bv w3 (.value amt)] =>
      if h1 : w1 = w3 then
        if h2 : w2 = w3 then
          let r := if name.startsWith "llvm.fshl"
            then bvFshl (h1 ▸ a) (h2 ▸ b) amt
            else bvFshr (h1 ▸ a) (h2 ▸ b) amt
          return some (.bv w3 (.value r))
        else throwStatic "width mismatch in fshl/fshr"
      else throwStatic "width mismatch in fshl/fshr"
    | [.bv w _, _, _] => return some (.bv w .poison)
    | _ => throwStatic s!"{name} expects 3 integer arguments"
  if name.startsWith "llvm.sadd.sat" || name.startsWith "llvm.uadd.sat" ||
     name.startsWith "llvm.ssub.sat" || name.startsWith "llvm.usub.sat" then
    match argVals with
    | [v1, v2] =>
      let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
      let r ← liftBinary resElemTy v1 v2 fun a b =>
        match a, b with
        | .bv w1 (.value x), .bv w2 (.value y) =>
          if h : w1 = w2 then
            let x' : BitVec w2 := h ▸ x
            let res :=
              if name.startsWith "llvm.sadd.sat" then bvSAddSat x' y
              else if name.startsWith "llvm.uadd.sat" then bvUAddSat x' y
              else if name.startsWith "llvm.ssub.sat" then bvSSubSat x' y
              else bvUSubSat x' y
            pure (.bv w2 (.value res))
          else throwStatic "width mismatch in saturating intrinsic"
        | .bv w _, _ => pure (.bv w .poison)
        | _, _ => throwStatic "Expected int in saturating intrinsic"
      return some r
    | _ => throwStatic s!"{name} expects 2 arguments"
  if name.startsWith "llvm.sadd.with.overflow" || name.startsWith "llvm.uadd.with.overflow" ||
     name.startsWith "llvm.ssub.with.overflow" || name.startsWith "llvm.usub.with.overflow" ||
     name.startsWith "llvm.smul.with.overflow" || name.startsWith "llvm.umul.with.overflow" then
    match argVals with
    | [.bv w1 (.value x), .bv w2 (.value y)] =>
      if h : w1 = w2 then
        let x' : BitVec w2 := h ▸ x
        let (res, ov) :=
          if name.startsWith "llvm.sadd" then (x' + y, BitVec.saddOverflow x' y)
          else if name.startsWith "llvm.uadd" then (x' + y, BitVec.uaddOverflow x' y)
          else if name.startsWith "llvm.ssub" then (x' - y, BitVec.ssubOverflow x' y)
          else if name.startsWith "llvm.usub" then (x' - y, BitVec.usubOverflow x' y)
          else if name.startsWith "llvm.smul" then (x' * y, BitVec.smulOverflow x' y)
          else (x' * y, BitVec.umulOverflow x' y)
        return some (.struct false [.int (.concrete w2), .int (.concrete 1)]
          [.bv w2 (.value res), .bv 1 (.value (BitVec.ofBool ov))])
      else throwStatic "width mismatch in with.overflow intrinsic"
    | [.bv w _, _] =>
      return some (.struct false [.int (.concrete w), .int (.concrete 1)] [.bv w .poison, .bv 1 .poison])
    | _ => throwStatic s!"{name} expects 2 integer arguments"
  -- Floating-point intrinsics
  if name.startsWith "llvm.fabs" then
    match argVals with
    | [v] =>
      let resElemTy := match retTy with | .ret t => t.scalarType | .void => .f32
      let r ← liftUnary resElemTy v fun
        | .float ft .poison => pure (.float ft .poison)
        | .float ft (.value flt) => do
          let flipZ ← drawBool
          let validated := handleFMF fmf true flipZ flt
          match validated with
          | .poison => pure (.float ft .poison)
          | .value f' => pure (.float ft (handleFMF fmf false false f'.abs))
        | other => throwStatic s!"Expected float in llvm.fabs, got {other}"
      return some r
    | _ => throwStatic "llvm.fabs expects 1 argument"
  if name.startsWith "llvm.copysign" then
    match argVals with
    | [v1, v2] =>
      let resElemTy := match retTy with | .ret t => t.scalarType | .void => .f32
      let r ← liftBinary resElemTy v1 v2 fun a b =>
        match a, b with
        | .float ft1 (.value m), .float ft2 (.value s) =>
          if h : ft1 = ft2 then
            pure (.float ft2 (.value ((h ▸ m).copySign s)))
          else throwStatic "Mismatched float types in llvm.copysign"
        | .float ft _, _ => pure (.float ft .poison)
        | _, _ => throwStatic "Expected floats in llvm.copysign"
      return some r
    | _ => throwStatic "llvm.copysign expects 2 arguments"
  if name.startsWith "llvm.fma" || name.startsWith "llvm.fmuladd" then
    match argVals with
    | [.float ft1 (.value a), .float ft2 (.value b), .float ft3 (.value c)] =>
      if h1 : ft1 = ft3 then
        if h2 : ft2 = ft3 then
          let res := IEEEFloat.fma st.config.roundingMode (h1 ▸ a) (h2 ▸ b) c
          let nanSign ← drawBool
          let nanPick ← drawNat
          let final := applyNaNPropagation st.config.nanMode res [h1 ▸ a, h2 ▸ b, c] nanSign nanPick
          return some (.float ft3 (handleFMF fmf false false final))
        else throwStatic "Mismatched float types in llvm.fma"
      else throwStatic "Mismatched float types in llvm.fma"
    | [.float ft _, _, _] => return some (.float ft .poison)
    | _ => throwStatic s!"{name} expects 3 float arguments"
  if name.startsWith "llvm.minimum" || name.startsWith "llvm.maximum" ||
     name.startsWith "llvm.minnum" || name.startsWith "llvm.maxnum" then
    match argVals with
    | [v1, v2] =>
      let resElemTy := match retTy with | .ret t => t.scalarType | .void => .f32
      let r ← liftBinary resElemTy v1 v2 fun a b =>
        match a, b with
        | .float ft1 (.value x), .float ft2 (.value y) =>
          if h : ft1 = ft2 then do
            let x' : IEEEFloat ft2.format := h ▸ x
            let res :=
              if name.startsWith "llvm.minimumnum" || name.startsWith "llvm.minnum" then IEEEFloat.minimumnum x' y
              else if name.startsWith "llvm.maximumnum" || name.startsWith "llvm.maxnum" then IEEEFloat.maximumnum x' y
              else if name.startsWith "llvm.minimum" then IEEEFloat.minimum x' y
              else IEEEFloat.maximum x' y
            let nanSign ← drawBool
            let nanPick ← drawNat
            let final := applyNaNPropagation st.config.nanMode res [x', y] nanSign nanPick
            pure (.float ft2 (handleFMF fmf false false final))
          else throwStatic "Mismatched float types in FP min/max"
        | .float ft _, _ => pure (.float ft .poison)
        | _, _ => throwStatic "Expected floats in FP min/max"
      return some r
    | _ => throwStatic s!"{name} expects 2 arguments"
  if name.startsWith "llvm.is.fpclass" then
    match argVals with
    | [v, .bv _ (.value mask)] =>
      let r ← liftUnary .i1 v fun
        | .float _ .poison => pure (.bv 1 .poison)
        | .float _ (.value flt) =>
          pure (.bv 1 (.value (BitVec.ofBool ((flt.fpClassBit &&& mask.toNat) != 0))))
        | other => throwStatic s!"Expected float in llvm.is.fpclass, got {other}"
      return some r
    | _ => throwStatic "llvm.is.fpclass expects (float, i32)"
  if name.startsWith "llvm.fptosi.sat" || name.startsWith "llvm.fptoui.sat" then
    match argVals with
    | [v] =>
      let isSigned := name.startsWith "llvm.fptosi.sat"
      match retTy with
      | .ret rTy =>
        match rTy.scalarType with
        | .int (.concrete dstW) =>
          let r ← liftUnary (.int (.concrete dstW)) v fun
            | .float _ .poison => pure (.bv dstW .poison)
            | .float _ (.value flt) =>
              let bv := if isSigned then flt.toSignedBitVecSat dstW else flt.toUnsignedBitVecSat dstW
              pure (.bv dstW (.value bv))
            | other => throwStatic s!"Expected float in fpto[su]i.sat, got {other}"
          return some r
        | _ => throwStatic "Expected integer return type for fpto[su]i.sat"
      | .void => throwStatic "fpto[su]i.sat cannot return void"
    | _ => throwStatic s!"{name} expects 1 argument"
  pure none

/-! ### Single Instruction Execution -/

@[simp_llvm]
def writeRegister (id : InstructionId) (val : RegisterValue) (opName : String) : NanoLlvmM Unit := do
  match id with
  | .id rid =>
    let st ← get
    set { st with registers := st.registers.insert (.local_id rid) val }
  | .void _ =>
    throwStatic s!"{opName} should be assigned to a local register id"

/--
Execute one non-phi instruction.
Accepts `callFn` for executing user-defined functions (allowing clean fuel-bounded recursion).
-/
@[simp_llvm]
def evalInstructionWithCall {φ : Nat}
    (callFn : FunctionId → List RegisterValue → NanoLlvmM RegisterValue)
    (id : InstructionId) : (@Instruction φ) → NanoLlvmM Unit
  | .intBinaryOp op t v1 v2 => do
    match t with
    | .int w =>
      let w ← expectConcreteWidth w
      let x ← @evalExp φ w v1
      let y ← @evalExp φ w v2
      let res ← evalIntBinaryOpM op x y
      writeRegister id (.bv w res) "IntBinaryOp"
    | _ =>
      let ct ← concretizeType t
      let val1 ← evalTypedExp ct v1
      let val2 ← evalTypedExp ct v2
      let res ← liftBinary ct.scalarType val1 val2 fun a b =>
        match a, b with
        | .bv w1 x1, .bv w2 x2 =>
          if h : w1 = w2 then return .bv w2 (← evalIntBinaryOpM op (h ▸ x1) x2)
          else throwStatic "Mismatched integer widths in vector binary op"
        | _, _ => throwStatic s!"Expected int or int-vector in IntBinaryOp, got [{ct.print}]"
      writeRegister id res "IntBinaryOp"
  | .floatUnaryOp op t v => do
    let ct ← concretizeType t
    let val ← evalTypedExp ct v
    let res ← liftUnary ct.scalarType val (evalFloatUnaryScalar op)
    writeRegister id res "FloatUnaryOp"
  | .floatBinaryOp op t v1 v2 => do
    let ct ← concretizeType t
    let val1 ← evalTypedExp ct v1
    let val2 ← evalTypedExp ct v2
    let res ← liftBinary ct.scalarType val1 val2 (evalFloatBinaryScalar op)
    writeRegister id res "FloatBinaryOp"
  | .icmp ss pred t v1 v2 => do
    let ct ← concretizeType t
    let val1 ← evalTypedExp ct v1
    let val2 ← evalTypedExp ct v2
    let res ← liftBinary .i1 val1 val2 (evalICmpScalar ss pred)
    writeRegister id res "icmp"
  | .fcmp fmf pred t v1 v2 => do
    let ct ← concretizeType t
    let val1 ← evalTypedExp ct v1
    let val2 ← evalTypedExp ct v2
    let res ← liftBinary .i1 val1 val2 (evalFCmpScalar fmf pred)
    writeRegister id res "fcmp"
  | .conversionOp op fromTy v toTy => do
    match op, fromTy, toTy with
    | .trunc nuw nsw, .int fromW, .int toW =>
      let fromW ← expectConcreteWidth fromW
      let toW ← expectConcreteWidth toW
      let val ← @evalExp φ fromW v
      let res : IntW toW := trunc toW val { nuw := nuw, nsw := nsw }
      writeRegister id (.bv toW res) "ConversionOp"
    | .zext nneg, .int fromW, .int toW =>
      let fromW ← expectConcreteWidth fromW
      let toW ← expectConcreteWidth toW
      let val ← @evalExp φ fromW v
      let res : IntW toW := zext toW val { nneg := nneg }
      writeRegister id (.bv toW res) "ConversionOp"
    | .sext, .int fromW, .int toW =>
      let fromW ← expectConcreteWidth fromW
      let toW ← expectConcreteWidth toW
      let val ← @evalExp φ fromW v
      let res : IntW toW := sext toW val
      writeRegister id (.bv toW res) "ConversionOp"
    | _, _, _ =>
      let cFrom ← concretizeType fromTy
      let cTo ← concretizeType toTy
      let val ← evalTypedExp cFrom v
      let res ← evalConversionM op cFrom val cTo
      writeRegister id res "ConversionOp"
  | .select fmf condTy cond valTy tv fv => do
    let cCondTy ← concretizeType condTy
    let cValTy ← concretizeType valTy
    let condVal ← evalTypedExp cCondTy cond
    let trueVal ← evalTypedExp cValTy tv
    let falseVal ← evalTypedExp cValTy fv
    let rawRes ← match condVal with
      | .bv 1 .poison => pure (RegisterValue.poisonOf cValTy)
      | .bv 1 (.value b) => pure (if b != 0 then trueVal else falseVal)
      | .vector _ condElems =>
        match trueVal, falseVal with
        | .vector elemTy tElems, .vector _ fElems => do
          let mut out : List RegisterValue := []
          for i in [:condElems.length] do
            let cLane := condElems.getD i (.bv 1 .poison)
            let picked := match cLane with
              | .bv 1 (.value b) =>
                if b != 0 then tElems.getD i (RegisterValue.poisonOf elemTy)
                else fElems.getD i (RegisterValue.poisonOf elemTy)
              | _ => RegisterValue.poisonOf elemTy
            out := out ++ [picked]
          pure (.vector elemTy out)
        | _, _ => throwStatic "Vector select requires vector operands"
      | other => throwStatic s!"Expected i1 or <N x i1> condition in select, got {other}"
    let finalRes ← if fmf.any then
      liftUnary cValTy.scalarType rawRes fun
        | .float ft (.value flt) => do
          let flipZ ← drawBool
          pure (.float ft (handleFMF fmf true flipZ flt))
        | other => pure other
    else pure rawRes
    writeRegister id finalRes "select"
  | .phi _ _ _ =>
    -- Leading phi nodes are handled in parallel on block transition (`evalBlockPhis`).
    throwStatic "Unexpected phi instruction outside block entry"
  | .alloca allocTy numEl? align? addrSpace => do
    let cAllocTy ← concretizeType allocTy
    let st ← get
    let dl := st.dataLayout
    let baseSize := dl.typeAllocSize cAllocTy
    let count ← match numEl? with
      | none => pure 1
      | some (nTy, nExp) => do
        let cnTy ← concretizeType nTy
        let nVal ← evalTypedExp cnTy nExp
        match nVal with
        | .bv _ .poison => throwUB "alloca with poison array size"
        | .bv _ (.value bv) => pure bv.toNat
        | _ => throwStatic "alloca array size must be an integer"
    let totalSize := baseSize * count
    let effAlign := align?.getD (dl.typeABIAlign cAllocTy)
    let name := match id with | .id rid => rid.ToString | .void n => s!"alloca.{n}"
    let st ← get
    match st.memory.allocate dl st.config totalSize effAlign name addrSpace .uninitialized .stack with
    | .ok (obj, mem') =>
      let ptr := MemoryState.derivePointer dl obj
      set { st with memory := mem', frameAllocas := obj.allocId :: st.frameAllocas }
      writeRegister id (.ptr addrSpace (.value ptr)) "alloca"
    | .error e => throw e
  | .load ty ptrTy ptrExp align? _isVol noundef => do
    let cTy ← concretizeType ty
    let cPtrTy ← concretizeType ptrTy
    let ptrVal ← evalTypedExp cPtrTy ptrExp
    let st ← get
    let dl := st.dataLayout
    let p ← match ptrVal with
      | .ptr _ .poison => throwUB "load through poison pointer"
      | .ptr _ (.value p) => pure p
      | other => throwStatic s!"Expected pointer in load, got {other}"
    let effAlign := align?.getD (dl.typeABIAlign cTy)
    let storeSize := dl.typeStoreSize cTy
    let (mo, offset) ← match st.memory.verifyMemAccess p storeSize effAlign false with
      | .ok r => pure r
      | .error e => throw e
    let rawBytes := MemoryState.readObjectBytes mo offset storeSize
    let (val, hasUndef) ← StateT.lift (do
      let o ← get
      let (v, u, o') := bytesToValue dl st.config rawBytes cTy o
      set o'
      pure (v, u))
    if noundef && (hasUndef || val.containsPoison) then
      throwUB "Loaded value violates !noundef (contains poison or undef bits)"
    writeRegister id val "load"
  | .store valTy valExp ptrTy ptrExp align? _isVol => do
    let cValTy ← concretizeType valTy
    let cPtrTy ← concretizeType ptrTy
    let val ← evalTypedExp cValTy valExp
    let ptrVal ← evalTypedExp cPtrTy ptrExp
    let st ← get
    let dl := st.dataLayout
    let p ← match ptrVal with
      | .ptr _ .poison => throwUB "store through poison pointer"
      | .ptr _ (.value p) => pure p
      | other => throwStatic s!"Expected pointer in store, got {other}"
    let effAlign := align?.getD (dl.typeABIAlign cValTy)
    let storeSize := dl.typeStoreSize cValTy
    let (mo, offset) ← match st.memory.verifyMemAccess p storeSize effAlign true with
      | .ok r => pure r
      | .error e => throw e
    let rawBytes := valueToBytes dl st.config val cValTy
    set { st with memory := st.memory.writeObjectBytes mo.allocId offset rawBytes }
  | .getelementptr flags baseTy ptrTy ptrExp idxs => do
    let cBase ← concretizeType baseTy
    let cPtrTy ← concretizeType ptrTy
    let baseVal ← evalTypedExp cPtrTy ptrExp
    let idxVals ← idxs.mapM fun (it, ie) => do
      evalTypedExp (← concretizeType it) ie
    let res ← evalGEPValues flags cBase cPtrTy baseVal idxVals
    writeRegister id res "getelementptr"
  | .extractvalue aggTy aggExp idxs => do
    let cAggTy ← concretizeType aggTy
    let aggVal ← evalTypedExp cAggTy aggExp
    let res ← extractValueAux aggVal idxs
    writeRegister id res "extractvalue"
  | .insertvalue aggTy aggExp valTy valExp idxs => do
    let cAggTy ← concretizeType aggTy
    let cValTy ← concretizeType valTy
    let aggVal ← evalTypedExp cAggTy aggExp
    let insVal ← evalTypedExp cValTy valExp
    let res ← insertValueAux aggVal insVal idxs
    writeRegister id res "insertvalue"
  | .extractelement vecTy vecExp idxTy idxExp => do
    let cVecTy ← concretizeType vecTy
    let cIdxTy ← concretizeType idxTy
    let vecVal ← evalTypedExp cVecTy vecExp
    let idxVal ← evalTypedExp cIdxTy idxExp
    match vecVal with
    | .vector elemTy elems =>
      let res := match idxVal with
        | .bv _ (.value bv) =>
          match elems[bv.toNat]? with
          | some e => e
          | none => RegisterValue.poisonOf elemTy
        | _ => RegisterValue.poisonOf elemTy
      writeRegister id res "extractelement"
    | other => throwStatic s!"Expected vector in extractelement, got {other}"
  | .insertelement vecTy vecExp valTy valExp idxTy idxExp => do
    let cVecTy ← concretizeType vecTy
    let cValTy ← concretizeType valTy
    let cIdxTy ← concretizeType idxTy
    let vecVal ← evalTypedExp cVecTy vecExp
    let insVal ← evalTypedExp cValTy valExp
    let idxVal ← evalTypedExp cIdxTy idxExp
    match vecVal with
    | .vector elemTy elems =>
      let res := match idxVal with
        | .bv _ (.value bv) =>
          if bv.toNat < elems.length then
            .vector elemTy (elems.set bv.toNat insVal)
          else
            RegisterValue.poisonOf cVecTy
        | _ => RegisterValue.poisonOf cVecTy
      writeRegister id res "insertelement"
    | other => throwStatic s!"Expected vector in insertelement, got {other}"
  | .shufflevector vecTy v1Exp v2Exp mask => do
    let cVecTy ← concretizeType vecTy
    let v1 ← evalTypedExp cVecTy v1Exp
    let v2 ← evalTypedExp cVecTy v2Exp
    match v1, v2 with
    | .vector elemTy es1, .vector _ es2 =>
      let len := es1.length
      let out := mask.map fun
        | none => RegisterValue.poisonOf elemTy
        | some idx =>
          if idx < len then es1.getD idx (RegisterValue.poisonOf elemTy)
          else es2.getD (idx - len) (RegisterValue.poisonOf elemTy)
      writeRegister id (.vector elemTy out) "shufflevector"
    | _, _ => throwStatic "Expected vectors in shufflevector"
  | .call retTy fmf calleeExp args retAttrs => do
    let cRetTy ← concretizeRetType retTy
    -- Evaluate all arguments and apply call-site attributes
    let mut argVals : List RegisterValue := []
    for (aTy, aExp, aAttrs) in args do
      let caTy ← concretizeType aTy
      let caAttrs ← aAttrs.mapM fun
        | .byval t => return .byval (← concretizeType t)
        | .noundef => pure .noundef
        | .nonnull => pure .nonnull
        | .align a => pure (.align a)
        | .dereferenceable b => pure (.dereferenceable b)
        | .dereferenceableOrNull b => pure (.dereferenceableOrNull b)
        | .range lo hi => pure (.range lo hi)
        | .nofpclass m => pure (.nofpclass m)
      let av ← evalTypedExp caTy aExp
      let av ← applyValueAttrs caTy av caAttrs
      argVals := argVals ++ [av]
    -- Resolve callee (direct global id or indirect function pointer)
    let calleeId : FunctionId ← match calleeExp with
      | .identifier (.global_id fid) => pure fid
      | other => do
        let st ← get
        let ptrVal ← evalTypedExp (.ptr st.dataLayout.programAddrSpace) other
        match ptrVal with
        | .ptr _ .poison => throwUB "Indirect call through poison function pointer"
        | .ptr _ (.value p) =>
          match st.memory.addrToFunc.get? p.addr.toNat with
          | some fid => pure fid
          | none => throwUB s!"Indirect call through invalid function pointer {p}"
        | _ => throwStatic "Invalid callee expression in call"
    -- Dispatch intrinsic / libcall / user-defined function
    let retVal ← match ← evalIntrinsicOrLibcall? calleeId.ToString cRetTy fmf argVals with
      | some v => pure v
      | none => callFn calleeId argVals
    -- Apply return FMF and return attributes
    let retVal ← match cRetTy with
      | .void => pure .void
      | .ret rTy => do
        let v1 ← if fmf.any then
          liftUnary rTy.scalarType retVal fun
            | .float ft (.value flt) => pure (.float ft (handleFMF fmf false false flt))
            | other => pure other
        else pure retVal
        let cRetAttrs ← retAttrs.mapM fun
          | .byval t => return .byval (← concretizeType t)
          | .noundef => pure .noundef
          | .nonnull => pure .nonnull
          | .align a => pure (.align a)
          | .dereferenceable b => pure (.dereferenceable b)
          | .dereferenceableOrNull b => pure (.dereferenceableOrNull b)
          | .range lo hi => pure (.range lo hi)
          | .nofpclass m => pure (.nofpclass m)
        applyValueAttrs rTy v1 cRetAttrs
    match cRetTy, id with
    | .void, _ => pure ()
    | .ret _, .id rid =>
      let st ← get
      set { st with registers := st.registers.insert (.local_id rid) retVal }
    | .ret _, .void _ => pure () -- LLVM allows discarding non-void call result
  | .freeze ⟨ty, exp⟩ => do
    let st ← get
    match ty with
    | .int w =>
      let w ← expectConcreteWidth w
      let val ← @evalExp φ w exp
      let res : IntW w ← match val with
        | .value a => pure (.value a)
        | .poison =>
          match st.config.freezeMode with
          | .zero => pure (.value (BitVec.ofNat w 0))
          | .nondet => do
            let b ← drawBitVec w
            pure (.value b)
      writeRegister id (.bv w res) "freeze"
    | _ =>
      let cTy ← concretizeType ty
      let val ← evalTypedExp cTy exp
      let frozen ← StateT.lift (do
        let o ← get
        let (v, o') := freezeValue st.dataLayout st.config val o
        set o'
        pure v)
      writeRegister id frozen "freeze"

/-- Execute one instruction without user-defined function calls (for straight-line code). -/
@[simp_llvm]
def evalInstruction {φ : Nat} (id : InstructionId) (instr : @Instruction φ) : NanoLlvmM Unit :=
  evalInstructionWithCall (fun fid _ => throwStatic s!"Cannot call @{fid} outside a module/definition context") id instr

@[simp_llvm]
def evalNanoLlvmCodeWithCall {φ : Nat}
    (callFn : FunctionId → List RegisterValue → NanoLlvmM RegisterValue) :
    (@Code φ) → NanoLlvmM Unit
  | .nil => pure ()
  | ⟨instr_id, instr⟩ :: t => do
    evalInstructionWithCall callFn instr_id instr
    evalNanoLlvmCodeWithCall callFn t

@[simp_llvm]
def evalNanoLlvmCode {φ : Nat} : (@Code φ) → NanoLlvmM Unit
  | .nil => pure ()
  | ⟨instr_id, instr⟩ :: t => do
    evalInstruction instr_id instr
    evalNanoLlvmCode t

/-! ### Argument Binding, Parallel Phi Evaluation, and Multi-Block CFG Execution -/

/-- Check that a runtime `RegisterValue` matches concrete `LlvmType 0` and bind function arguments. -/
@[simp_llvm]
def bindDefinitionArgs {φ : Nat} :
    List (LlvmType φ) → List RawId → List RegisterValue → NanoLlvmM Unit
  | [], [], [] => pure ()
  | [], _, _ => throwStatic "unmatched number of argument types, ids and values"
  | _, [], _ => throwStatic "unmatched number of argument types, ids and values"
  | _, _, [] => throwStatic "unmatched number of argument types, ids and values"
  | (argTy :: restTys), (argId :: restIds), (argVal :: restVals) => do
      match argTy, argVal with
      | .int wTy, .bv wVal _v =>
        let wTy ← expectConcreteWidth wTy
        if wTy = wVal then
          let st ← get
          set { st with registers := st.registers.insert (.local_id argId) argVal }
        else
          throwStatic s!"unmatched argument integer width: [{argTy.print} {argId} = {argVal}]"
      | .float ft1, .float ft2 _ =>
        if ft1 = ft2 then
          let st ← get
          set { st with registers := st.registers.insert (.local_id argId) argVal }
        else
          throwStatic s!"unmatched argument float type: [{argTy.print} {argId} = {argVal}]"
      | .ptr as1, .ptr as2 _ =>
        if as1 = as2 then
          let st ← get
          set { st with registers := st.registers.insert (.local_id argId) argVal }
        else
          throwStatic s!"unmatched argument pointer addrspace: [{argTy.print} {argId} = {argVal}]"
      | .vector n _, .vector _ elems =>
        if n = elems.length then
          let st ← get
          set { st with registers := st.registers.insert (.local_id argId) argVal }
        else
          throwStatic s!"unmatched argument vector length: [{argTy.print} {argId} = {argVal}]"
      | .array n _, .array _ elems =>
        if n = elems.length then
          let st ← get
          set { st with registers := st.registers.insert (.local_id argId) argVal }
        else
          throwStatic s!"unmatched argument array length: [{argTy.print} {argId} = {argVal}]"
      | .struct p1 fs1, .struct p2 _ fs2 =>
        if p1 = p2 && fs1.length = fs2.length then
          let st ← get
          set { st with registers := st.registers.insert (.local_id argId) argVal }
        else
          throwStatic s!"unmatched argument struct type: [{argTy.print} {argId} = {argVal}]"
      | _, _ => throwStatic s!"unsupported/mismatched argument: [{argTy.print} {argId} = {argVal}]"
      bindDefinitionArgs restTys restIds restVals

/-- Split a block's code into leading `phi` instructions and remaining regular instructions. -/
@[simp_llvm]
def splitPhis {φ : Nat} : @Code φ →
    List (InstructionId × LlvmType φ × FastMathFlags × List (Exp φ × BlockId)) × @Code φ
  | (id, .phi ty fmf incs) :: rest =>
    let (phis, body) := splitPhis rest
    ((id, ty, fmf, incs) :: phis, body)
  | code => ([], code)

/-- Evaluate all leading `phi` nodes in parallel using the predecessor's register state (matches `llubi::jumpTo`). -/
private def evalBlockPhis {φ : Nat} (predId? : Option BlockId)
    (phis : List (InstructionId × LlvmType φ × FastMathFlags × List (Exp φ × BlockId))) :
    NanoLlvmM Unit := do
  if phis.isEmpty then return ()
  let predId ← match predId? with
    | some p => pure p
    | none => throwStatic "Entry block cannot contain phi instructions"
  -- Stage 1: evaluate ALL incoming expressions BEFORE updating any register!
  let mut updates : List (RawId × RegisterValue) := []
  for (id, ty, fmf, incs) in phis do
    let rid ← match id with
      | .id r => pure r
      | .void _ => throwStatic "phi instruction must have a local register id"
    let incomingExp ← match incs.find? (fun (_, b) => b == predId) with
      | some (e, _) => pure e
      | none => throwStatic s!"phi node %{rid} has no incoming value for predecessor %{predId}"
    let cTy ← concretizeType ty
    let val ← evalTypedExp cTy incomingExp
    let val ← if fmf.any then
      liftUnary cTy.scalarType val fun
        | .float ft (.value flt) => do
          let flipZ ← drawBool
          pure (.float ft (handleFMF fmf true flipZ flt))
        | other => pure other
    else pure val
    updates := updates ++ [(rid, val)]
  -- Stage 2: commit all phi registers simultaneously
  let mut st ← get
  for (rid, val) in updates do
    st := { st with registers := st.registers.insert (.local_id rid) val }
  set st

/-- Evaluate a single return terminator cleanly. -/
@[simp_llvm]
def evalRetTerminator {φ : Nat} (retTy : LlvmRetType φ) : @Terminator φ → NanoLlvmM RegisterValue
  | .retVoid =>
    match retTy with
    | .void => pure .void
    | _ => throwStatic s!"Expected [{retTy.print}] as return type, but found void"
  | .ret ⟨.int w, exp⟩ => do
    let w ← expectConcreteWidth w
    match retTy with
    | .ret (.int retW) =>
      let retW ← expectConcreteWidth retW
      if h : retW = w then
        let exp ← @evalExp φ w exp
        pure (.bv w (h ▸ exp))
      else
        throwStatic s!"Expected [{retTy.print}] as return type, but found [i{w}]"
    | _ => throwStatic s!"Expected [{retTy.print}] as return type, but found [i{w}]"
  | .ret ⟨ty, exp⟩ => do
    let cTy ← concretizeType ty
    let cRetTy ← concretizeRetType retTy
    match cRetTy with
    | .ret rTy =>
      if rTy = cTy then evalTypedExp cTy exp
      else throwStatic s!"Expected [{rTy.print}] as return type, but found [{cTy.print}]"
    | .void => throwStatic s!"Expected void return type, but found [{cTy.print}]"
  | term => throwStatic s!"Expected ret terminator, found [{term.print}]"

/-- Free all stack allocas owned by the current frame. -/
@[simp_llvm]
def freeCurrentFrameAllocas : NanoLlvmM Unit := do
  let st ← get
  let mem' := st.frameAllocas.foldl (init := st.memory) fun m aid => m.freeObject aid
  set { st with memory := mem', frameAllocas := [] }

/--
Fuel-bounded multi-block CFG and recursive-call interpreter (mirrors `llubi::InstExecutor::runMainLoop`).
Structurally recursive on `fuel : Nat`.
-/
def evalDefinitionFuel {φ : Nat} (fuel : Nat) (defn : @Definition φ)
    (argVals : List RegisterValue) : NanoLlvmM RegisterValue :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel' + 1 =>
    match defn.prototype.type with
    | .function retTy argTys _ => do
      -- Fast path for single-block definitions with ret/retVoid (keeps straight-line proofs reducible by `simp`!)
      match defn.blocks with
      | [] => throwStatic s!"Function @{defn.prototype.name} has no basic blocks"
      | [singleBlock] =>
        let hasCalls := singleBlock.code.any fun (_, i) => match i with | .call .. => true | _ => false
        let isSimpleRet := match singleBlock.terminator.snd with | .ret _ | .retVoid => true | _ => false
        if !hasCalls && isSimpleRet && (splitPhis singleBlock.code).1.isEmpty then
          bindDefinitionArgs argTys defn.args argVals
          evalNanoLlvmCode singleBlock.code
          let ret ← evalRetTerminator retTy singleBlock.terminator.snd
          freeCurrentFrameAllocas
          pure ret
        else
          runCFG fuel' retTy argTys defn argVals singleBlock
      | entryBlock :: _ =>
        runCFG fuel' retTy argTys defn argVals entryBlock
    | ty => throwStatic s!"Expected function type for prototype, found [{ty.print}]"
termination_by (fuel, 3)
where
  runCFG (f : Nat) (retTy : LlvmRetType φ) (argTys : List (LlvmType φ))
      (defn : @Definition φ) (argVals : List RegisterValue) (entry : @Block φ) :
      NanoLlvmM RegisterValue := do
    bindDefinitionArgs argTys defn.args argVals
    -- Apply callee parameter attributes if any
    let cArgTys ← concretizeTypeList argTys
    for i in [:defn.args.length] do
      match defn.args[i]?, cArgTys[i]?, defn.prototype.argAttrs[i]? with
      | some argId, some cTy, some attrs =>
        if !attrs.isEmpty then
          let st ← get
          match st.registers.get? (.local_id argId) with
          | some v =>
            let cAttrs ← attrs.mapM fun
              | .byval t => return .byval (← concretizeType t)
              | .noundef => pure .noundef
              | .nonnull => pure .nonnull
              | .align a => pure (.align a)
              | .dereferenceable b => pure (.dereferenceable b)
              | .dereferenceableOrNull b => pure (.dereferenceableOrNull b)
              | .range lo hi => pure (.range lo hi)
              | .nofpclass m => pure (.nofpclass m)
            let v' ← applyValueAttrs cTy v cAttrs
            set { st with registers := st.registers.insert (.local_id argId) v' }
          | none => pure ()
      | _, _, _ => pure ()
    let ret ← execBlockLoop f retTy defn entry none
    freeCurrentFrameAllocas
    pure ret
  termination_by (f, 2)

  callUserFunction (f : Nat) (fid : FunctionId) (calleeArgs : List RegisterValue) :
      NanoLlvmM RegisterValue := do
    let st ← get
    if st.config.maxStackDepth != 0 && st.callDepth + 1 ≥ st.config.maxStackDepth then
      throw .stackOverflow
    match st.functions.get? fid with
    | none => throwStatic s!"Call to undefined external function @{fid}"
    | some calleeDef =>
      -- Save caller frame
      let savedRegs := st.registers
      let savedAllocas := st.frameAllocas
      let savedDepth := st.callDepth
      set { st with registers := ∅, frameAllocas := [], callDepth := savedDepth + 1 }
      let ret ← evalDefinitionFuel f calleeDef calleeArgs
      -- Restore caller frame (callee allocas already freed by callee exit)
      let stAfter ← get
      set { stAfter with registers := savedRegs, frameAllocas := savedAllocas, callDepth := savedDepth }
      pure ret
  termination_by (f, 4)

  execBlockLoop (f : Nat) (retTy : LlvmRetType φ) (defn : @Definition φ)
      (blk : @Block φ) (predId? : Option BlockId) : NanoLlvmM RegisterValue :=
    match f with
    | 0 => throw .outOfFuel
    | f' + 1 => do
      let (phis, bodyCode) := splitPhis blk.code
      evalBlockPhis predId? phis
      evalNanoLlvmCodeWithCall (callUserFunction f') bodyCode
      match blk.terminator.snd with
      | .retVoid | .ret _ =>
        evalRetTerminator retTy blk.terminator.snd
      | .br dest =>
        match defn.findBlock? dest with
        | some nextBlk => execBlockLoop f' retTy defn nextBlk (some blk.id)
        | none => throwStatic s!"Unknown branch target label %{dest}"
      | .condBr condExp tDest fDest =>
        let condVal ← evalTypedExp .i1 condExp
        match condVal with
        | .bv 1 .poison => throwUB "Branch on poison condition"
        | .bv 1 (.value b) =>
          let dest := if b != 0 then tDest else fDest
          match defn.findBlock? dest with
          | some nextBlk => execBlockLoop f' retTy defn nextBlk (some blk.id)
          | none => throwStatic s!"Unknown branch target label %{dest}"
        | other => throwStatic s!"Expected i1 condition in br, got {other}"
      | .switch ty condExp defDest cases =>
        let cTy ← concretizeType ty
        let condVal ← evalTypedExp cTy condExp
        match condVal with
        | .bv _ .poison => throwUB "Switch on poison condition"
        | .bv w (.value bv) =>
          let matched := cases.find? fun (cv, _) => BitVec.ofInt w cv == bv
          let dest := match matched with
            | some (_, lbl) => lbl
            | none => defDest
          match defn.findBlock? dest with
          | some nextBlk => execBlockLoop f' retTy defn nextBlk (some blk.id)
          | none => throwStatic s!"Unknown switch target label %{dest}"
        | other => throwStatic s!"Expected integer condition in switch, got {other}"
      | .unreachable =>
        throwUB "Executed unreachable instruction"
  termination_by (f, 1)

/-- Primary definition evaluator (preserves fast straight-line reduction for single-block definitions!). -/
@[simp_llvm]
def evalNanoLlvmDefinition {φ : Nat} (defn : @Definition φ) (argVals : List RegisterValue) :
    NanoLlvmM RegisterValue := do
  let st ← get
  match defn.prototype.type with
  | .function retTy argTys _ =>
    match defn.blocks with
    | [body] =>
      let hasCalls := body.code.any fun (_, i) => match i with | .call .. => true | _ => false
      let isSimpleRet := match body.terminator.snd with | .ret _ | .retVoid => true | _ => false
      if !hasCalls && isSimpleRet && (splitPhis body.code).1.isEmpty then
        bindDefinitionArgs argTys defn.args argVals
        evalNanoLlvmCode body.code
        let ret ← evalRetTerminator retTy body.terminator.snd
        freeCurrentFrameAllocas
        pure ret
      else
        evalDefinitionFuel st.stepsRemaining defn argVals
    | _ =>
      evalDefinitionFuel st.stepsRemaining defn argVals
  | ty => throwStatic s!"Expected function type for the prototype of definition, but found [{ty.print}]"

/-! ### Module Initialization & Execution -/

/-- Initialize all globals, declarations, and function addresses for a concrete module `TopLevel 0`. -/
def initModule (mod : @TopLevel 0) : NanoLlvmM Unit := do
  -- Pass 1: register function definitions, declarations, function pointers, and allocate global objects
  for ent in mod.entities do
    match ent with
    | .declaration decl =>
      let st ← get
      let dl := st.dataLayout
      match st.memory.allocate dl st.config 0 1 decl.name.ToString dl.programAddrSpace .zeroed .func true with
      | .ok (obj, mem') =>
        let ptr := MemoryState.derivePointer dl obj
        let mem'' := { mem' with
          funcAddrs  := mem'.funcAddrs.insert decl.name ptr
          addrToFunc := mem'.addrToFunc.insert obj.baseAddr decl.name }
        set { st with memory := mem'', declarations := st.declarations.insert decl.name decl }
      | .error e => throw e
    | .definition defn =>
      let st ← get
      let dl := st.dataLayout
      match st.memory.allocate dl st.config 0 1 defn.prototype.name.ToString dl.programAddrSpace .zeroed .func true with
      | .ok (obj, mem') =>
        let ptr := MemoryState.derivePointer dl obj
        let mem'' := { mem' with
          funcAddrs  := mem'.funcAddrs.insert defn.prototype.name ptr
          addrToFunc := mem'.addrToFunc.insert obj.baseAddr defn.prototype.name }
        set { st with memory := mem'', functions := st.functions.insert defn.prototype.name defn }
      | .error e => throw e
    | .global gv =>
      let st ← get
      let dl := st.dataLayout
      let size := dl.typeAllocSize gv.ty
      let effAlign := gv.align.getD (dl.typeABIAlign gv.ty)
      let initKind := if gv.initializer.isSome then MemInitKind.zeroed else MemInitKind.uninitialized
      match st.memory.allocate dl st.config size effAlign gv.name.ToString gv.addrSpace initKind .global gv.isConstant with
      | .ok (obj, mem') =>
        let ptr := MemoryState.derivePointer dl obj
        let mem'' := { mem' with globalAddrs := mem'.globalAddrs.insert gv.name ptr }
        set { st with memory := mem'' }
      | .error e => throw e
  -- Pass 2: evaluate and store global variable initializers (after all addresses are assigned!)
  for ent in mod.entities do
    match ent with
    | .global gv =>
      match gv.initializer with
      | none => pure ()
      | some initExp =>
        let initVal ← evalTypedExp gv.ty initExp
        let st ← get
        match st.memory.globalAddrs.get? gv.name with
        | some ptr =>
          match ptr.prov with
          | .concrete aid =>
            let rawBytes := valueToBytes st.dataLayout st.config initVal gv.ty
            set { st with memory := st.memory.writeObjectBytes aid 0 rawBytes }
          | _ => pure ()
        | none => pure ()
    | _ => pure ()

/-- Execute a named function inside a concrete module `TopLevel 0`. -/
def evalModuleFunction (mod : @TopLevel 0) (fnName : FunctionId)
    (argVals : List RegisterValue) : NanoLlvmM RegisterValue := do
  initModule mod
  let st ← get
  match st.functions.get? fnName with
  | none => throwStatic s!"Function @{fnName} not found in module"
  | some defn => evalNanoLlvmDefinition defn argVals

/-! ### Top-Level Runners -/

def runModuleFunction (mod : @TopLevel 0) (fnName : FunctionId)
    (argVals : List RegisterValue := [])
    (cfg : SemanticsConfig := .modern) (dl : DataLayout := .default64LE)
    (oracle : OracleState := default) : Except ExecError RegisterValue :=
  let initSt : NanoLlvmState := { config := cfg, dataLayout := dl, stepsRemaining := cfg.maxSteps }
  runNanoLlvmM (evalModuleFunction mod fnName argVals) initSt oracle

def runDefinitionWithConfig {φ : Nat} (ws : List.Vector Nat φ) (defn : @Definition φ)
    (args : List RegisterValue) (cfg : SemanticsConfig := .modern)
    (dl : DataLayout := .default64LE) (oracle : OracleState := default) :
    Except ExecError RegisterValue :=
  let initSt : NanoLlvmState := { config := cfg, dataLayout := dl, stepsRemaining := cfg.maxSteps }
  runNanoLlvmM (evalNanoLlvmDefinition (defn.instantiateWidths ws) args) initSt oracle

@[simp_llvm]
def evalInstantiatedDefinition {φ : Nat} (ws : List.Vector Nat φ) (defn : @Definition φ)
    (argVals : List RegisterValue) : NanoLlvmM RegisterValue :=
  evalNanoLlvmDefinition (defn.instantiateWidths ws) argVals

@[simp_llvm]
def runInstantiatedDefinition {φ : Nat} (ws : List.Vector Nat φ) (defn : @Definition φ)
    (args : List RegisterValue) (st : NanoLlvmState := default) : Except ExecError RegisterValue :=
  runNanoLlvmStateM (evalInstantiatedDefinition ws defn args) st

@[simp_llvm]
def runInstantiatedDefinitionWithUndef {φ : Nat} (ws : List.Vector Nat φ) (defn : @Definition φ)
    (args : List RegisterValue) (st : NanoLlvmState := { config := .withUndef })
    (uState : UndefState := default) : Except ExecError RegisterValue :=
  runNanoLlvmStateM (evalInstantiatedDefinition ws defn args) st uState

end LeanNanoLlvm.Semantics
