import LeanNanoLlvm.Util.Config
import LeanNanoLlvm.Util.Undef
import LeanNanoLlvm.Util.AssocMap
import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.DataLayout
import LeanNanoLlvm.Semantics.Semantics
import LeanNanoLlvm.Semantics.FloatOps
import LeanNanoLlvm.Semantics.Memory

namespace LeanNanoLlvm.Semantics

open AST

/--
Runtime SSA value representation covering all first-class LLVM IR types
(mirrors `llubi::AnyValue`, preserving `.bv` and `.void` from the original `lean-nano-llvm`).
-/
inductive RegisterValue : Type where
  | bv     (w : Nat) (val : IntW w)
  | float  (ft : FloatType) (val : FloatW ft)
  | ptr    (addrSpace : Nat) (val : PoisonOr Pointer)
  | vector (elemTy : LlvmType 0) (elems : List RegisterValue)
  | array  (elemTy : LlvmType 0) (elems : List RegisterValue)
  | struct (packed : Bool) (fieldTys : List (LlvmType 0)) (fields : List RegisterValue)
  | void

namespace RegisterValue

mutual
def toStringAux : RegisterValue → String
  | .bv _ .poison => "poison"
  | .bv _ (.value v) => s!"{v}"
  | .float _ .poison => "poison"
  | .float ft (.value f) => s!"{ft.print} {f}"
  | .ptr _ .poison => "poison"
  | .ptr _ (.value p) => s!"{p}"
  | .vector _ elems => "<" ++ String.intercalate ", " (toStringList elems) ++ ">"
  | .array _ elems => "[" ++ String.intercalate ", " (toStringList elems) ++ "]"
  | .struct false _ fields => "{ " ++ String.intercalate ", " (toStringList fields) ++ " }"
  | .struct true _ fields => "<{ " ++ String.intercalate ", " (toStringList fields) ++ " }>"
  | .void => "void"

def toStringList : List RegisterValue → List String
  | [] => []
  | v :: vs => toStringAux v :: toStringList vs
end

instance : ToString RegisterValue := ⟨toStringAux⟩

mutual
def beq : RegisterValue → RegisterValue → Bool
  | .bv w1 v1, .bv w2 v2 =>
      if h : w1 = w2 then (h ▸ v1) == v2 else false
  | .float ft1 v1, .float ft2 v2 =>
      if h : ft1 = ft2 then (h ▸ v1) == v2 else false
  | .ptr as1 v1, .ptr as2 v2 =>
      as1 == as2 && v1 == v2
  | .vector t1 es1, .vector t2 es2 =>
      t1 == t2 && beqList es1 es2
  | .array t1 es1, .array t2 es2 =>
      t1 == t2 && beqList es1 es2
  | .struct p1 ts1 fs1, .struct p2 ts2 fs2 =>
      p1 == p2 && ts1.length == ts2.length &&
      (ts1.zip ts2).all (fun (a, b) => a == b) && beqList fs1 fs2
  | .void, .void => true
  | _, _ => false

def beqList : List RegisterValue → List RegisterValue → Bool
  | [], [] => true
  | x :: xs, y :: ys => beq x y && beqList xs ys
  | _, _ => false
end

instance : BEq RegisterValue := ⟨beq⟩

mutual
def decEq : (a b : RegisterValue) → Decidable (a = b)
  | .bv w1 v1, .bv w2 v2 =>
    if hw : w1 = w2 then by
      subst hw
      exact if hv : v1 = v2 then isTrue (by rw [hv]) else isFalse (by intro h; cases h; exact hv rfl)
    else isFalse (by intro h; cases h; exact hw rfl)
  | .float ft1 v1, .float ft2 v2 =>
    if hft : ft1 = ft2 then by
      subst hft
      exact if hv : v1 = v2 then isTrue (by rw [hv]) else isFalse (by intro h; cases h; exact hv rfl)
    else isFalse (by intro h; cases h; exact hft rfl)
  | .ptr as1 v1, .ptr as2 v2 =>
    if has : as1 = as2 then
      if hv : v1 = v2 then isTrue (by rw [has, hv]) else isFalse (by intro h; cases h; exact hv rfl)
    else isFalse (by intro h; cases h; exact has rfl)
  | .vector t1 es1, .vector t2 es2 =>
    if ht : t1 = t2 then
      match decEqList es1 es2 with
      | isTrue hes => isTrue (by rw [ht, hes])
      | isFalse hes => isFalse (by intro h; cases h; exact hes rfl)
    else isFalse (by intro h; cases h; exact ht rfl)
  | .array t1 es1, .array t2 es2 =>
    if ht : t1 = t2 then
      match decEqList es1 es2 with
      | isTrue hes => isTrue (by rw [ht, hes])
      | isFalse hes => isFalse (by intro h; cases h; exact hes rfl)
    else isFalse (by intro h; cases h; exact ht rfl)
  | .struct p1 ts1 fs1, .struct p2 ts2 fs2 =>
    if hp : p1 = p2 then
      if hts : ts1 = ts2 then
        match decEqList fs1 fs2 with
        | isTrue hfs => isTrue (by rw [hp, hts, hfs])
        | isFalse hfs => isFalse (by intro h; cases h; exact hfs rfl)
      else isFalse (by intro h; cases h; exact hts rfl)
    else isFalse (by intro h; cases h; exact hp rfl)
  | .void, .void => isTrue rfl
  | .bv _ _, .float _ _ | .bv _ _, .ptr _ _ | .bv _ _, .vector _ _ | .bv _ _, .array _ _ | .bv _ _, .struct _ _ _ | .bv _ _, .void
  | .float _ _, .bv _ _ | .float _ _, .ptr _ _ | .float _ _, .vector _ _ | .float _ _, .array _ _ | .float _ _, .struct _ _ _ | .float _ _, .void
  | .ptr _ _, .bv _ _ | .ptr _ _, .float _ _ | .ptr _ _, .vector _ _ | .ptr _ _, .array _ _ | .ptr _ _, .struct _ _ _ | .ptr _ _, .void
  | .vector _ _, .bv _ _ | .vector _ _, .float _ _ | .vector _ _, .ptr _ _ | .vector _ _, .array _ _ | .vector _ _, .struct _ _ _ | .vector _ _, .void
  | .array _ _, .bv _ _ | .array _ _, .float _ _ | .array _ _, .ptr _ _ | .array _ _, .vector _ _ | .array _ _, .struct _ _ _ | .array _ _, .void
  | .struct _ _ _, .bv _ _ | .struct _ _ _, .float _ _ | .struct _ _ _, .ptr _ _ | .struct _ _ _, .vector _ _ | .struct _ _ _, .array _ _ | .struct _ _ _, .void
  | .void, .bv _ _ | .void, .float _ _ | .void, .ptr _ _ | .void, .vector _ _ | .void, .array _ _ | .void, .struct _ _ _ =>
    isFalse (by intro h; cases h)

def decEqList : (a b : List RegisterValue) → Decidable (a = b)
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
    match decEq x y, decEqList xs ys with
    | isTrue hx, isTrue hxs => isTrue (by rw [hx, hxs])
    | isFalse hx, _ => isFalse (by intro h; cases h; exact hx rfl)
    | _, isFalse hxs => isFalse (by intro h; cases h; exact hxs rfl)
  | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq RegisterValue := decEq

instance : Inhabited RegisterValue := ⟨.void⟩

/- Produce the canonical `poison` value of concrete LLVM type `ty` (matches `AnyValue::getPoisonValue`). -/
mutual
def poisonOf : LlvmType 0 → RegisterValue
  | .int (.concrete w) => .bv w .poison
  | .float ft => .float ft .poison
  | .ptr as => .ptr as .poison
  | .vector n elem => .vector elem (List.replicate n (poisonOf elem))
  | .array n elem => .array elem (List.replicate n (poisonOf elem))
  | .struct packed fields => .struct packed fields (poisonOfList fields)
  | .function .. => .void

def poisonOfList : List (LlvmType 0) → List RegisterValue
  | [] => []
  | t :: ts => poisonOf t :: poisonOfList ts
end

/- Produce the canonical zero / null value of concrete LLVM type `ty` (matches `AnyValue::getNullValue`). -/
mutual
def nullOf (dl : DataLayout) : LlvmType 0 → RegisterValue
  | .int (.concrete w) => .bv w (.value (BitVec.ofNat w 0))
  | .float ft => .float ft (.value (IEEEFloat.zero ft.format false))
  | .ptr as => .ptr as (.value (Pointer.null dl as))
  | .vector n elem => .vector elem (List.replicate n (nullOf dl elem))
  | .array n elem => .array elem (List.replicate n (nullOf dl elem))
  | .struct packed fields => .struct packed fields (nullOfList dl fields)
  | .function .. => .void

def nullOfList (dl : DataLayout) : List (LlvmType 0) → List RegisterValue
  | [] => []
  | t :: ts => nullOf dl t :: nullOfList dl ts
end

/- Check whether `v` contains any poison scalar element (for `noundef` attribute checks). -/
mutual
def containsPoison : RegisterValue → Bool
  | .bv _ .poison => true
  | .float _ .poison => true
  | .ptr _ .poison => true
  | .vector _ elems => containsPoisonList elems
  | .array _ elems => containsPoisonList elems
  | .struct _ _ fields => containsPoisonList fields
  | _ => false

def containsPoisonList : List RegisterValue → Bool
  | [] => false
  | v :: vs => containsPoison v || containsPoisonList vs
end

/-- Check whether a scalar value is poison. -/
@[simp]
def isScalarPoison : RegisterValue → Bool
  | .bv _ .poison => true
  | .float _ .poison => true
  | .ptr _ .poison => true
  | _ => false

/-- Extract boolean tri-state (`none` = poison, `some b` = bool) from an `i1` `RegisterValue`. -/
def asBool? : RegisterValue → Option (PoisonOr Bool)
  | .bv 1 .poison => some .poison
  | .bv 1 (.value b) => some (.value (b != 0))
  | _ => none

end RegisterValue

def castRegValue? (w : Nat) : RegisterValue → Option (IntW w)
  | .bv w' v =>
    if h : w' = w then some (h ▸ v) else none
  | _ => none

/-! ### Bit-level Byte Serialization & Deserialization (`toBytes` / `fromBytes`, matches `llubi`) -/

/-- Access logical byte `idx` in endianness-aware byte array (LSB at logical index 0). -/
def getLogicalByte (dl : DataLayout) (bytes : Array MemByte) (idx : Nat) : MemByte :=
  let physIdx := if dl.isLittleEndian then idx else bytes.size - 1 - idx
  bytes.getD physIdx MemByte.poison

def setLogicalByte (dl : DataLayout) (bytes : Array MemByte) (idx : Nat) (b : MemByte) :
    Array MemByte :=
  let physIdx := if dl.isLittleEndian then idx else bytes.size - 1 - idx
  if h : physIdx < bytes.size then bytes.set physIdx b h else bytes

/-- Read bit `bitIdx` (0 = LSB in logical order) from `bytes`. -/
def getLogicalBit (dl : DataLayout) (bytes : Array MemByte) (bitIdx : Nat) : MemBit :=
  (getLogicalByte dl bytes (bitIdx / 8)).getBit (bitIdx % 8)

/-- Write bit `bitIdx` (0 = LSB in logical order) into `bytes` in a single pass (zero `bytes` duplication). -/
def setLogicalBit (dl : DataLayout) (bytes : Array MemByte) (bitIdx : Nat) (v : MemBit) :
    Array MemByte :=
  let byteIdx := bitIdx / 8
  let bitOff := bitIdx % 8
  match bytes with
  | ⟨data⟩ =>
    let physIdx := if dl.isLittleEndian then byteIdx else data.length - 1 - byteIdx
    let rec updateList : Nat → List MemByte → List MemByte
      | _, [] => []
      | 0, b :: rest => b.setBit bitOff v :: rest
      | k + 1, b :: rest => b :: updateList k rest
    ⟨updateList physIdx data⟩

/-- Structurally recursive bit writer (avoids `ForIn`/`Std.Range` and forces intermediate arrays for `O(N)` kernel reduction). -/
def writeBitLoop (dl : DataLayout) (offsetInBits : Nat) (bitFn : Nat → MemBit) :
    Nat → Nat → Array MemByte → Array MemByte
  | _, 0, bs => bs
  | i, rem + 1, bs =>
    match setLogicalBit dl bs (offsetInBits + i) (bitFn i) with
    | ⟨data⟩ => writeBitLoop dl offsetInBits bitFn (i + 1) rem ⟨data⟩

/-- Write a scalar value into `bytes` starting at logical `offsetInBits`. -/
def writeScalarBits (dl : DataLayout) (val : RegisterValue) (ty : LlvmType 0)
    (offsetInBits : Nat) (writePadding : Bool) (bytes : Array MemByte) : Array MemByte :=
  let numBits := dl.typeSizeInBits ty
  let endBits := if writePadding then DataLayout.alignTo (offsetInBits + numBits) 8 else offsetInBits + numBits
  let totalWrite := endBits - offsetInBits
  match val with
  | .bv _ .poison | .float _ .poison | .ptr _ .poison =>
    writeBitLoop dl offsetInBits (fun _ => .poison) 0 totalWrite bytes
  | .bv _ (.value bv) =>
    writeBitLoop dl offsetInBits
      (fun i => if i < numBits then .concrete (bv.getLsbD i) none else .concrete false none)
      0 totalWrite bytes
  | .float _ (.value flt) =>
    writeBitLoop dl offsetInBits
      (fun i => if i < numBits then .concrete (flt.bits.getLsbD i) none else .concrete false none)
      0 totalWrite bytes
  | .ptr _ (.value p) =>
    writeBitLoop dl offsetInBits
      (fun i => if i < numBits then .concrete (p.addr.getLsbD i) (some (p.prov, i)) else .concrete false none)
      0 totalWrite bytes
  | _ => bytes

/-- Read a scalar value from `bytes` starting at logical `offsetInBits`. -/
def readScalarBits (dl : DataLayout) (cfg : SemanticsConfig) (bytes : Array MemByte)
    (ty : LlvmType 0) (offsetInBits : Nat) (checkPadding : Bool) (oracle : OracleState) :
    RegisterValue × Bool × OracleState :=
  let numBits := dl.typeSizeInBits ty
  let endBits := if checkPadding then DataLayout.alignTo (offsetInBits + numBits) 8 else offsetInBits + numBits
  let totalRead := endBits - offsetInBits
  let rec loop (i : Nat) : Nat → Nat → Bool → Bool → Bool → Option Provenance → Bool → OracleState →
      Nat × Bool × Bool × Bool × Option Provenance × Bool × OracleState
    | 0, valBits, hasUndef, isPoison, provOk, provAcc, padNonZero, o =>
      (valBits, hasUndef, isPoison, provOk, provAcc, padNonZero, o)
    | rem + 1, valBits, hasUndef, isPoison, provOk, provAcc, padNonZero, o =>
      let mb := getLogicalBit dl bytes (offsetInBits + i)
      let inValue := i < numBits
      match mb with
      | .poison =>
        loop (i + 1) rem valBits true true false none padNonZero o
      | .undef =>
        match cfg.undefMode with
        | .disabled =>
          -- When undef is disabled, any undef bit behaves as poison.
          loop (i + 1) rem valBits true true false none padNonZero o
        | .zero =>
          loop (i + 1) rem valBits true isPoison false none padNonZero o
        | .nondet =>
          match o.nextBool with
          | (b, o') =>
            match b with
            | false =>
              loop (i + 1) rem valBits true isPoison false none padNonZero o'
            | true =>
              if inValue then
                loop (i + 1) rem (valBits + (1 <<< i)) true isPoison false none padNonZero o'
              else
                loop (i + 1) rem valBits true isPoison false none true o'
      | .concrete b provBit =>
        let nextProv : Bool × Option Provenance :=
          if !inValue then (provOk, provAcc)
          else if !provOk then (false, none)
          else match provBit with
            | none => (false, none)
            | some (p, bitPos) =>
              if bitPos != i then (false, none)
              else match provAcc with
                | none => (true, some p)
                | some p0 => if p0 == p then (true, some p0) else (false, none)
        match nextProv with
        | (provOk', provAcc') =>
          match b with
          | false =>
            loop (i + 1) rem valBits hasUndef isPoison provOk' provAcc' padNonZero o
          | true =>
            if inValue then
              loop (i + 1) rem (valBits + (1 <<< i)) hasUndef isPoison provOk' provAcc' padNonZero o
            else
              loop (i + 1) rem valBits hasUndef isPoison provOk' provAcc' true o
  match loop 0 totalRead 0 false false true none false oracle with
  | (valBits, hasUndef, isPoison, provOk, provAcc, padNonZero, o') =>
    if isPoison || (checkPadding && padNonZero) then
      (RegisterValue.poisonOf ty, true, o')
    else
      let res := match ty with
        | .int (.concrete w) => RegisterValue.bv w (.value (BitVec.ofNat w valBits))
        | .float ft => RegisterValue.float ft (.value (IEEEFloat.ofNatBits valBits))
        | .ptr as =>
          let prov := if provOk then provAcc.getD .nullary else .nullary
          RegisterValue.ptr as (.value { prov := prov, addrWidth := numBits, addr := BitVec.ofNat numBits valBits })
        | _ => RegisterValue.poisonOf ty
      (res, hasUndef, o')

/-- Slice `[start, start + len)` out of an `Array MemByte`. -/
private def sliceBytes (bytes : Array MemByte) (start len : Nat) : Array MemByte :=
  Array.ofFn (n := len) fun i => bytes.getD (start + i.val) MemByte.poison

/-- Overwrite `dst` starting at `offset` with `src`. -/
private def blitBytes (dst : Array MemByte) (offset : Nat) (src : Array MemByte) : Array MemByte :=
  let rec go (i : Nat) : Nat → Array MemByte → Array MemByte
    | 0, out => out
    | rem + 1, out =>
      let idx := offset + i
      let out' := if h : idx < out.size then out.set idx (src.getD i MemByte.poison) h else out
      go (i + 1) rem out'
  go 0 src.size dst

/- Serialize a `RegisterValue` of concrete type `ty` into `dl.typeStoreSize ty` `MemByte`s. -/
mutual
def valueToBytes (dl : DataLayout) (cfg : SemanticsConfig)
    (val : RegisterValue) : LlvmType 0 → Array MemByte
  | .int w =>
    writeScalarBits dl val (.int w) 0 true (Array.replicate (dl.typeStoreSize (.int w)) MemByte.zero)
  | .float ft =>
    writeScalarBits dl val (.float ft) 0 true (Array.replicate (dl.typeStoreSize (.float ft)) MemByte.zero)
  | .ptr as =>
    writeScalarBits dl val (.ptr as) 0 true (Array.replicate (dl.typeStoreSize (.ptr as)) MemByte.zero)
  | .vector n elemTy =>
    let storeSize := dl.typeStoreSize (.vector n elemTy)
    let initBytes := Array.replicate storeSize MemByte.zero
    let elemBits := dl.typeSizeInBits elemTy
    let vecBits := n * elemBits
    let elems := match val with
      | .vector _ es => es
      | _ => List.replicate n (RegisterValue.poisonOf elemTy)
    let rec writeElems (idx : Nat) : Nat → Array MemByte → Array MemByte
      | 0, arr => arr
      | rem + 1, arr =>
        let eVal := elems.getD idx (RegisterValue.poisonOf elemTy)
        let bitOff := if dl.isLittleEndian then idx * elemBits else vecBits - elemBits - idx * elemBits
        writeElems (idx + 1) rem (writeScalarBits dl eVal elemTy bitOff false arr)
    let bs := writeElems 0 n initBytes
    -- Canonicalize padding bits in the MSB logical byte (matches `llubi::Context::toBytes`)
    let remBits := vecBits % 8
    if remBits == 0 || storeSize == 0 then bs
    else
      let msbByte := getLogicalByte dl bs (storeSize - 1)
      let allNonPadPoison := (List.range remBits).all fun b => (msbByte.getBit b).isPoison
      let padBit : MemBit := if allNonPadPoison then .poison else .concrete false none
      let msbByte' := (List.range (8 - remBits)).foldl (init := msbByte) fun acc k =>
        acc.setBit (remBits + k) padBit
      setLogicalByte dl bs (storeSize - 1) msbByte'
  | .array n elemTy =>
    let storeSize := dl.typeStoreSize (.array n elemTy)
    let stride := dl.typeAllocSize elemTy
    let elemStore := dl.typeStoreSize elemTy
    let elems := match val with
      | .array _ es => es
      | _ => List.replicate n (RegisterValue.poisonOf elemTy)
    let initArr := Array.replicate storeSize (MemByte.uninitFor cfg)
    (List.range n).foldl (init := initArr) fun arr idx =>
      let eVal := elems.getD idx (RegisterValue.poisonOf elemTy)
      let eBytes := valueToBytes dl cfg eVal elemTy
      blitBytes arr (idx * stride) (sliceBytes eBytes 0 elemStore)
  | .struct packed fieldTys =>
    let storeSize := dl.typeStoreSize (.struct packed fieldTys)
    match dl.structLayout packed fieldTys with
    | (offsets, _) =>
      let fields := match val with
        | .struct _ _ fs => fs
        | _ => fieldTys.map RegisterValue.poisonOf
      let arr := Array.replicate storeSize (MemByte.uninitFor cfg)
      valueToBytesStruct dl cfg fieldTys offsets fields arr
  | .function .. => #[]

def valueToBytesStruct (dl : DataLayout) (cfg : SemanticsConfig) :
    List (LlvmType 0) → List Nat → List RegisterValue → Array MemByte → Array MemByte
  | fTy :: restT, fOff :: restO, fVals, arr =>
    match fVals with
    | v :: vs =>
      let fBytes := valueToBytes dl cfg v fTy
      let arr' := blitBytes arr fOff fBytes
      valueToBytesStruct dl cfg restT restO vs arr'
    | [] =>
      let fBytes := valueToBytes dl cfg (RegisterValue.poisonOf fTy) fTy
      let arr' := blitBytes arr fOff fBytes
      valueToBytesStruct dl cfg restT restO [] arr'
  | _, _, _, arr => arr
end

/- Deserialize `dl.typeStoreSize ty` `MemByte`s into `(value, containsUndefOrPoison, nextOracle)`. -/
mutual
def bytesToValue (dl : DataLayout) (cfg : SemanticsConfig)
    (bytes : Array MemByte) : LlvmType 0 → OracleState →
    RegisterValue × Bool × OracleState
  | .int w, oracle => readScalarBits dl cfg bytes (.int w) 0 true oracle
  | .float ft, oracle => readScalarBits dl cfg bytes (.float ft) 0 true oracle
  | .ptr as, oracle => readScalarBits dl cfg bytes (.ptr as) 0 true oracle
  | .vector n elemTy, oracle =>
    let elemBits := dl.typeSizeInBits elemTy
    let vecBits := n * elemBits
    let remBits := vecBits % 8
    let prepBytes : Array MemByte × Bool :=
      if remBits == 0 || bytes.size == 0 then (bytes, false)
      else
        let msbByte := getLogicalByte dl bytes (bytes.size - 1)
        if msbByte.isCanonicalPaddingByte remBits then (bytes, false)
        else (setLogicalByte dl bytes (bytes.size - 1) MemByte.poison, true)
    match prepBytes with
    | (bytes', padUndef) =>
      let rec readElems (idx : Nat) : Nat → List RegisterValue → Bool → OracleState →
          List RegisterValue × Bool × OracleState
        | 0, acc, hasU, o => (acc.reverse, hasU, o)
        | rem + 1, acc, hasU, o =>
          let bitOff := if dl.isLittleEndian then idx * elemBits else vecBits - elemBits - idx * elemBits
          match readScalarBits dl cfg bytes' elemTy bitOff false o with
          | (v, u, o') => readElems (idx + 1) rem (v :: acc) (hasU || u) o'
      match readElems 0 n [] padUndef oracle with
      | (elems, hasU, o') => (.vector elemTy elems, hasU, o')
  | .array n elemTy, oracle =>
    let stride := dl.typeAllocSize elemTy
    let elemStore := dl.typeStoreSize elemTy
    match (List.range n).foldl (init := ([], false, oracle)) fun (acc, hasU, o) idx =>
        let subBytes := sliceBytes bytes (idx * stride) elemStore
        match bytesToValue dl cfg subBytes elemTy o with
        | (v, u, o') => (v :: acc, hasU || u, o') with
    | (revElems, hasU, o') => (.array elemTy revElems.reverse, hasU, o')
  | .struct packed fieldTys, oracle =>
    match dl.structLayout packed fieldTys with
    | (offsets, _) =>
      match bytesToValueStruct dl cfg bytes fieldTys offsets [] false oracle with
      | (fields, hasU, o') => (.struct packed fieldTys fields, hasU, o')
  | .function .., oracle => (.void, false, oracle)

def bytesToValueStruct (dl : DataLayout) (cfg : SemanticsConfig) (bytes : Array MemByte) :
    List (LlvmType 0) → List Nat → List RegisterValue → Bool → OracleState →
    List RegisterValue × Bool × OracleState
  | fTy :: restT, fOff :: restO, acc, hasU, o =>
    let subBytes := sliceBytes bytes fOff (dl.typeStoreSize fTy)
    match bytesToValue dl cfg subBytes fTy o with
    | (v, u, o') => bytesToValueStruct dl cfg bytes restT restO (v :: acc) (hasU || u) o'
  | _, _, acc, hasU, o => (acc.reverse, hasU, o)
end

/-! ### Freezing Any Value (faithful to LLVM + `llubi::Context::freeze`) -/

private def drawFreezeBits (cfg : SemanticsConfig) (w : Nat) (o : OracleState) : BitVec w × OracleState :=
  match cfg.freezeMode with
  | .zero => (BitVec.ofNat w 0, o)
  | .nondet => o.nextBitVec w

mutual
def freezeValue (dl : DataLayout) (cfg : SemanticsConfig) :
    RegisterValue → OracleState → RegisterValue × OracleState
  | .bv w .poison, oracle =>
    match drawFreezeBits cfg w oracle with
    | (bits, o') => (.bv w (.value bits), o')
  | .bv w (.value v), oracle => (.bv w (.value v), oracle)
  | .float ft .poison, oracle =>
    match drawFreezeBits cfg ft.bitWidth oracle with
    | (bits, o') => (.float ft (.value (IEEEFloat.ofBits bits)), o')
  | .float ft (.value f), oracle => (.float ft (.value f), oracle)
  | .ptr as .poison, oracle =>
    let pw := dl.getPointerSizeInBits as
    match drawFreezeBits cfg pw oracle with
    | (bits, o') => (.ptr as (.value { prov := .nullary, addrWidth := pw, addr := bits }), o')
  | .ptr as (.value p), oracle => (.ptr as (.value p), oracle)
  | .vector elemTy elems, oracle =>
    match freezeValueList dl cfg elems oracle with
    | (elems', o') => (.vector elemTy elems', o')
  | .array elemTy elems, oracle =>
    match freezeValueList dl cfg elems oracle with
    | (elems', o') => (.array elemTy elems', o')
  | .struct packed fTys fields, oracle =>
    match freezeValueList dl cfg fields oracle with
    | (fields', o') => (.struct packed fTys fields', o')
  | .void, oracle => (.void, oracle)

def freezeValueList (dl : DataLayout) (cfg : SemanticsConfig) :
    List RegisterValue → OracleState → List RegisterValue × OracleState
  | [], oracle => ([], oracle)
  | v :: vs, oracle =>
    match freezeValue dl cfg v oracle with
    | (v', o1) =>
      match freezeValueList dl cfg vs o1 with
      | (vs', o2) => (v' :: vs', o2)
end

/-! ### GEP Pointer Arithmetic (mirrors `llubi::Context::computeGEP`) -/

/-- Sign-extend or truncate GEP index to `idxWidth`, checking `nusw`/`nuw` truncation overflow. -/
def canonicalizeGEPIndex (idxWidth : Nat) (flags : GEPFlags) (idxVal : RegisterValue) :
    PoisonOr (BitVec idxWidth) :=
  match idxVal with
  | .bv w (.value bv) =>
    if h : w = idxWidth then .value (h ▸ bv)
    else if w > idxWidth then
      let tr := bv.truncate idxWidth
      if flags.hasNUSW && tr.signExtend w != bv then .poison
      else if flags.nuw && tr.zeroExtend w != bv then .poison
      else .value tr
    else
      .value (bv.signExtend idxWidth)
  | _ => .poison

/-- Compute one GEP pointer-add step `(ptr, offset, accumulatedOffset)` with `inbounds`/`nusw`/`nuw`. -/
def computePtrAddStep (mem : MemoryState) (flags : GEPFlags)
    (ptr : Pointer) {idxW : Nat} (offset : BitVec idxW) (accOff : PoisonOr (BitVec idxW)) :
    PoisonOr Pointer × PoisonOr (BitVec idxW) :=
  if offset == 0 then
    (.value ptr, accOff)
  else
    let oldIdx : BitVec idxW := ptr.addr.truncate idxW
    let newIdx := oldIdx + offset
    -- nuw check: unsigned overflow on index addition
    if flags.nuw && BitVec.uaddOverflow oldIdx offset then
      (.poison, .poison)
    else
      -- nusw check: unsigned base + signed offset must not wrap index space
      let nuswBad := flags.hasNUSW &&
        (if !offset.msb then newIdx < oldIdx else oldIdx < newIdx)
      if nuswBad then
        (.poison, .poison)
      else
        -- Insert low `idxW` bits into full pointer address
        let highBits : Nat := (ptr.addr.toNat >>> idxW) <<< idxW
        let newAddrNat := highBits ||| newIdx.toNat
        let newAddr := BitVec.ofNat ptr.addrWidth newAddrNat
        -- Check `inbounds` on underlying object (both old and new address must be in [base, base+size])
        let inboundsCheck : Bool × Provenance :=
          if !flags.inbounds then (true, ptr.prov)
          else match mem.resolveObject? ptr with
            | none => (false, ptr.prov)
            | some mo =>
              if mo.inBounds ptr.addr.toNat && mo.inBounds newAddr.toNat then
                let prov' := match ptr.prov with
                  | .wildcard g none => Provenance.wildcard g (some mo.allocId)
                  | p => p
                (true, prov')
              else (false, ptr.prov)
        match inboundsCheck with
        | (false, _) => (.poison, .poison)
        | (true, narrowedProv) =>
          let newAcc : PoisonOr (BitVec idxW) := match accOff with
            | .poison => .poison
            | .value a =>
              let s := a + offset
              if flags.hasNUSW && BitVec.saddOverflow a offset then .poison
              else if flags.nuw && BitVec.uaddOverflow a offset then .poison
              else .value s
          match newAcc with
          | .poison => (.poison, .poison)
          | .value _ =>
            (.value ⟨narrowedProv, ptr.addrWidth, newAddr⟩, newAcc)

/-- Compute scaled pointer add `ptr + idx * scale`. -/
def computeScaledPtrAdd (mem : MemoryState) (flags : GEPFlags)
    (ptrOpt : PoisonOr Pointer) {idxW : Nat} (idxOpt : PoisonOr (BitVec idxW))
    (scale : Nat) (accOff : PoisonOr (BitVec idxW)) :
    PoisonOr Pointer × PoisonOr (BitVec idxW) :=
  match ptrOpt, idxOpt with
  | .value ptr, .value idx =>
    if scale == 0 then (.value ptr, accOff)
    else if scale == 1 then computePtrAddStep mem flags ptr idx accOff
    else
      let scaleBV := BitVec.ofNat idxW scale
      let scaled := idx * scaleBV
      if flags.hasNUSW && BitVec.smulOverflow idx scaleBV then (.poison, .poison)
      else if flags.nuw && BitVec.umulOverflow idx scaleBV then (.poison, .poison)
      else computePtrAddStep mem flags ptr scaled accOff
  | _, _ => (.poison, .poison)

/-! ### Execution State & Monad -/

/-- Complete machine state for executing LLVM IR (registers, memory, module table, config, fuel). -/
structure NanoLlvmState : Type where
  registers      : AssocMap AST.Identifier RegisterValue := ∅
  memory         : MemoryState := {}
  config         : SemanticsConfig := .modern
  dataLayout     : DataLayout := .default64LE
  frameAllocas   : List AllocId := []
  functions      : AssocMap AST.FunctionId (@AST.Definition 0) := ∅
  declarations   : AssocMap AST.FunctionId (@AST.Declaration 0) := ∅
  stepsRemaining : Nat := 10000
  callDepth      : Nat := 0

instance : Inhabited NanoLlvmState := ⟨{}⟩

namespace NanoLlvmState

/-- Pattern-matching state updaters (evaluate `st` once via `casesOn` instead of `9×` projection duplication in Lean's kernel). -/
@[simp, simp_llvm]
def insertRegister : NanoLlvmState → AST.Identifier → RegisterValue → NanoLlvmState
  | ⟨regs, mem, cfg, dl, allocas, fns, decls, steps, depth⟩, k, v =>
    ⟨regs.insert k v, mem, cfg, dl, allocas, fns, decls, steps, depth⟩

@[simp, simp_llvm]
def withMemory : NanoLlvmState → MemoryState → NanoLlvmState
  | ⟨regs, _, cfg, dl, allocas, fns, decls, steps, depth⟩, mem =>
    ⟨regs, mem, cfg, dl, allocas, fns, decls, steps, depth⟩

@[simp, simp_llvm]
def withMemoryAndAllocas : NanoLlvmState → MemoryState → List AllocId → NanoLlvmState
  | ⟨regs, _, cfg, dl, _, fns, decls, steps, depth⟩, mem, allocas =>
    ⟨regs, mem, cfg, dl, allocas, fns, decls, steps, depth⟩

@[simp, simp_llvm]
def withFrame : NanoLlvmState → AssocMap AST.Identifier RegisterValue → List AllocId → Nat → NanoLlvmState
  | ⟨_, mem, cfg, dl, _, fns, decls, steps, _⟩, regs, allocas, depth =>
    ⟨regs, mem, cfg, dl, allocas, fns, decls, steps, depth⟩

@[simp, simp_llvm]
def addDeclaration : NanoLlvmState → MemoryState → AST.FunctionId → (@AST.Declaration 0) → NanoLlvmState
  | ⟨regs, _, cfg, dl, allocas, fns, decls, steps, depth⟩, mem, fid, decl =>
    ⟨regs, mem, cfg, dl, allocas, fns, decls.insert fid decl, steps, depth⟩

@[simp, simp_llvm]
def addFunction : NanoLlvmState → MemoryState → AST.FunctionId → (@AST.Definition 0) → NanoLlvmState
  | ⟨regs, _, cfg, dl, allocas, fns, decls, steps, depth⟩, mem, fid, defn =>
    ⟨regs, mem, cfg, dl, allocas, fns.insert fid defn, decls, steps, depth⟩

end NanoLlvmState

/-- Legacy-compatible alias for finite supply chain. -/
abbrev UndefChain : Type := SupplyChain Nat
abbrev UndefState : Type := SupplyState Nat

/-- Primary execution monad: state + total nondeterminism oracle + structured `ExecError` (UB vs static vs resource). -/
abbrev NanoLlvmM (retTy : Type) := StateT NanoLlvmState (StateT OracleState (Except ExecError)) retTy

/-- Backwards-compatible execution monad alias (`NanoLlvmStateM`). -/
abbrev NanoLlvmStateM (retTy : Type) := NanoLlvmM retTy

@[simp]
def runNanoLlvmM {α : Type} (m : NanoLlvmM α)
    (st : NanoLlvmState := default) (oState : OracleState := default) : Except ExecError α :=
  ((m.run st).run oState).map (fun ((a, _), _) => a)

@[simp]
def runNanoLlvmMWithState {α : Type} (m : NanoLlvmM α)
    (st : NanoLlvmState := default) (oState : OracleState := default) :
    Except ExecError ((α × NanoLlvmState) × OracleState) :=
  (m.run st).run oState

/-- Convenience runner accepting a legacy `UndefState` (list supply). -/
@[simp]
def runNanoLlvmStateM {α : Type} (m : NanoLlvmStateM α)
    (st : NanoLlvmState := default) (uState : UndefState := default) : Except ExecError α :=
  let oState : OracleState := ⟨NondetOracle.ofList uState.supplyChain, uState.supplyIndex⟩
  runNanoLlvmM m st oState

@[simp]
def runNanoLlvmStateMWithState {α : Type} (m : NanoLlvmStateM α)
    (st : NanoLlvmState := default) (uState : UndefState := default) :
    Except ExecError ((α × NanoLlvmState) × OracleState) :=
  let oState : OracleState := ⟨NondetOracle.ofList uState.supplyChain, uState.supplyIndex⟩
  runNanoLlvmMWithState m st oState

@[simp, simp_llvm]
theorem except_map_pure {ε α β : Type} (f : α → β) (a : α) :
    Except.map f (pure a : Except ε α) = .ok (f a) := rfl

@[simp, simp_llvm]
theorem except_map_ok {ε α β : Type} (f : α → β) (a : α) :
    Except.map f (.ok a : Except ε α) = .ok (f a) := rfl

@[simp, simp_llvm]
theorem except_map_error {ε α β : Type} (f : α → β) (e : ε) :
    Except.map f (.error e : Except ε α) = .error e := rfl

@[simp, simp_llvm]
theorem except_map_throw {ε α β : Type} (f : α → β) (e : ε) :
    Except.map f (throw e : Except ε α) = .error e := rfl

@[simp, simp_llvm]
theorem functor_map_except_ok {ε α β : Type} (f : α → β) (a : α) :
    f <$> (Except.ok a : Except ε α) = .ok (f a) := rfl

@[simp, simp_llvm]
theorem functor_map_except_pure {ε α β : Type} (f : α → β) (a : α) :
    f <$> (pure a : Except ε α) = .ok (f a) := rfl

@[simp, simp_llvm]
theorem functor_map_except_throw {ε α β : Type} (f : α → β) (e : ε) :
    f <$> (throw e : Except ε α) = .error e := rfl

end LeanNanoLlvm.Semantics
