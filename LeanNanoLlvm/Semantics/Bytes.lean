import LeanNanoLlvm.Util.Config
import LeanNanoLlvm.Util.Oracle
import LeanNanoLlvm.Util.AssocMap
import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.DataLayout
import LeanNanoLlvm.AST.Print
import LeanNanoLlvm.Semantics.Value

/-!
# Byte serialization of values

`valueToBytes` and `bytesToValue` convert between register values and memory bytes, bit by bit
and endianness-aware, as `llubi`'s `toBytes`/`fromBytes` do. Reading `undef` bytes is
nondeterministic; `BytesToValueRel` is the relational view over all oracles.
-/

namespace LeanNanoLlvm.Semantics

open AST

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

/-- Write bit `bitIdx` (0 = LSB in logical order) into `bytes` in a single pass. -/
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

/-- Structurally recursive bit writer (linear-time kernel reduction). -/
def writeBitLoop (dl : DataLayout) (offsetInBits : Nat) (bitFn : Nat → MemBit) :
    Nat → Nat → Array MemByte → Array MemByte
  | _, 0, bs => bs
  | i, rem + 1, bs =>
    match setLogicalBit dl bs (offsetInBits + i) (bitFn i) with
    | ⟨data⟩ => writeBitLoop dl offsetInBits bitFn (i + 1) rem ⟨data⟩

/-- The stored bit pattern of a float of type `ft` (`x86_fp80`: insert the explicit integer
bit 63, which is 1 unless the exponent is 0). -/
def floatStorageBits (ft : FloatType) (n : Nat) : Nat :=
  match ft with
  | .x86_fp80 =>
    let sig := n &&& ((1 <<< 63) - 1)
    let se := n >>> 63
    let intBit := if se &&& 0x7FFF == 0 then 0 else 1
    (se <<< 64) ||| (intBit <<< 63) ||| sig
  | _ => n

/-- The value of a stored bit pattern of type `ft`. `x86_fp80` is the x87 extended format, not an
IEEE interchange format: its integer bit (63) is explicit, so some encodings have no IEEE
counterpart. They are decoded as LLVM's `APFloat` does (`initFromF80LongDoubleAPInt`):
unnormals (exponent ≠ 0, integer bit 0), pseudo-infinities and pseudo-NaNs (exponent 0x7FFF,
integer bit 0) are NaNs; pseudo-denormals (exponent 0, integer bit 1) have the value of exponent 1.
Our 79-bit format (`FloatFormat.x86_fp80`, implicit integer bit) keeps a NaN's fraction but not
the integer bit, so such a NaN is re-encoded canonically (a fraction of 0 becomes the quiet NaN). -/
def floatOfStorageBits (ft : FloatType) (v : Nat) : Nat :=
  match ft with
  | .x86_fp80 =>
    let sig64 := v &&& ((1 <<< 64) - 1)
    let exp := (v >>> 64) &&& 0x7FFF
    let sign := (v >>> 79) &&& 1
    let intBit := sig64 >>> 63
    let frac := sig64 &&& ((1 <<< 63) - 1)
    let mk (e f : Nat) := (sign <<< 78) ||| (e <<< 63) ||| f
    let nan := mk 0x7FFF (if frac == 0 then 1 <<< 62 else frac)
    if exp == 0x7FFF then
      if sig64 == (1 <<< 63) then mk 0x7FFF 0   -- infinity
      else nan                                    -- NaN, pseudo-NaN, pseudo-infinity
    else if exp != 0 && intBit == 0 then nan      -- unnormal
    else if exp == 0 && intBit == 1 then mk 1 frac  -- pseudo-denormal
    else mk exp frac
  | _ => v

/-- Write a scalar value into `bytes` starting at logical `offsetInBits`. -/
def writeScalarBits (dl : DataLayout) (val : RegisterValue) (ty : LlvmType)
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
  | .byte _ bits =>
    let remBits := numBits % 8
    let startPadByte := numBits - remBits
    let padBit : MemBit :=
      if remBits == 0 then .concrete false none
      else
        let allNonPadPoison := (List.range remBits).all fun k =>
          (bits.getD (startPadByte + k) .poison).isPoison
        if allNonPadPoison then .poison else .concrete false none
    writeBitLoop dl offsetInBits
      (fun i => if i < numBits then bits.getD i .poison else padBit)
      0 totalWrite bytes
  | .float ft (.value flt) =>
    let stored := floatStorageBits ft flt.bits.toNat
    writeBitLoop dl offsetInBits
      (fun i => if i < numBits then .concrete (stored.testBit i) none else .concrete false none)
      0 totalWrite bytes
  | .ptr _ (.value p) =>
    writeBitLoop dl offsetInBits
      (fun i => if i < numBits then .concrete (p.addr.getLsbD i) (some (p.prov, i)) else .concrete false none)
      0 totalWrite bytes
  | _ => bytes

/-- `llubi`'s undef resolution on loads: walking the logical bytes of `[offsetInBits,
offsetInBits + 8·chunks)`, each byte containing undef bits takes one oracle draw (its low 8 bits
supply the undef bits); the walk stops at the first byte containing a poison bit, since the whole
value is then poison. Returns the per-byte draws (0 where no draw was needed). -/
def undefByteDraws (dl : DataLayout) (bytes : Array MemByte) (offsetInBits totalBits : Nat) :
    Nat → Nat → List Nat → OracleState → List Nat × OracleState
  | _, 0, acc, o => (acc.reverse, o)
  | k, rem + 1, acc, o =>
    let n := min 8 (totalBits - 8 * k)
    let chunk := (List.range n).map fun j => getLogicalBit dl bytes (offsetInBits + 8 * k + j)
    if chunk.any MemBit.isPoison then (acc.reverse, o)
    else if chunk.any MemBit.isUndef then
      match o.nextNat with
      | (r, o') => undefByteDraws dl bytes offsetInBits totalBits (k + 1) rem (r :: acc) o'
    else undefByteDraws dl bytes offsetInBits totalBits (k + 1) rem (0 :: acc) o

/-- Read a scalar value from `bytes` starting at logical `offsetInBits`. -/
def readScalarBits (dl : DataLayout) (cfg : SemanticsConfig) (bytes : Array MemByte)
    (ty : LlvmType) (offsetInBits : Nat) (checkPadding : Bool) (oracle : OracleState) :
    RegisterValue × Bool × OracleState :=
  match ty with
  | .byte w =>
    let remBits := w % 8
    let (bytes', padUndef) : Array MemByte × Bool :=
      if !checkPadding || remBits == 0 || bytes.size == 0 then (bytes, false)
      else
        let msbByte := getLogicalByte dl bytes (bytes.size - 1)
        if msbByte.isCanonicalPaddingByte remBits then (bytes, false)
        else (setLogicalByte dl bytes (bytes.size - 1) MemByte.poison, true)
    let rec loopByte (i : Nat) : Nat → List MemBit → Bool → List MemBit × Bool
      | 0, acc, hasU => (acc.reverse, hasU)
      | rem + 1, acc, hasU =>
        match getLogicalBit dl bytes' (offsetInBits + i) with
        | .concrete b p => loopByte (i + 1) rem (.concrete b p :: acc) hasU
        | .poison | .undef => loopByte (i + 1) rem (.poison :: acc) true
    match loopByte 0 w [] padUndef with
    | (bits, hasU) => (.byte w bits, hasU, oracle)
  | _ =>
  let numBits := dl.typeSizeInBits ty
  let endBits := if checkPadding then DataLayout.alignTo (offsetInBits + numBits) 8 else offsetInBits + numBits
  let totalRead := endBits - offsetInBits
  -- per-byte undef draws (made up front, in llubi's order); the bit loop reads them through a
  -- local oracle indexed by byte
  let pre : List Nat × OracleState :=
    if cfg.undefMode == .nondet then
      undefByteDraws dl bytes offsetInBits totalRead 0 ((totalRead + 7) / 8) [] oracle
    else ([], oracle)
  let localO : OracleState := { oracle := fun k => pre.1.getD k 0 }
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
          loop (i + 1) rem valBits true true false none padNonZero o
        | .zero =>
          loop (i + 1) rem valBits true isPoison false none padNonZero o
        | .nondet =>
          match (o.oracle (i / 8)).testBit (i % 8) with
          | false =>
            loop (i + 1) rem valBits true isPoison false none padNonZero o
          | true =>
            if inValue then
              loop (i + 1) rem (valBits + (1 <<< i)) true isPoison false none padNonZero o
            else
              loop (i + 1) rem valBits true isPoison false none true o
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
  match loop 0 totalRead 0 false false true none false localO with
  | (valBits, hasUndef, isPoison, provOk, provAcc, padNonZero, _) =>
    let o' := pre.2
    if isPoison || (checkPadding && padNonZero) then
      (RegisterValue.poisonOf ty, true, o')
    else
      let res := match ty with
        | .int w => RegisterValue.bv w (.value (BitVec.ofNat w valBits))
        | .float ft => RegisterValue.float ft (.value (IEEEFloat.ofNatBits (floatOfStorageBits ft valBits)))
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

/- Serialize a `RegisterValue` of type `ty` into `dl.typeStoreSize ty` `MemByte`s. -/
mutual
def valueToBytes (dl : DataLayout) (cfg : SemanticsConfig)
    (val : RegisterValue) : LlvmType → Array MemByte
  | .int w =>
    writeScalarBits dl val (.int w) 0 true (Array.replicate (dl.typeStoreSize (.int w)) MemByte.zero)
  | .byte w =>
    writeScalarBits dl val (.byte w) 0 true (Array.replicate (dl.typeStoreSize (.byte w)) MemByte.zero)
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
  | .function .. | .named _ => #[]

def valueToBytesStruct (dl : DataLayout) (cfg : SemanticsConfig) :
    List LlvmType → List Nat → List RegisterValue → Array MemByte → Array MemByte
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
    (bytes : Array MemByte) : LlvmType → OracleState →
    RegisterValue × Bool × OracleState
  | .int w, oracle => readScalarBits dl cfg bytes (.int w) 0 true oracle
  | .byte w, oracle => readScalarBits dl cfg bytes (.byte w) 0 true oracle
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
  | .function .., oracle | .named _, oracle => (.void, false, oracle)

def bytesToValueStruct (dl : DataLayout) (cfg : SemanticsConfig) (bytes : Array MemByte) :
    List LlvmType → List Nat → List RegisterValue → Bool → OracleState →
    List RegisterValue × Bool × OracleState
  | fTy :: restT, fOff :: restO, acc, hasU, o =>
    let subBytes := sliceBytes bytes fOff (dl.typeStoreSize fTy)
    match bytesToValue dl cfg subBytes fTy o with
    | (v, u, o') => bytesToValueStruct dl cfg bytes restT restO (v :: acc) (hasU || u) o'
  | _, _, acc, hasU, o => (acc.reverse, hasU, o)
end

/-- Relational deserialization specification (any oracle-consistent resolution of `.undef` bits). -/
def BytesToValueRel (dl : DataLayout) (cfg : SemanticsConfig) (bytes : Array MemByte)
    (ty : LlvmType) (val : RegisterValue) (hasUndef : Bool) : Prop :=
  ∃ (o : OracleState) (o' : OracleState),
    bytesToValue dl cfg bytes ty o = (val, hasUndef, o')

theorem bytesToValue_satisfies_rel {dl cfg bytes ty o val hasUndef o'}
    (h : bytesToValue dl cfg bytes ty o = (val, hasUndef, o')) :
    BytesToValueRel dl cfg bytes ty val hasUndef :=
  ⟨o, o', h⟩

end LeanNanoLlvm.Semantics
