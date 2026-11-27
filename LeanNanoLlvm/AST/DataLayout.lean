import LeanNanoLlvm.AST.AST

namespace LeanNanoLlvm.AST

/-- Byte order (endianness) specified by LLVM target DataLayout. -/
inductive Endianness : Type where
  | little
  | big
deriving Repr, DecidableEq, Inhabited

/-- Pointer layout specification for an address space (`p[n]:<size>:<abi>[:<pref>[:<idx>]]`). -/
structure PointerLayout : Type where
  addrSpace : Nat := 0
  sizeBits  : Nat := 64
  abiAlign  : Nat := 8  -- in bytes
  prefAlign : Nat := 8  -- in bytes
  indexBits : Nat := 64
  nullAddr  : Nat := 0
deriving Repr, DecidableEq, Inhabited

/-- LLVM DataLayout controlling endianness, pointer/index widths, type sizes, and struct layout. -/
structure DataLayout : Type where
  endianness        : Endianness := .little
  defaultPtr        : PointerLayout := {}
  addrSpacePtrs     : List PointerLayout := []
  programAddrSpace  : Nat := 0
  allocaAddrSpace   : Nat := 0
  globalsAddrSpace  : Nat := 0
  intAligns         : List (Nat × Nat) := []
  /-- Explicit integer preferred alignments `(bitWidth, prefAlignBytes)` from `i<N>:<abi>:<pref>`. -/
  intPrefAligns     : List (Nat × Nat) := []
  targetTriple      : String := ""
deriving Repr, DecidableEq, Inhabited

namespace DataLayout

/-- Standard 64-bit little-endian layout (x86_64 / aarch64 Linux). -/
def default64LE : DataLayout := {}

/-- Standard 64-bit big-endian layout (for big-endian load/store testing). -/
def default64BE : DataLayout := { endianness := .big }

/-- Standard 32-bit little-endian layout. -/
def default32LE : DataLayout :=
  { defaultPtr := { sizeBits := 32, abiAlign := 4, prefAlign := 4, indexBits := 32 } }

@[simp]
def isLittleEndian (dl : DataLayout) : Bool := dl.endianness == .little

@[simp]
def isBigEndian (dl : DataLayout) : Bool := dl.endianness == .big

/-- Round `n` up to the next multiple of `align` (with `align ≤ 1` returning `n`). -/
@[simp]
def alignTo (n align : Nat) : Nat :=
  if align ≤ 1 then n
  else ((n + align - 1) / align) * align

/-- Next power of two ≥ `n` (with minimum 1). -/
def nextPow2 (n : Nat) : Nat :=
  if n ≤ 1 then 1
  else
    let k := Nat.log2 (n - 1)
    1 <<< (k + 1)

def getPointerLayout (dl : DataLayout) (addrSpace : Nat) : PointerLayout :=
  match dl.addrSpacePtrs.find? (fun p => p.addrSpace == addrSpace) with
  | some p => p
  | none => { dl.defaultPtr with addrSpace := addrSpace }

@[simp]
def getPointerSizeInBits (dl : DataLayout) (addrSpace : Nat := 0) : Nat :=
  (dl.getPointerLayout addrSpace).sizeBits

@[simp]
def getIndexSizeInBits (dl : DataLayout) (addrSpace : Nat := 0) : Nat :=
  (dl.getPointerLayout addrSpace).indexBits

@[simp]
def getAddressSizeInBits (dl : DataLayout) (addrSpace : Nat := 0) : Nat :=
  (dl.getPointerLayout addrSpace).sizeBits

@[simp]
def getPointerABIAlign (dl : DataLayout) (addrSpace : Nat := 0) : Nat :=
  (dl.getPointerLayout addrSpace).abiAlign

@[simp]
def getNullPtrValue (dl : DataLayout) (addrSpace : Nat := 0) : Nat :=
  (dl.getPointerLayout addrSpace).nullAddr

/-- LLVM's default integer alignment specs `(bitWidth, abiBytes, prefBytes)`
(`i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64`). -/
def defaultIntSpecs : List (Nat × Nat × Nat) :=
  [(1, 1, 1), (8, 1, 1), (16, 2, 2), (32, 4, 4), (64, 4, 8)]

/-- Integer alignment lookup following `DataLayout::getIntegerAlignment`: the spec for the
smallest specified width `≥ w`, or the largest specified width if none is larger. -/
def intAlignLookup (specs : List (Nat × Nat)) (w : Nat) : Nat :=
  -- smallest specified width ≥ w (structural fold, kernel-reducible)
  let best := specs.foldl (fun (acc : Option (Nat × Nat)) p =>
    if p.1 ≥ w then
      match acc with
      | some q => if p.1 < q.1 then some p else acc
      | none => some p
    else acc) none
  match best with
  | some (_, a) => a
  | none =>
    let largest := specs.foldl (fun (acc : Option (Nat × Nat)) p =>
      match acc with
      | some q => if p.1 > q.1 then some p else acc
      | none => some p) none
    match largest with
    | some (_, a) => a
    | none => 1

/-- Merge explicit `(width, align)` specs over LLVM's defaults (selected by `pick`). -/
def mergeIntSpecs (explicit : List (Nat × Nat)) (pick : Nat × Nat × Nat → Nat) : List (Nat × Nat) :=
  let defaults := defaultIntSpecs.filterMap fun d =>
    if explicit.any (·.1 == d.1) then none else some (d.1, pick d)
  explicit.foldl (fun acc e => if acc.any (·.1 == e.1) then acc else acc ++ [e]) [] ++ defaults

/-- Default ABI alignment (in bytes) for an integer of `w` bits (matches LLVM default DataLayout). -/
def intABIAlign (w : Nat) : Nat :=
  intAlignLookup (defaultIntSpecs.map fun (w', a, _) => (w', a)) w

/-- Default ABI alignment (in bytes) for a floating-point type. -/
def floatABIAlign : FloatType → Nat
  | .half   => 2
  | .bfloat => 2
  | .float  => 4
  | .double    => 8
  | .x86_fp80  => 16
  | .fp128     => 16
  | .ppc_fp128 => 16

mutual

/-- Compute `(sizeInBits, abiAlignInBytes)` structurally for an `LlvmType`. -/
def typeLayout (dl : DataLayout) : LlvmType → Nat × Nat
  | .int w => (w, intAlignLookup (mergeIntSpecs dl.intAligns (fun (_, a, _) => a)) w)
  | .byte w => (w, intAlignLookup (mergeIntSpecs dl.intAligns (fun (_, a, _) => a)) w)
  | .float ft => (ft.bitWidth, floatABIAlign ft)
  | .ptr as => (dl.getPointerSizeInBits as, dl.getPointerABIAlign as)
  | .vector n elem =>
      match dl.typeLayout elem with
      | (elemBits, _) =>
        let bits := n * elemBits
        let bytes := (bits + 7) / 8
        (bits, nextPow2 (max 1 bytes))
  | .array n elem =>
      match dl.typeLayout elem with
      | (elemBits, elemAlign) =>
        let elemAlloc := alignTo ((elemBits + 7) / 8) elemAlign
        (n * elemAlloc * 8, elemAlign)
  | .struct packed fields =>
      match dl.structLayoutAux packed 0 1 fields with
      | (_, rawEnd, maxAlign) =>
        let sAlign := if packed then 1 else maxAlign
        (alignTo rawEnd sAlign * 8, sAlign)
  | .named _ => (0, 1)
  | .function .. => (0, 1)

/--
Compute `(fieldByteOffsets, rawEndOffset, maxFieldABIAlign)` for a struct's fields.
For unpacked structs, each field is aligned to its ABI alignment and total size
is padded to the struct's ABI alignment (matching `llvm::StructLayout`).
-/
def structLayoutAux (dl : DataLayout) (packed : Bool) (offset maxAlign : Nat) :
    List LlvmType → List Nat × Nat × Nat
  | [] => ([], offset, maxAlign)
  | f :: fs =>
      match dl.typeLayout f with
      | (fBits, fAlign0) =>
        let fAlign := if packed then 1 else fAlign0
        let fOffset := alignTo offset fAlign
        let fAlloc := alignTo ((fBits + 7) / 8) fAlign0
        match dl.structLayoutAux packed (fOffset + fAlloc) (max maxAlign fAlign0) fs with
        | (restOffsets, endOff, restMax) =>
          (fOffset :: restOffsets, endOff, restMax)

end

/-- Compute the ABI alignment in bytes for an `LlvmType`. -/
def typeABIAlign (dl : DataLayout) (ty : LlvmType) : Nat :=
  (dl.typeLayout ty).2

/-- Compute the preferred alignment in bytes for an `LlvmType` (used by `alloca` without explicit align). -/
def typePrefAlign (dl : DataLayout) (ty : LlvmType) : Nat :=
  match ty with
  | .struct _ _ => max 8 (dl.typeABIAlign ty)
  | .int w | .byte w =>
    let explicitPref := dl.intPrefAligns ++
      (dl.intAligns.filter fun (w', _) => !(dl.intPrefAligns.any (·.1 == w')))
    max (dl.typeABIAlign ty) (intAlignLookup (mergeIntSpecs explicitPref (fun (_, _, p) => p)) w)
  | .array _ elem => max (dl.typeABIAlign ty) (typePrefAlignScalar dl elem)
  | _ => dl.typeABIAlign ty
where
  typePrefAlignScalar (dl : DataLayout) : LlvmType → Nat
    | .int w | .byte w =>
      let explicitPref := dl.intPrefAligns ++
        (dl.intAligns.filter fun (w', _) => !(dl.intPrefAligns.any (·.1 == w')))
      max (dl.typeABIAlign (.int w)) (intAlignLookup (mergeIntSpecs explicitPref (fun (_, _, p) => p)) w)
    | t => dl.typeABIAlign t

/-- Alignment `llubi` gives a global variable (`GlobalValue::getPointerAlignment`): an explicit
`align`, else for definitions `DataLayout::getPreferredAlign` (preferred type alignment, raised
to 16 bytes for globals larger than 128 bits), else (external declarations) the ABI alignment. -/
def globalAlign (dl : DataLayout) (ty : LlvmType) (explicit? : Option Nat) (isDefinition : Bool) : Nat :=
  match explicit? with
  | some a => a
  | none =>
    if isDefinition then
      let a := dl.typePrefAlign ty
      if a < 16 && (dl.typeLayout ty).1 > 128 then 16 else a
    else dl.typeABIAlign ty

/-- Exact size in bits (matches `DataLayout::getTypeSizeInBits`). -/
def typeSizeInBits (dl : DataLayout) (ty : LlvmType) : Nat :=
  (dl.typeLayout ty).1

/-- Store size in bytes (matches `DataLayout::getTypeStoreSize`). -/
def typeStoreSize (dl : DataLayout) (ty : LlvmType) : Nat :=
  (dl.typeSizeInBits ty + 7) / 8

/-- Allocation size in bytes (matches `DataLayout::getTypeAllocSize`). -/
def typeAllocSize (dl : DataLayout) (ty : LlvmType) : Nat :=
  alignTo (dl.typeStoreSize ty) (dl.typeABIAlign ty)

/-- Compute `(fieldOffsets, totalSizeInBytes)` for a struct type. -/
def structLayout (dl : DataLayout) (packed : Bool) (fields : List LlvmType) :
    List Nat × Nat :=
  match dl.structLayoutAux packed 0 1 fields with
  | (offsets, rawEnd, maxAlign) =>
    let sAlign := if packed then 1 else maxAlign
    (offsets, alignTo rawEnd sAlign)

/-- Byte offset of field `idx` in a struct (returns `none` if out of bounds). -/
def structFieldOffset? (dl : DataLayout) (packed : Bool) (fields : List LlvmType)
    (idx : Nat) : Option Nat :=
  (dl.structLayout packed fields).1[idx]?

end DataLayout

end LeanNanoLlvm.AST
