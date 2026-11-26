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

/-- Default ABI alignment (in bytes) for an integer of `w` bits (matches LLVM default DataLayout). -/
def intABIAlign (w : Nat) : Nat :=
  if w ≤ 8 then 1
  else if w ≤ 16 then 2
  else if w ≤ 32 then 4
  else 8

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
  | .int w =>
      let al := match dl.intAligns.find? (fun p => p.1 == w) with
        | some (_, a) => a
        | none => intABIAlign w
      (w, al)
  | .byte w =>
      let al := match dl.intAligns.find? (fun p => p.1 == w) with
        | some (_, a) => a
        | none => intABIAlign w
      (w, al)
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

def structFieldsMaxAlign (dl : DataLayout) (fields : List LlvmType) : Nat :=
  (dl.structLayoutAux false 0 1 fields).2.2

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
