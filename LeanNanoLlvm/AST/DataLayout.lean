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
  | .double => 8
  | .fp128  => 16

mutual

/-- Compute the ABI alignment in bytes for a concrete `LlvmType 0`. -/
def typeABIAlign (dl : DataLayout) : LlvmType 0 → Nat
  | .int (.concrete w) => intABIAlign w
  | .float ft => floatABIAlign ft
  | .ptr as => dl.getPointerABIAlign as
  | .vector n elem =>
      let bits := n * dl.typeSizeInBits elem
      let bytes := (bits + 7) / 8
      nextPow2 (max 1 bytes)
  | .array _ elem => dl.typeABIAlign elem
  | .struct true _ => 1
  | .struct false fields => dl.structFieldsMaxAlign fields
  | .function .. => 1

def structFieldsMaxAlign (dl : DataLayout) : List (LlvmType 0) → Nat
  | [] => 1
  | f :: fs => max (dl.typeABIAlign f) (dl.structFieldsMaxAlign fs)

/--
Compute `(fieldByteOffsets, totalStructBytes)` for a struct type.
For unpacked structs, each field is aligned to its ABI alignment and total size
is padded to the struct's ABI alignment (matching `llvm::StructLayout`).
-/
def structLayoutAux (dl : DataLayout) (packed : Bool) (offset : Nat) :
    List (LlvmType 0) → List Nat × Nat
  | [] => ([], offset)
  | f :: fs =>
      let fAlign := if packed then 1 else dl.typeABIAlign f
      let fOffset := alignTo offset fAlign
      let fAlloc := dl.typeAllocSize f
      let (restOffsets, endOff) := dl.structLayoutAux packed (fOffset + fAlloc) fs
      (fOffset :: restOffsets, endOff)

/-- Exact size in bits (matches `DataLayout::getTypeSizeInBits`). -/
def typeSizeInBits (dl : DataLayout) : LlvmType 0 → Nat
  | .int (.concrete w) => w
  | .float ft => ft.bitWidth
  | .ptr as => dl.getPointerSizeInBits as
  | .vector n elem => n * dl.typeSizeInBits elem
  | .array n elem => n * dl.typeAllocSize elem * 8
  | .struct packed fields =>
      let (_, rawEnd) := dl.structLayoutAux packed 0 fields
      let sAlign := if packed then 1 else dl.structFieldsMaxAlign fields
      alignTo rawEnd sAlign * 8
  | .function .. => 0

/-- Store size in bytes (matches `DataLayout::getTypeStoreSize`). -/
def typeStoreSize (dl : DataLayout) (ty : LlvmType 0) : Nat :=
  (dl.typeSizeInBits ty + 7) / 8

/-- Allocation size in bytes (matches `DataLayout::getTypeAllocSize`). -/
def typeAllocSize (dl : DataLayout) (ty : LlvmType 0) : Nat :=
  alignTo (dl.typeStoreSize ty) (dl.typeABIAlign ty)

end

/-- Compute `(fieldOffsets, totalSizeInBytes)` for a struct type. -/
def structLayout (dl : DataLayout) (packed : Bool) (fields : List (LlvmType 0)) :
    List Nat × Nat :=
  let (offsets, rawEnd) := dl.structLayoutAux packed 0 fields
  let sAlign := if packed then 1 else dl.structFieldsMaxAlign fields
  (offsets, alignTo rawEnd sAlign)

/-- Byte offset of field `idx` in a struct (returns `none` if out of bounds). -/
def structFieldOffset? (dl : DataLayout) (packed : Bool) (fields : List (LlvmType 0))
    (idx : Nat) : Option Nat :=
  (dl.structLayout packed fields).1[idx]?

end DataLayout

end LeanNanoLlvm.AST
