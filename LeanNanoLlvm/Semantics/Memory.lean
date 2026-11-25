import LeanNanoLlvm.Util.Config
import LeanNanoLlvm.Util.Undef
import LeanNanoLlvm.Util.AssocMap
import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.DataLayout

namespace LeanNanoLlvm.Semantics

open AST

/-- Unique identifier for every allocated memory object (globals, stack allocas, heap objects, functions). -/
abbrev AllocId := Nat

/--
Pointer provenance tracking (aligned with LLVM's provenance model and `llubi::Provenance`).
- `nullary`: invalid / null / unexposed integer-cast pointer.
- `concrete allocId`: derived from a specific memory object.
- `wildcard gen knownAlloc?`: created by `inttoptr` with snapshot of exposed provenances up to `gen`,
  optionally narrowed to `knownAlloc?` by `gep inbounds` or a previous memory access.
-/
inductive Provenance : Type where
  | nullary
  | concrete (allocId : AllocId)
  | wildcard (generation : Nat) (knownAlloc? : Option AllocId := none)
deriving Repr, DecidableEq, Inhabited

/-- Runtime pointer value: provenance + address bitvector of width `addrWidth`. -/
structure Pointer : Type where
  prov      : Provenance
  addrWidth : Nat
  addr      : BitVec addrWidth
deriving Repr, DecidableEq

namespace Pointer

def null (dl : DataLayout) (addrSpace : Nat := 0) : Pointer :=
  let w := dl.getPointerSizeInBits addrSpace
  { prov := .nullary, addrWidth := w, addr := BitVec.ofNat w (dl.getNullPtrValue addrSpace) }

def isNull (p : Pointer) (dl : DataLayout) (addrSpace : Nat := 0) : Bool :=
  p.addr.toNat == dl.getNullPtrValue addrSpace

def withNewAddr (p : Pointer) (newAddr : BitVec p.addrWidth) : Pointer :=
  { p with addr := newAddr }

def withNewProv (p : Pointer) (newProv : Provenance) : Pointer :=
  { p with prov := newProv }

def toString (p : Pointer) : String :=
  let hex := String.ofList (Nat.toDigits 16 p.addr.toNat)
  let provStr := match p.prov with
    | .nullary => "nullary"
    | .concrete id => s!"alloc#{id}"
    | .wildcard g none => s!"wildcard@{g}"
    | .wildcard g (some id) => s!"wildcard@{g}(alloc#{id})"
  s!"ptr 0x{hex} [{provStr}]"

instance : ToString Pointer := ⟨Pointer.toString⟩

end Pointer

/--
Single bit in memory (idealized exact model of `llubi::Byte`).
Unlike `llubi`'s randomized C++ tag approximation, each concrete pointer bit stores
its exact `(Provenance × bitIndex)` fragment — zero false negatives and proof-friendly.
-/
inductive MemBit : Type where
  | poison
  | undef
  | concrete (bit : Bool) (provBit : Option (Provenance × Nat) := none)
deriving Repr, DecidableEq

namespace MemBit

instance : Inhabited MemBit := ⟨.poison⟩

@[simp]
def isConcrete : MemBit → Bool
  | .concrete _ _ => true
  | _ => false

@[simp]
def isPoison : MemBit → Bool
  | .poison => true
  | _ => false

@[simp]
def isUndef : MemBit → Bool
  | .undef => true
  | _ => false

end MemBit

/--
An 8-bit byte in memory (`b0` = LSB, `b7` = MSB), supporting sub-byte access (`i1`, `i25`, `<3 x i3>`),
poison/undef bits, and exact per-bit pointer provenance.
-/
structure MemByte : Type where
  b0 : MemBit
  b1 : MemBit
  b2 : MemBit
  b3 : MemBit
  b4 : MemBit
  b5 : MemBit
  b6 : MemBit
  b7 : MemBit
deriving Repr, DecidableEq

namespace MemByte

def poison : MemByte :=
  ⟨.poison, .poison, .poison, .poison, .poison, .poison, .poison, .poison⟩

def undef : MemByte :=
  ⟨.undef, .undef, .undef, .undef, .undef, .undef, .undef, .undef⟩

def uninitFor (cfg : SemanticsConfig) : MemByte :=
  if cfg.allowUndef then undef else poison

def concrete (v : UInt8) : MemByte :=
  let n := v.toNat
  let mk (i : Nat) : MemBit := .concrete (((n >>> i) &&& 1) == 1) none
  ⟨mk 0, mk 1, mk 2, mk 3, mk 4, mk 5, mk 6, mk 7⟩

def zero : MemByte := concrete 0

instance : Inhabited MemByte := ⟨poison⟩

def getBit (b : MemByte) : Nat → MemBit
  | 0 => b.b0
  | 1 => b.b1
  | 2 => b.b2
  | 3 => b.b3
  | 4 => b.b4
  | 5 => b.b5
  | 6 => b.b6
  | _ => b.b7

def setBit : MemByte → Nat → MemBit → MemByte
  | ⟨_, b1, b2, b3, b4, b5, b6, b7⟩, 0, v => ⟨v, b1, b2, b3, b4, b5, b6, b7⟩
  | ⟨b0, _, b2, b3, b4, b5, b6, b7⟩, 1, v => ⟨b0, v, b2, b3, b4, b5, b6, b7⟩
  | ⟨b0, b1, _, b3, b4, b5, b6, b7⟩, 2, v => ⟨b0, b1, v, b3, b4, b5, b6, b7⟩
  | ⟨b0, b1, b2, _, b4, b5, b6, b7⟩, 3, v => ⟨b0, b1, b2, v, b4, b5, b6, b7⟩
  | ⟨b0, b1, b2, b3, _, b5, b6, b7⟩, 4, v => ⟨b0, b1, b2, b3, v, b5, b6, b7⟩
  | ⟨b0, b1, b2, b3, b4, _, b6, b7⟩, 5, v => ⟨b0, b1, b2, b3, b4, v, b6, b7⟩
  | ⟨b0, b1, b2, b3, b4, b5, _, b7⟩, 6, v => ⟨b0, b1, b2, b3, b4, b5, v, b7⟩
  | ⟨b0, b1, b2, b3, b4, b5, b6, _⟩, _, v => ⟨b0, b1, b2, b3, b4, b5, b6, v⟩

/-- Extract all 8 bits LSB-first as a list. -/
def toBits (b : MemByte) : List MemBit :=
  [b.b0, b.b1, b.b2, b.b3, b.b4, b.b5, b.b6, b.b7]

/-- Build a `MemByte` from an 8-element LSB-first list (missing bits default to `.poison`). -/
def ofBits (bs : List MemBit) : MemByte :=
  ⟨bs.getD 0 .poison, bs.getD 1 .poison, bs.getD 2 .poison, bs.getD 3 .poison,
   bs.getD 4 .poison, bs.getD 5 .poison, bs.getD 6 .poison, bs.getD 7 .poison⟩

/-- Check whether a byte is fully concrete and return its `UInt8` value if so. -/
def asConcreteUInt8? (b : MemByte) : Option UInt8 :=
  let rec go (i : Nat) (acc : Nat) : Option Nat :=
    match i with
    | 0 => some acc
    | k + 1 =>
      match b.getBit k with
      | .concrete bit _ => go k (acc ||| (if bit then 1 <<< k else 0))
      | _ => none
  (go 8 0).map UInt8.ofNat

/--
Check `llubi::Byte::isCanonicalPaddingByte`:
For a byte whose low `validBits` bits (1..7) hold the value and upper `(8 - validBits)` bits
are padding, padding bits must be concrete zero (if any value bit is non-poison) or poison
(if all value bits are poison).
-/
def isCanonicalPaddingByte (b : MemByte) (validBits : Nat) : Bool :=
  if validBits == 0 || validBits ≥ 8 then true
  else
    let valueIndices := List.range validBits
    let padIndices := (List.range (8 - validBits)).map (· + validBits)
    let allValPoison := valueIndices.all fun i => (b.getBit i).isPoison
    if allValPoison then
      padIndices.all fun i => (b.getBit i).isPoison
    else
      padIndices.all fun i =>
        match b.getBit i with
        | .concrete false _ => true
        | _ => false

end MemByte

/-- Lifetime state of a memory object (matches `llubi::MemoryObjectState`). -/
inductive MemoryObjectState : Type where
  | alive
  | dead  -- outside lifetime (alloca before lifetime.start or after lifetime.end): loads yield poison, stores are UB
  | freed -- deallocated (after free or stack frame exit): any load or store is UB
deriving Repr, DecidableEq, Inhabited

/-- Allocation provenance kind of a memory object (matches `llubi::MemAllocKind`). -/
inductive MemAllocKind : Type where
  | global
  | stack
  | heap
  | func
  | blockAddr
deriving Repr, DecidableEq, Inhabited

/-- Initializer kind for newly allocated memory objects. -/
inductive MemInitKind : Type where
  | zeroed
  | uninitialized
  | poisoned
deriving Repr, DecidableEq, Inhabited

/-- A single allocated memory object in the abstract machine. -/
structure MemoryObject : Type where
  allocId    : AllocId
  baseAddr   : Nat
  size       : Nat
  align      : Nat
  addrSpace  : Nat
  name       : String
  state      : MemoryObjectState
  allocKind  : MemAllocKind
  isConstant : Bool := false
  bytes      : Array MemByte
deriving Repr, DecidableEq

namespace MemoryObject

/-- Check whether `addr` lies in `[baseAddr, baseAddr + size]` (inclusive end for one-past-the-end GEP). -/
def inBounds (mo : MemoryObject) (addr : Nat) : Bool :=
  mo.baseAddr ≤ addr && addr ≤ mo.baseAddr + mo.size

def isHeap (mo : MemoryObject) : Bool := mo.allocKind == .heap
def isStack (mo : MemoryObject) : Bool := mo.allocKind == .stack
def isGlobal (mo : MemoryObject) : Bool := mo.allocKind == .global

end MemoryObject

/-- Full memory subsystem state (mirrors `llubi::Context` memory fields). -/
structure MemoryState : Type where
  nextAllocId        : AllocId := 1
  nextAddr           : Nat := 8
  usedMem            : Nat := 0
  objects            : AssocMap AllocId MemoryObject := ∅
  /-- Ordered list of `(allocId, exposedAtGeneration)` for `ptrtoint` / `inttoptr` provenance exposure. -/
  exposedGeneration  : Nat := 0
  exposedProvenances : List (AllocId × Nat) := []
  globalAddrs        : AssocMap AST.GlobalId Pointer := ∅
  funcAddrs          : AssocMap AST.FunctionId Pointer := ∅
  addrToFunc         : AssocMap Nat AST.FunctionId := ∅

instance : Inhabited MemoryState := ⟨{}⟩

namespace MemoryState

/-- Check whether `size` exceeds the largest signed integer of the index type (matches `llubi::exceedsMaxObjectSize`). -/
def exceedsMaxObjectSize (dl : DataLayout) (size addrSpace : Nat) : Bool :=
  let idxBits := dl.getIndexSizeInBits addrSpace
  if idxBits ≤ 1 then size > 0
  else size ≥ (1 <<< (idxBits - 1))

/-- Pattern-matching updaters (avoid struct-with projection duplication in Lean's kernel). -/
def withObjects : MemoryState → AssocMap AllocId MemoryObject → MemoryState
  | ⟨nextAllocId, nextAddr, usedMem, _, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc⟩, objs =>
    ⟨nextAllocId, nextAddr, usedMem, objs, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc⟩

def insertGlobalAddr : MemoryState → AST.GlobalId → Pointer → MemoryState
  | ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc⟩, name, ptr =>
    ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs.insert name ptr, funcAddrs, addrToFunc⟩

def insertFuncAddr : MemoryState → AST.FunctionId → Nat → Pointer → MemoryState
  | ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc⟩, name, baseAddr, ptr =>
    ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs.insert name ptr, addrToFunc.insert baseAddr name⟩

private def moWithBytes : MemoryObject → Array MemByte → MemoryObject
  | ⟨allocId, baseAddr, size, align, addrSpace, name, state, allocKind, isConstant, _⟩, bs =>
    ⟨allocId, baseAddr, size, align, addrSpace, name, state, allocKind, isConstant, bs⟩

private def moWithStateBytes : MemoryObject → MemoryObjectState → Array MemByte → MemoryObject
  | ⟨allocId, baseAddr, size, align, addrSpace, name, _, allocKind, isConstant, _⟩, st, bs =>
    ⟨allocId, baseAddr, size, align, addrSpace, name, st, allocKind, isConstant, bs⟩

/-- Allocate a new memory object with monotonically increasing aligned address + guard byte. -/
def allocate : MemoryState → DataLayout → SemanticsConfig →
    Nat → Nat → String → Nat → MemInitKind → MemAllocKind → (isConstant : Bool := false) →
    Except ExecError (MemoryObject × MemoryState)
  | ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc⟩,
    dl, cfg, size, align, name, addrSpace, initKind, allocKind, isConstant => do
  if exceedsMaxObjectSize dl size addrSpace then
    .error (.immediateUB s!"Allocation size {size} exceeds maximum object size")
  let effAlign := max 1 align
  let allocSpace := max 1 size
  if cfg.maxMem != 0 && usedMem + allocSpace > cfg.maxMem then
    .error .outOfMemory
  let alignedAddr := DataLayout.alignTo nextAddr effAlign
  let addrBits := dl.getAddressSizeInBits addrSpace
  if alignedAddr + allocSpace ≥ (1 <<< addrBits) then
    .error .outOfMemory
  let fillByte := match initKind with
    | .zeroed        => MemByte.zero
    | .uninitialized => MemByte.uninitFor cfg
    | .poisoned      => MemByte.poison
  let initState := match initKind with
    | .poisoned => MemoryObjectState.dead
    | _         => MemoryObjectState.alive
  let obj : MemoryObject := {
    allocId    := nextAllocId
    baseAddr   := alignedAddr
    size       := size
    align      := effAlign
    addrSpace  := addrSpace
    name       := name
    state      := initState
    allocKind  := allocKind
    isConstant := isConstant
    bytes      := Array.replicate size fillByte
  }
  let mem' : MemoryState :=
    ⟨nextAllocId + 1, alignedAddr + allocSpace + 1, usedMem + allocSpace,
     objects.insert obj.allocId obj, exposedGeneration, exposedProvenances,
     globalAddrs, funcAddrs, addrToFunc⟩
  .ok (obj, mem')

/-- Create a concrete pointer at offset 0 of `obj`. -/
def derivePointer (dl : DataLayout) (obj : MemoryObject) : Pointer :=
  let w := dl.getPointerSizeInBits obj.addrSpace
  { prov := .concrete obj.allocId, addrWidth := w, addr := BitVec.ofNat w obj.baseAddr }

/-- Free an allocated memory object (marks `state := .freed`, clears bytes, removes exposed entries). -/
def freeObject : MemoryState → AllocId → MemoryState
  | mem@⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc⟩, allocId =>
    match objects.get? allocId with
    | none => mem
    | some obj =>
      if obj.state == .freed then mem
      else
        let allocSpace := max 1 obj.size
        let freedObj := moWithStateBytes obj .freed #[]
        ⟨nextAllocId, nextAddr, usedMem - allocSpace, objects.insert allocId freedObj,
         exposedGeneration, exposedProvenances.filter (fun (id, _) => id != allocId),
         globalAddrs, funcAddrs, addrToFunc⟩

/-- Expose provenance on `ptrtoint` (matches `llubi::Context::exposeProvenance`). -/
def exposeProvenance : MemoryState → Provenance → MemoryState
  | mem@⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc⟩, prov =>
    match prov with
    | .concrete allocId =>
      match objects.get? allocId with
      | some obj =>
        if obj.state == .alive then
          let nextGen := exposedGeneration + 1
          ⟨nextAllocId, nextAddr, usedMem, objects, nextGen,
           exposedProvenances ++ [(allocId, nextGen)], globalAddrs, funcAddrs, addrToFunc⟩
        else mem
      | none => mem
    | _ => mem

/-- Create a wildcard provenance snapshot on `inttoptr` (matches `llubi::Context::getWildcardProvenance`). -/
def getWildcardProvenance (mem : MemoryState) : Provenance :=
  if mem.exposedGeneration == 0 then .nullary
  else .wildcard mem.exposedGeneration none

/--
Resolve the underlying `MemoryObject` for a pointer `ptr` (for concrete or wildcard provenance).
Matches `llubi::Context::checkProvenance`:
- `nullary` → `none`
- `concrete id` → `objects.get? id`
- `wildcard gen known?` → find an exposed allocation `(id, expGen)` with `expGen ≤ gen` whose
  address range contains `ptr.addr` (and matches `known?` if already fixed).
-/
def resolveObject? (mem : MemoryState) (ptr : Pointer) : Option MemoryObject :=
  match ptr.prov with
  | .nullary => none
  | .concrete id => mem.objects.get? id
  | .wildcard gen known? =>
    let addr := ptr.addr.toNat
    let rec findExposed : List (AllocId × Nat) → Option MemoryObject
      | [] => none
      | (id, expGen) :: rest =>
        if expGen ≤ gen then
          let knownOk := match known? with
            | none => true
            | some k => k == id
          if knownOk then
            match mem.objects.get? id with
            | some mo =>
              if mo.state != .freed && mo.inBounds addr then some mo
              else findExposed rest
            | none => findExposed rest
          else findExposed rest
        else findExposed rest
    findExposed mem.exposedProvenances

/--
Verify whether a memory access of `accessSize` bytes with required `alignment` via `ptr` is valid.
Returns `(memoryObject, byteOffset)` or raises `ExecError.immediateUB` (matches `llubi::ExecutorBase::verifyMemAccess`).
Note: Loading from a `.dead` (out-of-lifetime) stack object is allowed and yields poison bytes,
whereas storing to a `.dead` object or accessing a `.freed` object is Immediate UB.
-/
def verifyMemAccess (mem : MemoryState) (ptr : Pointer) (accessSize alignment : Nat)
    (isStore : Bool) : Except ExecError (MemoryObject × Nat) := do
  match mem.resolveObject? ptr with
  | none =>
    .error (.immediateUB s!"Invalid memory access via pointer with invalid/nullary provenance: {ptr}")
  | some mo =>
    let badState := if isStore then mo.state != .alive else mo.state == .freed
    if badState then
      .error (.immediateUB s!"Access to dead/freed memory object '{mo.name}' via {ptr}")
    if isStore && mo.isConstant then
      .error (.immediateUB s!"Write to constant memory object '{mo.name}' via {ptr}")
    let effAlign := max 1 alignment
    let addr := ptr.addr.toNat
    if addr % effAlign != 0 then
      .error (.immediateUB s!"Misaligned memory access: addr=0x{String.ofList (Nat.toDigits 16 addr)}, align={effAlign}")
    if accessSize > mo.size || addr < mo.baseAddr then
      .error (.immediateUB s!"Out-of-bounds memory access: size={accessSize}, ptr={ptr}, obj=[0x{String.ofList (Nat.toDigits 16 mo.baseAddr)}, +{mo.size})")
    let offset := addr - mo.baseAddr
    if offset > mo.size - accessSize then
      .error (.immediateUB s!"Out-of-bounds memory access: offset={offset}, size={accessSize}, objSize={mo.size}")
    .ok (mo, offset)

/-- Read `len` raw bytes from `mo` starting at `offset` (returns poison bytes if `mo.state == .dead`). -/
def readObjectBytes (mo : MemoryObject) (offset len : Nat) : Array MemByte :=
  if mo.state == .dead then
    Array.replicate len MemByte.poison
  else
    Array.ofFn (n := len) fun i => mo.bytes.getD (offset + i.val) MemByte.poison

/-- Write `newBytes` into object `allocId` starting at `offset`. -/
def writeObjectBytes : MemoryState → AllocId → Nat → Array MemByte → MemoryState
  | mem@⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc⟩,
    allocId, offset, newBytes =>
    match objects.get? allocId with
    | none => mem
    | some mo =>
      let rec go (i : Nat) : Nat → Array MemByte → Array MemByte
        | 0, arr => arr
        | rem + 1, arr =>
          let idx := offset + i
          let arr' := if h : idx < arr.size then arr.set idx (newBytes.getD i MemByte.poison) h else arr
          go (i + 1) rem arr'
      let updated := go 0 newBytes.size mo.bytes
      ⟨nextAllocId, nextAddr, usedMem, objects.insert allocId (moWithBytes mo updated),
       exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc⟩

/-- Execute `llvm.lifetime.start` (makes stack object alive with fresh uninit/poison bytes). -/
def lifetimeStart (mem : MemoryState) (cfg : SemanticsConfig) (ptr : Pointer) : MemoryState :=
  match mem.resolveObject? ptr with
  | none => mem
  | some mo =>
    if mo.state == .freed then mem
    else
      let fillByte := MemByte.uninitFor cfg
      let mo' := moWithStateBytes mo .alive (Array.replicate mo.size fillByte)
      mem.withObjects (mem.objects.insert mo.allocId mo')

/-- Execute `llvm.lifetime.end` (marks stack object dead and poisons its bytes). -/
def lifetimeEnd (mem : MemoryState) (ptr : Pointer) : MemoryState :=
  match mem.resolveObject? ptr with
  | none => mem
  | some mo =>
    if mo.state == .freed then mem
    else
      let mo' := moWithStateBytes mo .dead (Array.replicate mo.size MemByte.poison)
      mem.withObjects (mem.objects.insert mo.allocId mo')

end MemoryState

end LeanNanoLlvm.Semantics
