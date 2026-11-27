import LeanNanoLlvm.Util.Config
import LeanNanoLlvm.Util.Oracle
import LeanNanoLlvm.Util.AssocMap
import LeanNanoLlvm.Util.Hex
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
  | wildcard (generation : Nat) (knownAlloc? : Option AllocId := none) (wildcardId : Nat := 0)
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

def withNewAddr : Pointer → (w : Nat) → BitVec w → Pointer
  | ⟨prov, _, _⟩, w, newAddr => ⟨prov, w, newAddr⟩

def withNewProv : Pointer → Provenance → Pointer
  | ⟨_, w, addr⟩, newProv => ⟨newProv, w, addr⟩

def toString (p : Pointer) : String :=
  let hex := String.ofList (Nat.toDigits 16 p.addr.toNat)
  let provStr := match p.prov with
    | .nullary => "nullary"
    | .concrete id => s!"alloc#{id}"
    | .wildcard g none _ => s!"wildcard@{g}"
    | .wildcard g (some id) _ => s!"wildcard@{g}(alloc#{id})"
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
  /-- Shared resolution table for wildcard provenances once dereferenced (matches `llubi::WildcardProvenance`). -/
  wildcardResolved   : AssocMap Nat AllocId := ∅
  /-- Stack objects of callers suspended in a `tail`/`musttail` call: any access to them is
  Immediate UB until the call returns (`llubi::MemoryObject::isInaccessible`). -/
  inaccessible       : List AllocId := []

instance : Inhabited MemoryState := ⟨{}⟩

namespace MemoryState

/-- Make `ids` inaccessible (no-op, definitionally, for `[]`). -/
def hide (mem : MemoryState) : List AllocId → MemoryState
  | [] => mem
  | ids => { mem with inaccessible := ids ++ mem.inaccessible }

/-- Make `ids` accessible again (no-op, definitionally, for `[]`). -/
def unhide (mem : MemoryState) : List AllocId → MemoryState
  | [] => mem
  | ids => { mem with inaccessible := mem.inaccessible.filter (fun i => !ids.contains i) }

/-- Whether the object `id` is currently inaccessible. -/
@[simp] def isInaccessible (mem : MemoryState) (id : AllocId) : Bool :=
  mem.inaccessible.contains id

/-- All currently tracked allocation IDs in `mem`. -/
def allocIds (mem : MemoryState) : List AllocId :=
  mem.objects.entries.map Prod.fst

/-- Check whether `size` exceeds the largest signed integer of the index type (matches `llubi::exceedsMaxObjectSize`). -/
def exceedsMaxObjectSize (dl : DataLayout) (size addrSpace : Nat) : Bool :=
  let idxBits := dl.getIndexSizeInBits addrSpace
  if idxBits ≤ 1 then size > 0
  else size ≥ (1 <<< (idxBits - 1))

/-- Pattern-matching updaters (avoid struct-with projection duplication in Lean's kernel). -/
def withObjects : MemoryState → AssocMap AllocId MemoryObject → MemoryState
  | ⟨nextAllocId, nextAddr, usedMem, _, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc, wildcardResolved, inaccessible⟩, objs =>
    ⟨nextAllocId, nextAddr, usedMem, objs, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc, wildcardResolved, inaccessible⟩

def insertGlobalAddr : MemoryState → AST.GlobalId → Pointer → MemoryState
  | ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc, wildcardResolved, inaccessible⟩, name, ptr =>
    ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs.insert name ptr, funcAddrs, addrToFunc, wildcardResolved, inaccessible⟩

def insertFuncAddr : MemoryState → AST.FunctionId → Nat → Pointer → MemoryState
  | ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc, wildcardResolved, inaccessible⟩, name, baseAddr, ptr =>
    ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs.insert name ptr, addrToFunc.insert baseAddr name, wildcardResolved, inaccessible⟩

/-- Bind a wildcard provenance ID to the resolved `AllocId` on first side-effecting memory access. -/
def bindWildcard : MemoryState → Provenance → AllocId → MemoryState
  | ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc, wildcardResolved, inaccessible⟩, prov, aid =>
    match prov with
    | .wildcard _ _ wid =>
      if wid == 0 then
        ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc, wildcardResolved, inaccessible⟩
      else
        match wildcardResolved.get? wid with
        | some _ =>
          ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc, wildcardResolved, inaccessible⟩
        | none =>
          ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc, wildcardResolved.insert wid aid, inaccessible⟩
    | _ =>
      ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc, wildcardResolved, inaccessible⟩

private def moWithBytes : MemoryObject → Array MemByte → MemoryObject
  | ⟨allocId, baseAddr, size, align, addrSpace, name, state, allocKind, isConstant, _⟩, bs =>
    ⟨allocId, baseAddr, size, align, addrSpace, name, state, allocKind, isConstant, bs⟩

private def moWithStateBytes : MemoryObject → MemoryObjectState → Array MemByte → MemoryObject
  | ⟨allocId, baseAddr, size, align, addrSpace, name, _, allocKind, isConstant, _⟩, st, bs =>
    ⟨allocId, baseAddr, size, align, addrSpace, name, st, allocKind, isConstant, bs⟩

/-- Structural well-formedness invariant on `MemoryState`:
    `nextAllocId` is strictly above all existing IDs, and `nextAddr` is strictly above
    every allocated object's address range (so deterministic bump allocation is disjoint). -/
structure WellFormed (mem : MemoryState) : Prop where
  nextAllocId_pos : 1 ≤ mem.nextAllocId
  nextAddr_ge : 8 ≤ mem.nextAddr
  objects_wf : ∀ id mo, mem.objects.get? id = some mo →
    mo.allocId = id ∧
    id < mem.nextAllocId ∧
    1 ≤ mo.baseAddr ∧
    mo.baseAddr + max 1 mo.size < mem.nextAddr

theorem hide_preserves_wf {mem : MemoryState} (hwf : WellFormed mem) (ids : List AllocId) :
    WellFormed (mem.hide ids) := by
  cases ids with
  | nil => exact hwf
  | cons _ _ => exact ⟨hwf.nextAllocId_pos, hwf.nextAddr_ge, hwf.objects_wf⟩

theorem unhide_preserves_wf {mem : MemoryState} (hwf : WellFormed mem) (ids : List AllocId) :
    WellFormed (mem.unhide ids) := by
  cases ids with
  | nil => exact hwf
  | cons _ _ => exact ⟨hwf.nextAllocId_pos, hwf.nextAddr_ge, hwf.objects_wf⟩

theorem empty_wf : WellFormed ({} : MemoryState) where
  nextAllocId_pos := Nat.le_refl 1
  nextAddr_ge := Nat.le_refl 8
  objects_wf := by
    intro id mo h
    simp at h

/-- Helper: `alignTo n align ≥ n`. -/
theorem alignTo_ge (n align : Nat) : n ≤ DataLayout.alignTo n align := by
  unfold DataLayout.alignTo
  split
  · exact Nat.le_refl n
  · rename_i h
    have hpos : 0 < align := by omega
    have hdiv := Nat.div_add_mod (n + align - 1) align
    have hmod := Nat.mod_lt (n + align - 1) hpos
    rw [Nat.mul_comm] at hdiv
    omega

/-- Helper: `alignTo n align` is divisible by `align` whenever `align ≥ 1`. -/
theorem alignTo_mod (n align : Nat) (h : 1 ≤ align) : DataLayout.alignTo n align % align = 0 := by
  unfold DataLayout.alignTo
  split
  · rename_i hle
    have : align = 1 := by omega
    subst this
    exact Nat.mod_one n
  · exact Nat.mul_mod_left ((n + align - 1) / align) align

/--
Relational nondeterministic allocation specification used by the primary inductive `Step` relation.
Any non-null, properly aligned address fitting in the target address space and disjoint from
all existing objects is permitted — enabling sound proofs of dead-`alloca` elimination and
allocation reordering without committing to a concrete allocator address layout.
-/
structure AllocSpec (mem : MemoryState) (dl : DataLayout) (cfg : SemanticsConfig)
    (size align : Nat) (name : String) (addrSpace : Nat)
    (initKind : MemInitKind) (allocKind : MemAllocKind) (isConstant : Bool)
    (obj : MemoryObject) (mem' : MemoryState) : Prop where
  size_ok : exceedsMaxObjectSize dl size addrSpace = false
  mem_budget : cfg.maxMem = 0 ∨ mem.usedMem + max 1 size < cfg.maxMem
  id_eq : obj.allocId = mem.nextAllocId
  size_eq : obj.size = size
  align_eq : obj.align = max 1 align
  as_eq : obj.addrSpace = addrSpace
  name_eq : obj.name = name
  kind_eq : obj.allocKind = allocKind
  const_eq : obj.isConstant = isConstant
  state_eq : obj.state = match initKind with | .poisoned => .dead | _ => .alive
  bytes_eq : obj.bytes = Array.replicate size (match initKind with
    | .zeroed => MemByte.zero
    | .uninitialized => MemByte.uninitFor cfg
    | .poisoned => MemByte.poison)
  addr_pos : 1 ≤ obj.baseAddr
  addr_aligned : obj.baseAddr % max 1 align = 0
  addr_in_space : obj.baseAddr + max 1 size < (1 <<< dl.getAddressSizeInBits addrSpace)
  disjoint : ∀ id mo, mem.objects.get? id = some mo →
    obj.baseAddr + max 1 size ≤ mo.baseAddr ∨ mo.baseAddr + max 1 mo.size ≤ obj.baseAddr
  mem'_eq : mem' =
    ⟨mem.nextAllocId + 1, max mem.nextAddr (obj.baseAddr + max 1 size + 1),
     mem.usedMem + max 1 size, mem.objects.insert obj.allocId obj,
     mem.exposedGeneration, mem.exposedProvenances,
     mem.globalAddrs, mem.funcAddrs, mem.addrToFunc, mem.wildcardResolved,
     mem.inaccessible.filter (· != obj.allocId)⟩

/-- A freshly allocated object is accessible. -/
theorem AllocSpec.not_inaccessible {mem dl cfg size align name addrSpace initKind allocKind isConstant obj mem'}
    (hspec : AllocSpec mem dl cfg size align name addrSpace initKind allocKind isConstant obj mem') :
    mem'.isInaccessible obj.allocId = false := by
  rw [hspec.mem'_eq]
  simp [isInaccessible, List.contains_eq_any_beq, List.any_filter]

theorem AllocSpec.not_mem_inaccessible {mem dl cfg size align name addrSpace initKind allocKind isConstant obj mem'}
    (hspec : AllocSpec mem dl cfg size align name addrSpace initKind allocKind isConstant obj mem') :
    obj.allocId ∉ mem'.inaccessible := by
  rw [hspec.mem'_eq]
  simp

/-- `AllocSpec` preserves `MemoryState.WellFormed`. -/
theorem AllocSpec.preserves_wf {mem dl cfg size align name addrSpace initKind allocKind isConstant obj mem'}
    (hwf : WellFormed mem)
    (hspec : AllocSpec mem dl cfg size align name addrSpace initKind allocKind isConstant obj mem') :
    WellFormed mem' := by
  rw [hspec.mem'_eq]
  refine ⟨by dsimp only [AllocId]; have := hwf.nextAllocId_pos; omega,
          by dsimp only; have := hwf.nextAddr_ge; omega, ?_⟩
  intro id mo hget
  dsimp only at hget ⊢
  rw [AssocMap.get?_insert] at hget
  by_cases heq : (obj.allocId == id) = true
  · simp only [heq, ↓reduceIte, Option.some.injEq] at hget
    subst hget
    have hid : obj.allocId = id := eq_of_beq heq
    refine ⟨hid, by rw [← hid, hspec.id_eq]; exact Nat.lt_succ_self _, hspec.addr_pos, ?_⟩
    rw [hspec.size_eq]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
  · have hne : (obj.allocId == id) = false := Bool.eq_false_iff.mpr heq
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at hget
    obtain ⟨h1, h2, h3, h4⟩ := hwf.objects_wf id mo hget
    exact ⟨h1, Nat.lt_succ_of_lt h2, h3, Nat.lt_of_lt_of_le h4 (Nat.le_max_left _ _)⟩

/-- Allocate a new memory object with monotonically increasing aligned address + guard byte. -/
def allocate : MemoryState → DataLayout → SemanticsConfig →
    Nat → Nat → String → Nat → MemInitKind → MemAllocKind → (isConstant : Bool := false) →
    Except ExecError (MemoryObject × MemoryState)
  | ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc, wildcardResolved, inaccessible⟩,
    dl, cfg, size, align, name, addrSpace, initKind, allocKind, isConstant =>
  if exceedsMaxObjectSize dl size addrSpace then
    .error (.immediateUB s!"Allocation size {size} exceeds maximum object size")
  else
    let effAlign := max 1 align
    let allocSpace := max 1 size
    if cfg.maxMem != 0 && usedMem + allocSpace ≥ cfg.maxMem then
      .error .outOfMemory
    else
      let alignedAddr := DataLayout.alignTo nextAddr effAlign
      let addrBits := dl.getAddressSizeInBits addrSpace
      if alignedAddr + allocSpace ≥ (1 <<< addrBits) then
        .error .outOfMemory
      else
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
           globalAddrs, funcAddrs, addrToFunc, wildcardResolved,
           inaccessible.filter (· != obj.allocId)⟩
        .ok (obj, mem')

/-- Soundness of deterministic bump `allocate` w.r.t. relational `AllocSpec`. -/
theorem allocate_satisfies_AllocSpec {mem dl cfg size align name addrSpace initKind allocKind isConstant obj mem'}
    (hwf : WellFormed mem)
    (h : allocate mem dl cfg size align name addrSpace initKind allocKind isConstant = .ok (obj, mem')) :
    AllocSpec mem dl cfg size align name addrSpace initKind allocKind isConstant obj mem' := by
  cases mem with
  | mk nextAllocId nextAddr usedMem objects exposedGeneration exposedProvenances globalAddrs funcAddrs addrToFunc wildcardResolved inaccessible =>
    simp only [allocate] at h
    split at h
    · simp at h
    · rename_i hSizeOk
      simp only [Bool.not_eq_true] at hSizeOk
      split at h
      · simp at h
      · rename_i hMemOk
        split at h
        · simp at h
        · rename_i hSpaceOk
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hAlignGe : nextAddr ≤ DataLayout.alignTo nextAddr (max 1 align) :=
            alignTo_ge nextAddr (max 1 align)
          have hNextGe : 8 ≤ nextAddr := hwf.nextAddr_ge
          have hBudget : cfg.maxMem = 0 ∨ usedMem + max 1 size < cfg.maxMem := by
            simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_and] at hMemOk
            by_cases h0 : cfg.maxMem = 0
            · exact Or.inl h0
            · have := hMemOk h0
              exact Or.inr (by omega)
          have hSpace : DataLayout.alignTo nextAddr (max 1 align) + max 1 size <
              1 <<< dl.getAddressSizeInBits addrSpace := by
            omega
          refine {
            size_ok := hSizeOk
            mem_budget := hBudget
            id_eq := rfl
            size_eq := rfl
            align_eq := rfl
            as_eq := rfl
            name_eq := rfl
            kind_eq := rfl
            const_eq := rfl
            state_eq := by cases initKind <;> rfl
            bytes_eq := by cases initKind <;> rfl
            addr_pos := by dsimp only; omega
            addr_aligned := alignTo_mod nextAddr (max 1 align) (by omega)
            addr_in_space := hSpace
            disjoint := ?_
            mem'_eq := ?_
          }
          · intro id mo hget
            obtain ⟨_, _, _, hlt⟩ := hwf.objects_wf id mo hget
            dsimp only at hlt ⊢
            exact Or.inr (by omega)
          · have hmax : max nextAddr (DataLayout.alignTo nextAddr (max 1 align) + max 1 size + 1) =
                DataLayout.alignTo nextAddr (max 1 align) + max 1 size + 1 := by omega
            dsimp only
            rw [hmax]

theorem allocate_preserves_wf {mem dl cfg size align name addrSpace initKind allocKind isConstant obj mem'}
    (hwf : WellFormed mem)
    (h : allocate mem dl cfg size align name addrSpace initKind allocKind isConstant = .ok (obj, mem')) :
    WellFormed mem' :=
  (allocate_satisfies_AllocSpec hwf h).preserves_wf hwf

/-- Exhaustive classification of `MemoryState.allocate` errors. -/
theorem allocate_error_cases {mem : MemoryState} {dl : DataLayout} {cfg : SemanticsConfig}
    {size align : Nat} {name : String} {addrSpace : Nat} {initKind : MemInitKind}
    {allocKind : MemAllocKind} {isConstant : Bool} {e : ExecError}
    (h : allocate mem dl cfg size align name addrSpace initKind allocKind isConstant = .error e) :
    (e = .outOfMemory ∧
      ((cfg.maxMem ≠ 0 ∧ mem.usedMem + max 1 size ≥ cfg.maxMem) ∨
       DataLayout.alignTo mem.nextAddr (max 1 align) + max 1 size ≥ 1 <<< dl.getAddressSizeInBits addrSpace)) ∨
    (∃ msg, e = .immediateUB msg ∧ exceedsMaxObjectSize dl size addrSpace = true) := by
  cases mem with
  | mk nextAllocId nextAddr usedMem objects exposedGen exposedProvs globalAddrs funcAddrs addrToFunc wildcardResolved inaccessible =>
    unfold allocate at h
    dsimp only at h
    by_cases hsz : exceedsMaxObjectSize dl size addrSpace = true
    · rw [if_pos hsz] at h; cases h; exact Or.inr ⟨_, rfl, hsz⟩
    · rw [if_neg hsz] at h
      split at h
      · rename_i hmem
        cases h
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hmem
        exact Or.inl ⟨rfl, Or.inl hmem⟩
      · split at h
        · rename_i hsp
          cases h
          exact Or.inl ⟨rfl, Or.inr hsp⟩
        · cases h

/-- Create a concrete pointer at offset 0 of `obj`. -/
def derivePointer (dl : DataLayout) (obj : MemoryObject) : Pointer :=
  let w := dl.getPointerSizeInBits obj.addrSpace
  { prov := .concrete obj.allocId, addrWidth := w, addr := BitVec.ofNat w obj.baseAddr }

/-- Free an allocated memory object (marks `state := .freed`, clears bytes, removes exposed entries). -/
def freeObject : MemoryState → AllocId → MemoryState
  | ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc, wildcardResolved, inaccessible⟩, allocId =>
    match objects.get? allocId with
    | none =>
      ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc, wildcardResolved, inaccessible⟩
    | some obj =>
      if obj.state == .freed then
        ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc, wildcardResolved, inaccessible⟩
      else
        let allocSpace := max 1 obj.size
        let freedObj := moWithStateBytes obj .freed #[]
        ⟨nextAllocId, nextAddr, usedMem - allocSpace, objects.insert allocId freedObj,
         exposedGeneration, exposedProvenances.filter (fun (id, _) => id != allocId),
         globalAddrs, funcAddrs, addrToFunc, wildcardResolved, inaccessible⟩

theorem freeObject_preserves_wf {mem : MemoryState} (hwf : WellFormed mem) (allocId : AllocId) :
    WellFormed (freeObject mem allocId) := by
  cases mem with
  | mk nextAllocId nextAddr usedMem objects exposedGeneration exposedProvenances globalAddrs funcAddrs addrToFunc wildcardResolved inaccessible =>
    simp only [freeObject]
    cases hget : objects.get? allocId with
    | none => exact hwf
    | some obj =>
      dsimp only
      by_cases hf : (obj.state == .freed) = true
      · simp only [if_pos hf]; exact hwf
      · simp only [if_neg hf]
        refine ⟨hwf.nextAllocId_pos, hwf.nextAddr_ge, ?_⟩
        intro id mo hmo
        dsimp only at hmo ⊢
        rw [AssocMap.get?_insert] at hmo
        by_cases heq : (allocId == id) = true
        · simp only [heq, ↓reduceIte, Option.some.injEq] at hmo
          subst hmo
          have hid : allocId = id := eq_of_beq heq
          subst hid
          obtain ⟨h1, h2, h3, h4⟩ := hwf.objects_wf allocId obj hget
          cases obj
          exact ⟨h1, h2, h3, h4⟩
        · have hne : (allocId == id) = false := Bool.eq_false_iff.mpr heq
          simp only [hne, Bool.false_eq_true, ↓reduceIte] at hmo
          exact hwf.objects_wf id mo hmo

/-- Expose provenance on `ptrtoint` (matches `llubi::Context::exposeProvenance`). -/
def exposeProvenance : MemoryState → Provenance → MemoryState
  | ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc, wildcardResolved, inaccessible⟩, prov =>
    match prov with
    | .concrete allocId =>
      match objects.get? allocId with
      | some obj =>
        if obj.state == .alive then
          let nextGen := exposedGeneration + 1
          ⟨nextAllocId, nextAddr, usedMem, objects, nextGen,
           exposedProvenances ++ [(allocId, nextGen)], globalAddrs, funcAddrs, addrToFunc, wildcardResolved, inaccessible⟩
        else
          ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc, wildcardResolved, inaccessible⟩
      | none =>
        ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc, wildcardResolved, inaccessible⟩
    | _ =>
      ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc, wildcardResolved, inaccessible⟩

theorem exposeProvenance_preserves_wf {mem : MemoryState} (hwf : WellFormed mem) (prov : Provenance) :
    WellFormed (exposeProvenance mem prov) := by
  cases mem with
  | mk nextAllocId nextAddr usedMem objects exposedGeneration exposedProvenances globalAddrs funcAddrs addrToFunc wildcardResolved inaccessible =>
    simp only [exposeProvenance]
    cases prov with
    | nullary => exact hwf
    | wildcard _ _ _ => exact hwf
    | concrete allocId =>
      dsimp only
      cases hget : objects.get? allocId with
      | none => exact hwf
      | some obj =>
        dsimp only
        by_cases ha : (obj.state == .alive) = true
        · simp only [if_pos ha]
          exact ⟨hwf.nextAllocId_pos, hwf.nextAddr_ge, hwf.objects_wf⟩
        · simp only [if_neg ha]; exact hwf

theorem bindWildcard_preserves_wf {mem : MemoryState} (hwf : WellFormed mem)
    (prov : Provenance) (aid : AllocId) :
    WellFormed (bindWildcard mem prov aid) := by
  cases mem with
  | mk nextAllocId nextAddr usedMem objects exposedGeneration exposedProvenances globalAddrs funcAddrs addrToFunc wildcardResolved inaccessible =>
    simp only [bindWildcard]
    cases prov with
    | nullary => exact hwf
    | concrete _ => exact hwf
    | wildcard _ _ wid =>
      dsimp only
      split
      · exact hwf
      · cases wildcardResolved.get? wid with
        | some _ => exact hwf
        | none => exact ⟨hwf.nextAllocId_pos, hwf.nextAddr_ge, hwf.objects_wf⟩

/-- Create a wildcard provenance snapshot on `inttoptr` (matches `llubi::Context::getWildcardProvenance`). -/
def getWildcardProvenance (mem : MemoryState) (wildcardId : Nat := 0) : Provenance :=
  if mem.exposedGeneration == 0 then .nullary
  else .wildcard mem.exposedGeneration none wildcardId

/--
Resolve the underlying `MemoryObject` for a pointer `ptr` (for concrete or wildcard provenance).
Matches `llubi::Context::checkProvenance`:
- `nullary` → `none`
- `concrete id` → `objects.get? id`
- `wildcard gen known? wid` → if `wid` was already resolved to `fixedId` by a previous memory
  access, require `fixedId` (and agreement with `known?`); otherwise find an exposed allocation
  `(id, expGen)` with `expGen ≤ gen` whose address range contains `ptr.addr`.
-/
def resolveObject? (mem : MemoryState) (ptr : Pointer) : Option MemoryObject :=
  match ptr.prov with
  | .nullary => none
  | .concrete id => mem.objects.get? id
  | .wildcard gen known? wid =>
    let addr := ptr.addr.toNat
    let fixed? := if wid == 0 then none else mem.wildcardResolved.get? wid
    match fixed? with
    | some fixedId =>
      if (known?.map (· == fixedId)).getD true then
        match mem.objects.get? fixedId with
        | some mo =>
          if mo.state != .freed && mo.inBounds addr then some mo else none
        | none => none
      else none
    | none =>
      let rec findExposed : List (AllocId × Nat) → Option MemoryObject
        | [] => none
        | (id, expGen) :: rest =>
          if expGen ≤ gen && (known?.map (· == id)).getD true then
            match mem.objects.get? id with
            | some mo =>
              if mo.state != .freed && mo.inBounds addr then some mo
              else findExposed rest
            | none => findExposed rest
          else findExposed rest
      findExposed mem.exposedProvenances

/-- Is `allocId` the memory object of an IR global value (global variable or function)? -/
def isIRGlobalObject (mem : MemoryState) (allocId : AllocId) : Bool :=
  mem.globalAddrs.toList.any (fun (_, p) => p.prov == .concrete allocId) ||
  mem.funcAddrs.toList.any (fun (_, p) => p.prov == .concrete allocId)

/-- Display name of a memory object as `llubi` prints it (`@g` for IR globals; unnamed stack
objects print an empty name). -/
def objectDisplayName (mem : MemoryState) (obj : MemoryObject) : String :=
  if mem.isIRGlobalObject obj.allocId then "@" ++ obj.name
  else if obj.allocKind == .stack && !obj.name.isEmpty && obj.name.all Char.isDigit then ""
  else if obj.allocKind == .stack && obj.name.startsWith "alloca." then ""
  else obj.name

/-- `llubi`'s `Pointer::print`: `ptr 0x<addr> [<object>[ + <offset>][ (dead|dangling)]]`. -/
def ptrString (mem : MemoryState) (p : Pointer) : String :=
  let addr := p.addr.toNat
  let objOf : Option AllocId := match p.prov with
    | .concrete id => some id
    | .wildcard _ (some id) _ => some id
    | _ => none
  let tag : String :=
    match objOf with
    | some id =>
      match mem.objects.get? id with
      | some obj =>
        let w := p.addrWidth
        let diff : Int := ((addr : Int) - (obj.baseAddr : Int)) % (2 ^ w : Int)
        let sdiff : Int := if diff ≥ 2 ^ (w - 1) then diff - 2 ^ w else diff
        let off := if addr != obj.baseAddr then s!" + {sdiff}" else ""
        let st := if mem.isInaccessible obj.allocId then " (inaccessible)" else
          match obj.state with
          | .alive => ""
          | .dead => " (dead)"
          | .freed => " (dangling)"
        mem.objectDisplayName obj ++ off ++ st
      | none => "dangling"
    | none =>
      match p.prov with
      | .wildcard .. => "wildcard"
      | _ => "nullary"
  s!"ptr 0x{Hex.upper addr} [{tag}]"

/--
Verify whether a memory access of `accessSize` bytes with required `alignment` via `ptr` is valid.
Returns `(memoryObject, byteOffset)` or raises `ExecError.immediateUB` (matches `llubi::ExecutorBase::verifyMemAccess`).
Note: Loading from a `.dead` (out-of-lifetime) stack object is allowed and yields poison bytes,
whereas storing to a `.dead` object or accessing a `.freed` object is Immediate UB.
-/
def verifyMemAccess (mem : MemoryState) (ptr : Pointer) (accessSize alignment : Nat)
    (isStore : Bool) : Except ExecError (MemoryObject × Nat) :=
  match mem.resolveObject? ptr with
  | none =>
    .error (.immediateUB "Invalid memory access via a pointer with nullary provenance.")
  | some mo =>
    let badState := if isStore then mo.state != .alive else mo.state == .freed
    if mem.isInaccessible mo.allocId then
      .error (.immediateUB s!"Try to access an inaccessible memory object: {mem.ptrString ptr}.")
    else if badState then
      .error (.immediateUB s!"Try to access a dead memory object at address 0x{Hex.upper ptr.addr.toNat}.")
    else if isStore && mo.isConstant then
      .error (.immediateUB s!"Try to write to a constant memory object: {mem.ptrString ptr}.")
    else
      let effAlign := max 1 alignment
      let addr := ptr.addr.toNat
      let oob := s!"Memory access is out of bounds. Accessed size: {accessSize}, Address: 0x{Hex.upper addr}, Object base: 0x{Hex.upper mo.baseAddr}, Object size: {mo.size}."
      if addr % effAlign != 0 then
        .error (.immediateUB s!"Misaligned memory access. Address: 0x{Hex.upper addr}, Required alignment: {effAlign}.")
      else if accessSize > mo.size || addr < mo.baseAddr then
        .error (.immediateUB oob)
      else
        let offset := addr - mo.baseAddr
        if offset > mo.size - accessSize then
          .error (.immediateUB oob)
        else
          .ok (mo, offset)

/-- Read `len` raw bytes from `mo` starting at `offset` (returns poison bytes if `mo.state == .dead`). -/
def readObjectBytes (mo : MemoryObject) (offset len : Nat) : Array MemByte :=
  if mo.state == .dead then
    Array.replicate len MemByte.poison
  else
    Array.ofFn (n := len) fun i => mo.bytes.getD (offset + i.val) MemByte.poison

/-- Write `newBytes` into object `allocId` starting at `offset`. -/
def writeObjectBytes : MemoryState → AllocId → Nat → Array MemByte → MemoryState
  | ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc, wildcardResolved, inaccessible⟩,
    allocId, offset, newBytes =>
    match objects.get? allocId with
    | none =>
      ⟨nextAllocId, nextAddr, usedMem, objects, exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc, wildcardResolved, inaccessible⟩
    | some mo =>
      let rec go (i : Nat) : Nat → Array MemByte → Array MemByte
        | 0, arr => arr
        | rem + 1, arr =>
          let idx := offset + i
          let arr' := if h : idx < arr.size then arr.set idx (newBytes.getD i MemByte.poison) h else arr
          go (i + 1) rem arr'
      let updated := go 0 newBytes.size mo.bytes
      ⟨nextAllocId, nextAddr, usedMem, objects.insert allocId (moWithBytes mo updated),
       exposedGeneration, exposedProvenances, globalAddrs, funcAddrs, addrToFunc, wildcardResolved, inaccessible⟩

theorem writeObjectBytes_preserves_wf {mem : MemoryState} (hwf : WellFormed mem)
    (allocId offset : Nat) (newBytes : Array MemByte) :
    WellFormed (writeObjectBytes mem allocId offset newBytes) := by
  cases mem with
  | mk nextAllocId nextAddr usedMem objects exposedGeneration exposedProvenances globalAddrs funcAddrs addrToFunc wildcardResolved inaccessible =>
    simp only [writeObjectBytes]
    cases hget : objects.get? allocId with
    | none => exact hwf
    | some obj =>
      dsimp only
      refine ⟨hwf.nextAllocId_pos, hwf.nextAddr_ge, ?_⟩
      intro id mo hmo
      dsimp only at hmo ⊢
      rw [AssocMap.get?_insert] at hmo
      by_cases heq : (allocId == id) = true
      · simp only [heq, ↓reduceIte, Option.some.injEq] at hmo
        subst hmo
        have hid : allocId = id := eq_of_beq heq
        subst hid
        obtain ⟨h1, h2, h3, h4⟩ := hwf.objects_wf allocId obj hget
        cases obj
        exact ⟨h1, h2, h3, h4⟩
      · have hne : (allocId == id) = false := Bool.eq_false_iff.mpr heq
        simp only [hne, Bool.false_eq_true, ↓reduceIte] at hmo
        exact hwf.objects_wf id mo hmo

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

private theorem findExposed_in_objects {mem : MemoryState} {gen : Nat} {known? : Option AllocId}
    {addr : Nat} {mo : MemoryObject} :
    ∀ l, resolveObject?.findExposed mem gen known? addr l = some mo →
      ∃ id, mem.objects.get? id = some mo
  | [], h0 => by simp [resolveObject?.findExposed] at h0
  | (id, expGen) :: rest, h0 => by
    unfold resolveObject?.findExposed at h0
    split at h0
    · split at h0
      · rename_i m hobj
        split at h0
        · cases h0; exact ⟨id, hobj⟩
        · exact findExposed_in_objects rest h0
      · exact findExposed_in_objects rest h0
    · exact findExposed_in_objects rest h0

private theorem resolveObject?_in_objects {mem : MemoryState} {ptr : Pointer} {mo : MemoryObject}
    (h : mem.resolveObject? ptr = some mo) :
    ∃ id, mem.objects.get? id = some mo := by
  unfold resolveObject? at h
  cases hp : ptr.prov with
  | nullary => simp [hp] at h
  | concrete id => rw [hp] at h; exact ⟨id, h⟩
  | wildcard gen known? wid =>
    rw [hp] at h
    dsimp only at h
    cases hf : (if wid == 0 then none else mem.wildcardResolved.get? wid) with
    | some fixedId =>
      rw [hf] at h
      dsimp only at h
      split at h
      · cases hget : mem.objects.get? fixedId with
        | none => rw [hget] at h; cases h
        | some m =>
          rw [hget] at h; dsimp only at h
          split at h
          · cases h; exact ⟨fixedId, hget⟩
          · cases h
      · cases h
    | none =>
      rw [hf] at h
      exact findExposed_in_objects mem.exposedProvenances h

theorem lifetimeStart_preserves_wf {mem : MemoryState} (hwf : WellFormed mem)
    (cfg : SemanticsConfig) (ptr : Pointer) :
    WellFormed (lifetimeStart mem cfg ptr) := by
  unfold lifetimeStart
  cases hres : mem.resolveObject? ptr with
  | none => exact hwf
  | some mo =>
    dsimp only
    split
    · exact hwf
    · obtain ⟨id0, hget0⟩ := resolveObject?_in_objects hres
      obtain ⟨hid0, hlt0, hbase0, hbound0⟩ := hwf.objects_wf id0 mo hget0
      cases mem
      refine ⟨hwf.nextAllocId_pos, hwf.nextAddr_ge, ?_⟩
      intro id m hm
      dsimp only [withObjects] at hm ⊢
      rw [AssocMap.get?_insert] at hm
      by_cases heq : (mo.allocId == id) = true
      · simp only [heq, ↓reduceIte, Option.some.injEq] at hm
        subst hm
        have hid : mo.allocId = id := eq_of_beq heq
        subst hid
        cases mo
        exact ⟨rfl, by rw [hid0]; exact hlt0, hbase0, hbound0⟩
      · have hne : (mo.allocId == id) = false := Bool.eq_false_iff.mpr heq
        simp only [hne, Bool.false_eq_true, ↓reduceIte] at hm
        exact hwf.objects_wf id m hm

theorem lifetimeEnd_preserves_wf {mem : MemoryState} (hwf : WellFormed mem) (ptr : Pointer) :
    WellFormed (lifetimeEnd mem ptr) := by
  unfold lifetimeEnd
  cases hres : mem.resolveObject? ptr with
  | none => exact hwf
  | some mo =>
    dsimp only
    split
    · exact hwf
    · obtain ⟨id0, hget0⟩ := resolveObject?_in_objects hres
      obtain ⟨hid0, hlt0, hbase0, hbound0⟩ := hwf.objects_wf id0 mo hget0
      cases mem
      refine ⟨hwf.nextAllocId_pos, hwf.nextAddr_ge, ?_⟩
      intro id m hm
      dsimp only [withObjects] at hm ⊢
      rw [AssocMap.get?_insert] at hm
      by_cases heq : (mo.allocId == id) = true
      · simp only [heq, ↓reduceIte, Option.some.injEq] at hm
        subst hm
        have hid : mo.allocId = id := eq_of_beq heq
        subst hid
        cases mo
        exact ⟨rfl, by rw [hid0]; exact hlt0, hbase0, hbound0⟩
      · have hne : (mo.allocId == id) = false := Bool.eq_false_iff.mpr heq
        simp only [hne, Bool.false_eq_true, ↓reduceIte] at hm
        exact hwf.objects_wf id m hm

theorem insertGlobalAddr_preserves_wf {mem : MemoryState} (hwf : WellFormed mem)
    (name : AST.GlobalId) (ptr : Pointer) :
    WellFormed (insertGlobalAddr mem name ptr) := by
  cases mem; exact ⟨hwf.nextAllocId_pos, hwf.nextAddr_ge, hwf.objects_wf⟩

theorem insertFuncAddr_preserves_wf {mem : MemoryState} (hwf : WellFormed mem)
    (name : AST.FunctionId) (baseAddr : Nat) (ptr : Pointer) :
    WellFormed (insertFuncAddr mem name baseAddr ptr) := by
  cases mem; exact ⟨hwf.nextAllocId_pos, hwf.nextAddr_ge, hwf.objects_wf⟩

/-- Every allocation ID listed in `mem.allocIds` is strictly below `mem.nextAllocId`. -/
theorem allocId_lt_nextAllocId_of_mem_allocIds {mem : MemoryState}
    (hwf : WellFormed mem) {id : AllocId} (hid : id ∈ mem.allocIds) :
    id < mem.nextAllocId := by
  obtain ⟨mo, hget⟩ := AssocMap.get?_isSome_of_mem_keys mem.objects hid
  exact (hwf.objects_wf id mo hget).2.1

theorem objects_get?_writeObjectBytes_ne (mem : MemoryState) (aid offset : Nat)
    (bs : Array MemByte) {id : AllocId} (hne : aid ≠ id) :
    (mem.writeObjectBytes aid offset bs).objects.get? id = mem.objects.get? id := by
  cases mem with
  | mk nA nAd uM objs eG eP gA fA aF =>
    simp only [writeObjectBytes]
    cases objs.get? aid with
    | none => rfl
    | some mo =>
      dsimp only
      rw [AssocMap.get?_insert, beq_false_of_ne hne]; rfl

theorem objects_get?_freeObject_ne (mem : MemoryState) (aid : AllocId)
    {id : AllocId} (hne : aid ≠ id) :
    (mem.freeObject aid).objects.get? id = mem.objects.get? id := by
  cases mem with
  | mk nA nAd uM objs eG eP gA fA aF =>
    simp only [freeObject]
    cases objs.get? aid with
    | none => rfl
    | some mo =>
      dsimp only
      by_cases hf : (mo.state == .freed) = true
      · rw [if_pos hf]
      · rw [if_neg hf]
        dsimp only
        rw [AssocMap.get?_insert, beq_false_of_ne hne]; rfl

@[simp] theorem writeObjectBytes_inaccessible (mem : MemoryState) (aid off : Nat) (bs : Array MemByte) :
    (mem.writeObjectBytes aid off bs).inaccessible = mem.inaccessible := by
  cases mem; simp only [writeObjectBytes]; split <;> rfl

@[simp] theorem bindWildcard_inaccessible (mem : MemoryState) (prov : Provenance) (aid : AllocId) :
    (mem.bindWildcard prov aid).inaccessible = mem.inaccessible := by
  cases mem; simp only [bindWildcard]; repeat' split
  all_goals rfl

theorem verifyMemAccess_error_is_ub {mem : MemoryState} {ptr : Pointer}
    {accessSize alignment : Nat} {isStore : Bool} {err : ExecError}
    (h : mem.verifyMemAccess ptr accessSize alignment isStore = .error err) :
    ∃ msg, err = .immediateUB msg := by
  unfold verifyMemAccess at h
  cases hres : mem.resolveObject? ptr with
  | none => rw [hres] at h; cases h; exact ⟨_, rfl⟩
  | some mo =>
    rw [hres] at h; dsimp only at h
    by_cases h0 : mem.isInaccessible mo.allocId = true
    · rw [if_pos h0] at h; cases h; exact ⟨_, rfl⟩
    rw [if_neg h0] at h
    by_cases h1 : (if isStore = true then mo.state != MemoryObjectState.alive else mo.state == MemoryObjectState.freed) = true
    · rw [if_pos h1] at h; cases h; exact ⟨_, rfl⟩
    · rw [if_neg h1] at h
      by_cases h2 : (isStore && mo.isConstant) = true
      · rw [if_pos h2] at h; cases h; exact ⟨_, rfl⟩
      · rw [if_neg h2] at h
        by_cases h3 : (ptr.addr.toNat % max 1 alignment != 0) = true
        · rw [if_pos h3] at h; cases h; exact ⟨_, rfl⟩
        · rw [if_neg h3] at h
          by_cases h4 : (decide (accessSize > mo.size) || decide (ptr.addr.toNat < mo.baseAddr)) = true
          · rw [if_pos h4] at h; cases h; exact ⟨_, rfl⟩
          · rw [if_neg h4] at h
            by_cases h5 : ptr.addr.toNat - mo.baseAddr > mo.size - accessSize
            · rw [if_pos h5] at h; cases h; exact ⟨_, rfl⟩
            · rw [if_neg h5] at h; cases h

theorem resolveObject?_writeObjectBytes_same {mem : MemoryState}
    (hwf : WellFormed mem) {ptr : Pointer} {mo : MemoryObject}
    (hres : mem.resolveObject? ptr = some mo) (offset : Nat) (bs : Array MemByte) :
    let mo' := { mo with bytes := writeObjectBytes.go offset bs 0 bs.size mo.bytes }
    (mem.writeObjectBytes mo.allocId offset bs).resolveObject? ptr = some mo' := by
  intro mo'
  have hgetSame : mem.objects.get? mo.allocId = some mo := by
    obtain ⟨aid, haid⟩ := resolveObject?_in_objects hres
    have hid := (hwf.objects_wf aid mo haid).1
    rw [hid]; exact haid
  have hmoEq : moWithBytes mo (writeObjectBytes.go offset bs 0 bs.size mo.bytes) = mo' := by
    cases mo; rfl
  have hgetWrite : ∀ id, (mem.writeObjectBytes mo.allocId offset bs).objects.get? id =
      if mo.allocId == id then some mo' else mem.objects.get? id := by
    intro id
    cases mem with
    | mk nA nAd uM objs eG eP gA fA aF =>
      dsimp only [writeObjectBytes] at hgetSame ⊢
      rw [hgetSame]; dsimp only
      rw [hmoEq, AssocMap.get?_insert]
  cases hp : ptr.prov with
  | nullary => simp [resolveObject?, hp] at hres
  | concrete aid =>
    simp only [resolveObject?, hp] at hres ⊢
    have hid := (hwf.objects_wf aid mo hres).1
    rw [hgetWrite aid, hid, beq_self_eq_true]; rfl
  | wildcard gen known? wid =>
    simp only [resolveObject?, hp] at hres ⊢
    have hexp : (mem.writeObjectBytes mo.allocId offset bs).exposedProvenances = mem.exposedProvenances := by
      cases mem; dsimp only [writeObjectBytes] at hgetSame ⊢; rw [hgetSame]
    have hwr : (mem.writeObjectBytes mo.allocId offset bs).wildcardResolved = mem.wildcardResolved := by
      cases mem; dsimp only [writeObjectBytes] at hgetSame ⊢; rw [hgetSame]
    rw [hexp, hwr]
    cases hf : (if wid == 0 then none else mem.wildcardResolved.get? wid) with
    | some fixedId =>
      rw [hf] at hres
      dsimp only at hres ⊢
      by_cases hkn : (known?.map (fun x => x == fixedId)).getD true = true
      · rw [if_pos hkn] at hres ⊢
        rw [hgetWrite fixedId]
        by_cases hid : (mo.allocId == fixedId) = true
        · rw [if_pos hid]
          have hidEq : mo.allocId = fixedId := eq_of_beq hid
          rw [← hidEq, hgetSame] at hres
          dsimp only at hres ⊢
          by_cases hok : (mo.state != MemoryObjectState.freed && mo.inBounds ptr.addr.toNat) = true
          · have hok' : (mo'.state != MemoryObjectState.freed && mo'.inBounds ptr.addr.toNat) = true := hok
            rw [if_pos hok']
          · rw [if_neg hok] at hres; cases hres
        · rw [if_neg hid]
          cases hobj : mem.objects.get? fixedId with
          | none => rw [hobj] at hres; cases hres
          | some m =>
            rw [hobj] at hres; dsimp only at hres ⊢
            by_cases hok : (m.state != MemoryObjectState.freed && m.inBounds ptr.addr.toNat) = true
            · rw [if_pos hok] at hres; cases hres
              have hcontra := (hwf.objects_wf fixedId mo hobj).1
              exact False.elim (hid (by simp [hcontra]))
            · rw [if_neg hok] at hres; cases hres
      · rw [if_neg hkn] at hres; cases hres
    | none =>
      rw [hf] at hres
      dsimp only at hres ⊢
      have hgo : ∀ l, resolveObject?.findExposed mem gen known? ptr.addr.toNat l = some mo →
          resolveObject?.findExposed (mem.writeObjectBytes mo.allocId offset bs) gen known? ptr.addr.toNat l = some mo' := by
        intro l
        induction l with
        | nil => intro h; simp [resolveObject?.findExposed] at h
        | cons hd rest ih =>
          obtain ⟨id, expGen⟩ := hd
          intro h
          unfold resolveObject?.findExposed at h ⊢
          by_cases hcond : (decide (expGen ≤ gen) && (known?.map (fun x => x == id)).getD true) = true
          · rw [if_pos hcond] at h ⊢
            rw [hgetWrite id]
            by_cases hid : (mo.allocId == id) = true
            · rw [if_pos hid]
              have hidEq : mo.allocId = id := eq_of_beq hid
              rw [← hidEq, hgetSame] at h
              dsimp only at h ⊢
              by_cases hok : (mo.state != MemoryObjectState.freed && mo.inBounds ptr.addr.toNat) = true
              · have hok' : (mo'.state != MemoryObjectState.freed && mo'.inBounds ptr.addr.toNat) = true := hok
                rw [if_pos hok']
              · have hok' : ¬ (mo'.state != MemoryObjectState.freed && mo'.inBounds ptr.addr.toNat) = true := hok
                rw [if_neg hok] at h
                rw [if_neg hok']
                exact ih h
            · rw [if_neg hid]
              cases hobj : mem.objects.get? id with
              | none => rw [hobj] at h; exact ih h
              | some m =>
                rw [hobj] at h; dsimp only at h ⊢
                by_cases hok : (m.state != MemoryObjectState.freed && m.inBounds ptr.addr.toNat) = true
                · rw [if_pos hok] at h ⊢
                  cases h
                  have hcontra := (hwf.objects_wf id mo hobj).1
                  exact False.elim (hid (by simp [hcontra]))
                · rw [if_neg hok] at h ⊢; exact ih h
          · rw [if_neg hcond] at h ⊢; exact ih h
      exact hgo mem.exposedProvenances hres

theorem verifyMemAccess_writeObjectBytes_same {mem : MemoryState}
    (hwf : WellFormed mem) {ptr : Pointer} {accessSize alignment : Nat}
    {isStore : Bool} {mo : MemoryObject} {offset : Nat}
    (hver : mem.verifyMemAccess ptr accessSize alignment isStore = .ok (mo, offset))
    (wOff : Nat) (bs : Array MemByte) :
    let mo' := { mo with bytes := writeObjectBytes.go wOff bs 0 bs.size mo.bytes }
    (mem.writeObjectBytes mo.allocId wOff bs).verifyMemAccess ptr accessSize alignment isStore = .ok (mo', offset) := by
  intro mo'
  unfold verifyMemAccess at hver ⊢
  cases hres : mem.resolveObject? ptr with
  | none => rw [hres] at hver; cases hver
  | some mo0 =>
    rw [hres] at hver; dsimp only at hver
    by_cases h0 : mem.isInaccessible mo0.allocId = true
    · rw [if_pos h0] at hver; cases hver
    rw [if_neg h0] at hver
    by_cases h1 : (if isStore = true then mo0.state != MemoryObjectState.alive else mo0.state == MemoryObjectState.freed) = true
    · rw [if_pos h1] at hver; cases hver
    · rw [if_neg h1] at hver
      by_cases h2 : (isStore && mo0.isConstant) = true
      · rw [if_pos h2] at hver; cases hver
      · rw [if_neg h2] at hver
        by_cases h3 : (ptr.addr.toNat % max 1 alignment != 0) = true
        · rw [if_pos h3] at hver; cases hver
        · rw [if_neg h3] at hver
          by_cases h4 : (decide (accessSize > mo0.size) || decide (ptr.addr.toNat < mo0.baseAddr)) = true
          · rw [if_pos h4] at hver; cases hver
          · rw [if_neg h4] at hver
            by_cases h5 : ptr.addr.toNat - mo0.baseAddr > mo0.size - accessSize
            · rw [if_pos h5] at hver; cases hver
            · rw [if_neg h5] at hver
              cases hver
              have hres1 := resolveObject?_writeObjectBytes_same hwf hres wOff bs
              rw [hres1]; dsimp only
              rw [if_neg (by rw [isInaccessible, writeObjectBytes_inaccessible]; exact h0),
                if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]

@[simp]
theorem bindWildcard_concrete (mem : MemoryState) (a b : AllocId) :
    mem.bindWildcard (.concrete a) b = mem := by
  cases mem; rfl

theorem bindWildcard_idemp (mem : MemoryState) (p : Provenance) (a : AllocId) :
    (mem.bindWildcard p a).bindWildcard p a = mem.bindWildcard p a := by
  cases mem with
  | mk nextAllocId nextAddr usedMem objects exposedGeneration exposedProvenances globalAddrs funcAddrs addrToFunc wildcardResolved inaccessible =>
    cases p with
    | nullary | concrete _ => rfl
    | wildcard _ _ wid =>
      dsimp only [bindWildcard]
      by_cases h0 : (wid == 0) = true
      · simp [h0]
      · simp only [h0, Bool.false_eq_true, ↓reduceIte]
        cases hget : wildcardResolved.get? wid with
        | some _ => simp [hget]
        | none => simp [AssocMap.get?_insert]

theorem bindWildcard_writeObjectBytes_comm (mem : MemoryState) (aid off : Nat) (bs : Array MemByte)
    (p : Provenance) (a : AllocId) :
    (mem.writeObjectBytes aid off bs).bindWildcard p a =
    (mem.bindWildcard p a).writeObjectBytes aid off bs := by
  cases mem with
  | mk nextAllocId nextAddr usedMem objects exposedGeneration exposedProvenances globalAddrs funcAddrs addrToFunc wildcardResolved inaccessible =>
    cases p with
    | nullary | concrete _ => rfl
    | wildcard _ _ wid =>
      dsimp only [writeObjectBytes]
      cases hobj : objects.get? aid with
      | none =>
        dsimp only [bindWildcard]
        by_cases h0 : (wid == 0) = true
        · simp [h0, hobj]
        · simp only [h0, Bool.false_eq_true, ↓reduceIte]
          cases wildcardResolved.get? wid <;> simp [hobj]
      | some mo =>
        dsimp only [bindWildcard]
        by_cases h0 : (wid == 0) = true
        · simp [h0, hobj]
        · simp only [h0, Bool.false_eq_true, ↓reduceIte]
          cases wildcardResolved.get? wid <;> simp [hobj]

private theorem findExposed_props {mem : MemoryState} {gen : Nat} {known? : Option AllocId}
    {addr : Nat} {mo : MemoryObject} (hwf : WellFormed mem) :
    ∀ l, resolveObject?.findExposed mem gen known? addr l = some mo →
      (known?.map (· == mo.allocId)).getD true = true ∧
      mem.objects.get? mo.allocId = some mo ∧
      (mo.state != MemoryObjectState.freed && mo.inBounds addr) = true
  | [], h => by simp [resolveObject?.findExposed] at h
  | (id, expGen) :: rest, h => by
    unfold resolveObject?.findExposed at h
    split at h
    · rename_i hcond
      cases hobj : mem.objects.get? id with
      | none => rw [hobj] at h; exact findExposed_props hwf rest h
      | some m =>
        rw [hobj] at h; dsimp only at h
        split at h
        · rename_i hok
          cases h
          have hid := (hwf.objects_wf id mo hobj).1
          rw [hid]
          simp only [Bool.and_eq_true] at hcond
          exact ⟨hcond.2, hobj, hok⟩
        · exact findExposed_props hwf rest h
    · exact findExposed_props hwf rest h

theorem resolveObject?_bindWildcard_same {mem : MemoryState} (hwf : WellFormed mem)
    {ptr : Pointer} {mo : MemoryObject}
    (hres : mem.resolveObject? ptr = some mo) :
    (mem.bindWildcard ptr.prov mo.allocId).resolveObject? ptr = some mo := by
  cases mem with
  | mk nextAllocId nextAddr usedMem objects exposedGeneration exposedProvenances globalAddrs funcAddrs addrToFunc wildcardResolved inaccessible =>
    unfold resolveObject? at hres ⊢
    cases hp : ptr.prov with
    | nullary => simp [hp] at hres
    | concrete id => simp [hp, bindWildcard] at hres ⊢; exact hres
    | wildcard gen known? wid =>
      simp only [hp, bindWildcard] at hres ⊢
      by_cases h0 : (wid == 0) = true
      · simp only [h0, ↓reduceIte] at hres ⊢; exact hres
      · simp only [h0, Bool.false_eq_true, ↓reduceIte] at hres ⊢
        cases hget : wildcardResolved.get? wid with
        | some fixedId =>
          rw [hget] at hres; dsimp only at hres ⊢
          rw [hget]; exact hres
        | none =>
          rw [hget] at hres; dsimp only at hres
          rw [AssocMap.get?_insert, beq_self_eq_true]
          simp only [↓reduceIte]
          obtain ⟨hkn, hobj, hok⟩ := findExposed_props hwf exposedProvenances hres
          dsimp only at hobj
          rw [if_pos hkn, hobj]; dsimp only; rw [if_pos hok]

theorem verifyMemAccess_bindWildcard_same {mem : MemoryState} (hwf : WellFormed mem)
    {ptr : Pointer} {accessSize alignment : Nat} {isStore : Bool} {mo : MemoryObject} {offset : Nat}
    (hver : mem.verifyMemAccess ptr accessSize alignment isStore = .ok (mo, offset)) :
    (mem.bindWildcard ptr.prov mo.allocId).verifyMemAccess ptr accessSize alignment isStore = .ok (mo, offset) := by
  unfold verifyMemAccess at hver ⊢
  cases hres : mem.resolveObject? ptr with
  | none => rw [hres] at hver; cases hver
  | some mo0 =>
    rw [hres] at hver; dsimp only at hver
    by_cases h0 : mem.isInaccessible mo0.allocId = true
    · rw [if_pos h0] at hver; cases hver
    rw [if_neg h0] at hver
    by_cases h1 : (if isStore = true then mo0.state != MemoryObjectState.alive else mo0.state == MemoryObjectState.freed) = true
    · rw [if_pos h1] at hver; cases hver
    · rw [if_neg h1] at hver
      by_cases h2 : (isStore && mo0.isConstant) = true
      · rw [if_pos h2] at hver; cases hver
      · rw [if_neg h2] at hver
        by_cases h3 : (ptr.addr.toNat % max 1 alignment != 0) = true
        · rw [if_pos h3] at hver; cases hver
        · rw [if_neg h3] at hver
          by_cases h4 : (decide (accessSize > mo0.size) || decide (ptr.addr.toNat < mo0.baseAddr)) = true
          · rw [if_pos h4] at hver; cases hver
          · rw [if_neg h4] at hver
            by_cases h5 : ptr.addr.toNat - mo0.baseAddr > mo0.size - accessSize
            · rw [if_pos h5] at hver; cases hver
            · rw [if_neg h5] at hver
              cases hver
              rw [resolveObject?_bindWildcard_same hwf hres]; dsimp only
              rw [if_neg (by rw [isInaccessible, bindWildcard_inaccessible]; exact h0),
                if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]

theorem writeObjectBytes_overwrite_singleton (mem : MemoryState) (aid offset : Nat)
    (b1 b2 : MemByte) :
    (mem.writeObjectBytes aid offset #[b1]).writeObjectBytes aid offset #[b2] =
      mem.writeObjectBytes aid offset #[b2] := by
  cases mem with
  | mk nA nAd uM objs eG eP gA fA aF =>
    simp only [writeObjectBytes]
    cases hget : objs.get? aid with
    | none => simp [hget]
    | some mo =>
      dsimp only
      rw [AssocMap.get?_insert, beq_self_eq_true]
      simp only [↓reduceIte, moWithBytes, AssocMap.insert_insert_same]
      have hsz1 : (#[b1] : Array MemByte).size = 1 := rfl
      have hsz2 : (#[b2] : Array MemByte).size = 1 := rfl
      rw [hsz1, hsz2]
      dsimp only [writeObjectBytes.go]
      cases mo with
      | mk mId mBase mSz mAl mAs mNm mSt mAk mC mBs =>
        dsimp only
        by_cases hlt : offset < mBs.size
        · simp only [Nat.add_zero, hlt, ↓reduceDIte, Array.size_set, Array.set_set]
        · simp only [Nat.add_zero, hlt, ↓reduceDIte]

end MemoryState

/-! ### Memory Injections & Bit/Byte/Memory Refinement (CompCert / Alive2 style) -/

/--
Partial bijection mapping source `AllocId`s to target `AllocId`s,
used to relate pointers, memory bytes, and traces across optimizations that add, remove,
or reorder internal allocations (`alloca` / `malloc`).
-/
structure MemoryInjection : Type where
  map       : AllocId → Option AllocId
  injective : ∀ a1 a2 b, map a1 = some b → map a2 = some b → a1 = a2

namespace MemoryInjection

/-- Identity injection (`id ↦ some id`). -/
def id : MemoryInjection where
  map := some
  injective := by
    intro a1 a2 b h1 h2
    cases h1
    cases h2
    rfl

/-- Composition of injections (`f` maps `x → y`, `g` maps `y → z`, yielding `x → z`). -/
def comp (f g : MemoryInjection) : MemoryInjection where
  map := fun a => (f.map a).bind g.map
  injective := by
    intro a1 a2 b h1 h2
    cases hf1 : f.map a1 with
    | none => simp [hf1] at h1
    | some m1 =>
      rw [hf1] at h1
      cases hf2 : f.map a2 with
      | none => simp [hf2] at h2
      | some m2 =>
        rw [hf2] at h2
        have hm : m1 = m2 := g.injective m1 m2 b h1 h2
        subst hm
        exact f.injective a1 a2 m1 hf1 hf2

/-- An injection fixes every allocation ID in `ids` to itself (caller-owned / global objects). -/
def IdOn (inj : MemoryInjection) (ids : List AllocId) : Prop :=
  ∀ id ∈ ids, inj.map id = some id

theorem id_idOn (ids : List AllocId) : id.IdOn ids := by
  intro _ _; rfl

theorem comp_idOn {f g : MemoryInjection} {ids : List AllocId}
    (hf : f.IdOn ids) (hg : g.IdOn ids) : (comp f g).IdOn ids := by
  intro i hi
  simp [comp, hf i hi, hg i hi]

/-- `inj1.Extends inj2` means `inj2` agrees with `inj1` on every allocation mapped by `inj1`. -/
def Extends (inj1 inj2 : MemoryInjection) : Prop :=
  ∀ a b, inj1.map a = some b → inj2.map a = some b

theorem Extends.refl (inj : MemoryInjection) : inj.Extends inj :=
  fun _ _ h => h

theorem Extends.trans {inj1 inj2 inj3 : MemoryInjection}
    (h12 : inj1.Extends inj2) (h23 : inj2.Extends inj3) : inj1.Extends inj3 :=
  fun a b h => h23 a b (h12 a b h)

theorem Extends.idOn {inj1 inj2 : MemoryInjection} {ids : List AllocId}
    (hext : inj1.Extends inj2) (hid : inj1.IdOn ids) : inj2.IdOn ids :=
  fun id h => hext id id (hid id h)

end MemoryInjection

/-- Provenance refinement under a `MemoryInjection` (source `ps` is refined by target `pt`). -/
def Provenance.IsRefinedBy (inj : MemoryInjection) : Provenance → Provenance → Prop
  | .nullary, .nullary => True
  | .concrete aS, .concrete aT => inj.map aS = some aT
  | .wildcard _ ks _, .wildcard _ kt _ =>
    match ks, kt with
    | some aS, some aT => inj.map aS = some aT
    | none, some _ => True
    | none, none => True
    | some _, none => False
  | _, _ => False

theorem Provenance.IsRefinedBy.refl (p : Provenance) : Provenance.IsRefinedBy .id p p := by
  cases p with
  | nullary => trivial
  | concrete _ => rfl
  | wildcard _ k _ => cases k <;> trivial

theorem Provenance.IsRefinedBy.mono {f g : MemoryInjection} {p1 p2 : Provenance}
    (hext : f.Extends g) (h : Provenance.IsRefinedBy f p1 p2) :
    Provenance.IsRefinedBy g p1 p2 := by
  cases p1 <;> cases p2
  all_goals simp only [Provenance.IsRefinedBy] at h ⊢
  all_goals try exact h
  · exact hext _ _ h
  · rename_i k1 _ _ k2 _
    cases k1 <;> cases k2
    all_goals dsimp only at h ⊢
    all_goals try exact h
    exact hext _ _ h

theorem Provenance.IsRefinedBy.trans {f g : MemoryInjection} {p1 p2 p3 : Provenance}
    (h12 : Provenance.IsRefinedBy f p1 p2) (h23 : Provenance.IsRefinedBy g p2 p3) :
    Provenance.IsRefinedBy (f.comp g) p1 p3 := by
  cases p1 <;> cases p2 <;> cases p3
  all_goals simp only [Provenance.IsRefinedBy] at h12 h23 ⊢
  all_goals try exact trivial
  all_goals try exact False.elim h12
  all_goals try exact False.elim h23
  · simp [MemoryInjection.comp, h12, h23]
  · rename_i k1 _ _ k2 _ _ k3 _
    cases k1 <;> cases k2 <;> cases k3 <;> simp_all [MemoryInjection.comp]

/-- Pointer refinement under a `MemoryInjection` (matching address bitvector and refined provenance). -/
def Pointer.IsRefinedBy (inj : MemoryInjection) (ps pt : Pointer) : Prop :=
  (∃ h : ps.addrWidth = pt.addrWidth, h ▸ ps.addr = pt.addr) ∧
  Provenance.IsRefinedBy inj ps.prov pt.prov

theorem Pointer.IsRefinedBy.refl (p : Pointer) : Pointer.IsRefinedBy .id p p :=
  ⟨⟨rfl, rfl⟩, Provenance.IsRefinedBy.refl p.prov⟩

theorem Pointer.IsRefinedBy.mono {f g : MemoryInjection} {p1 p2 : Pointer}
    (hext : f.Extends g) (h : Pointer.IsRefinedBy f p1 p2) :
    Pointer.IsRefinedBy g p1 p2 :=
  ⟨h.1, Provenance.IsRefinedBy.mono hext h.2⟩

theorem Pointer.IsRefinedBy.trans {f g : MemoryInjection} {p1 p2 p3 : Pointer}
    (h12 : Pointer.IsRefinedBy f p1 p2) (h23 : Pointer.IsRefinedBy g p2 p3) :
    Pointer.IsRefinedBy (f.comp g) p1 p3 := by
  obtain ⟨⟨hw12, ha12⟩, hp12⟩ := h12
  obtain ⟨⟨hw23, ha23⟩, hp23⟩ := h23
  refine ⟨⟨hw12.trans hw23, ?_⟩, Provenance.IsRefinedBy.trans hp12 hp23⟩
  cases p1; cases p2; cases p3
  dsimp only at hw12 hw23 ha12 ha23 ⊢
  subst hw12; subst hw23
  exact ha12.trans ha23

/-- Single memory-bit refinement (`poison`/`undef` in source are refined by anything;
concrete bits must match under `inj`). -/
def MemBit.IsRefinedBy (inj : MemoryInjection) : MemBit → MemBit → Prop
  | .poison, _ => True
  | .undef, _ => True
  | .concrete bs ps, .concrete bt pt =>
    bs = bt ∧
    match ps, pt with
    | none, none => True
    | some (p1, i1), some (p2, i2) => i1 = i2 ∧ Provenance.IsRefinedBy inj p1 p2
    | _, _ => False
  | _, _ => False

theorem MemBit.IsRefinedBy.refl (b : MemBit) : MemBit.IsRefinedBy .id b b := by
  cases b with
  | poison => trivial
  | undef => trivial
  | concrete bit pb =>
    refine ⟨rfl, ?_⟩
    cases pb with
    | none => trivial
    | some p => exact ⟨rfl, Provenance.IsRefinedBy.refl p.1⟩

theorem MemBit.IsRefinedBy.mono {f g : MemoryInjection} {b1 b2 : MemBit}
    (hext : f.Extends g) (h : MemBit.IsRefinedBy f b1 b2) :
    MemBit.IsRefinedBy g b1 b2 := by
  cases b1 with
  | poison => trivial
  | undef => trivial
  | concrete bs ps =>
    cases b2 with
    | poison => cases h
    | undef => cases h
    | concrete bt pt =>
      refine ⟨h.1, ?_⟩
      cases ps <;> cases pt
      all_goals dsimp only at h ⊢
      all_goals try exact h.2
      exact ⟨h.2.1, Provenance.IsRefinedBy.mono hext h.2.2⟩

theorem MemBit.IsRefinedBy.trans {f g : MemoryInjection} {b1 b2 b3 : MemBit}
    (h12 : MemBit.IsRefinedBy f b1 b2) (h23 : MemBit.IsRefinedBy g b2 b3) :
    MemBit.IsRefinedBy (f.comp g) b1 b3 := by
  cases b1 with
  | poison => trivial
  | undef => trivial
  | concrete bs ps =>
    cases b2 with
    | poison => cases h12
    | undef => cases h12
    | concrete bm pm =>
      cases b3 with
      | poison => cases h23
      | undef => cases h23
      | concrete bt pt =>
        obtain ⟨hb12, hp12⟩ := h12
        obtain ⟨hb23, hp23⟩ := h23
        refine ⟨hb12.trans hb23, ?_⟩
        cases ps <;> cases pm <;> cases pt
        all_goals dsimp only at hp12 hp23 ⊢
        all_goals try exact trivial
        all_goals try exact False.elim hp12
        all_goals try exact False.elim hp23
        exact ⟨hp12.1.trans hp23.1, Provenance.IsRefinedBy.trans hp12.2 hp23.2⟩

/-- Byte-level memory refinement (all 8 bits of source `bs` are refined by those of target `bt`). -/
def MemByte.IsRefinedBy (inj : MemoryInjection) (bs bt : MemByte) : Prop :=
  ∀ i < 8, MemBit.IsRefinedBy inj (bs.getBit i) (bt.getBit i)

theorem MemByte.IsRefinedBy.refl (b : MemByte) : MemByte.IsRefinedBy .id b b :=
  fun i _ => MemBit.IsRefinedBy.refl (b.getBit i)

theorem MemByte.IsRefinedBy.mono {f g : MemoryInjection} {b1 b2 : MemByte}
    (hext : f.Extends g) (h : MemByte.IsRefinedBy f b1 b2) :
    MemByte.IsRefinedBy g b1 b2 :=
  fun i hi => MemBit.IsRefinedBy.mono hext (h i hi)

theorem MemByte.IsRefinedBy.trans {f g : MemoryInjection} {b1 b2 b3 : MemByte}
    (h12 : MemByte.IsRefinedBy f b1 b2) (h23 : MemByte.IsRefinedBy g b2 b3) :
    MemByte.IsRefinedBy (f.comp g) b1 b3 :=
  fun i hi => MemBit.IsRefinedBy.trans (h12 i hi) (h23 i hi)

/--
Caller-visible memory refinement (source `memS` is refined by target `memT` on all `callerIds`
under `inj`).
Every caller/global allocation in `callerIds` must exist with identical size and lifecycle state,
and its byte contents in `memS` must be refined by those in `memT` under `inj`.
Internal allocations (`alloca` / non-leaked `malloc`) outside `callerIds` may differ freely.
-/
def MemoryState.IsRefinedBy (inj : MemoryInjection) (callerIds : List AllocId)
    (memS memT : MemoryState) : Prop :=
  ∀ id ∈ callerIds,
    match memS.objects.get? id, memT.objects.get? id with
    | some moS, some moT =>
      moS.size = moT.size ∧
      moS.state = moT.state ∧
      (moS.state ≠ .freed →
        ∀ i < moS.size,
          MemByte.IsRefinedBy inj (moS.bytes.getD i MemByte.poison) (moT.bytes.getD i MemByte.poison))
    | none, none => True
    | _, _ => False

theorem MemoryState.IsRefinedBy.refl (callerIds : List AllocId) (mem : MemoryState) :
    MemoryState.IsRefinedBy .id callerIds mem mem := by
  intro id _
  cases mem.objects.get? id with
  | none => trivial
  | some mo => exact ⟨rfl, rfl, fun _ i _ => MemByte.IsRefinedBy.refl _⟩

theorem MemoryState.IsRefinedBy.mono {f g : MemoryInjection} {callerIds : List AllocId}
    {m1 m2 : MemoryState} (hext : f.Extends g) (h : MemoryState.IsRefinedBy f callerIds m1 m2) :
    MemoryState.IsRefinedBy g callerIds m1 m2 := by
  intro id hid
  have r := h id hid
  cases hm1 : m1.objects.get? id <;> cases hm2 : m2.objects.get? id
  all_goals simp only [hm1, hm2] at r ⊢
  all_goals try exact r
  exact ⟨r.1, r.2.1, fun hnf i hi => MemByte.IsRefinedBy.mono hext (r.2.2 hnf i hi)⟩

theorem MemoryState.IsRefinedBy.trans {f g : MemoryInjection} {callerIds : List AllocId}
    {m1 m2 m3 : MemoryState}
    (h12 : MemoryState.IsRefinedBy f callerIds m1 m2)
    (h23 : MemoryState.IsRefinedBy g callerIds m2 m3) :
    MemoryState.IsRefinedBy (f.comp g) callerIds m1 m3 := by
  intro id hid
  have r12 := h12 id hid
  have r23 := h23 id hid
  cases hm1 : m1.objects.get? id with
  | none =>
    cases hm2 : m2.objects.get? id with
    | none =>
      cases hm3 : m3.objects.get? id with
      | none => trivial
      | some _ => simp [hm2, hm3] at r23
    | some _ => simp [hm1, hm2] at r12
  | some mo1 =>
    cases hm2 : m2.objects.get? id with
    | none => simp [hm1, hm2] at r12
    | some mo2 =>
      cases hm3 : m3.objects.get? id with
      | none => simp [hm2, hm3] at r23
      | some mo3 =>
        simp only [hm1, hm2, hm3] at r12 r23 ⊢
        obtain ⟨hs12, hst12, hb12⟩ := r12
        obtain ⟨hs23, hst23, hb23⟩ := r23
        refine ⟨hs12.trans hs23, hst12.trans hst23, ?_⟩
        intro hnf i hi
        have hnf2 : mo2.state ≠ MemoryObjectState.freed := by rw [← hst12]; exact hnf
        have hi2 : i < mo2.size := by rw [← hs12]; exact hi
        exact MemByte.IsRefinedBy.trans (hb12 hnf i hi) (hb23 hnf2 i hi2)

end LeanNanoLlvm.Semantics
