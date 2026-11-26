import LeanNanoLlvm.Util.Config
import LeanNanoLlvm.Util.Undef
import LeanNanoLlvm.Util.AssocMap
import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.DataLayout
import LeanNanoLlvm.AST.Print
import LeanNanoLlvm.Semantics.IntOps
import LeanNanoLlvm.Semantics.FloatOps
import LeanNanoLlvm.Semantics.Memory
import LeanNanoLlvm.Llubi.FloatFormat

namespace LeanNanoLlvm.Semantics

open AST

/--
Runtime SSA value representation covering all first-class LLVM IR types
(mirrors `llubi::AnyValue`).
-/
inductive RegisterValue : Type where
  | bv     (w : Nat) (val : IntW w)
  | byte   (w : Nat) (bits : List MemBit)
  | float  (ft : FloatType) (val : FloatW ft)
  | ptr    (addrSpace : Nat) (val : PoisonOr Pointer)
  | vector (elemTy : LlvmType) (elems : List RegisterValue)
  | array  (elemTy : LlvmType) (elems : List RegisterValue)
  | struct (packed : Bool) (fieldTys : List LlvmType) (fields : List RegisterValue)
  | void

namespace RegisterValue

mutual
def toStringAux : RegisterValue → String
  | .bv _ .poison => "poison"
  | .bv _ (.value v) => s!"{v}"
  | .byte w bits =>
    let bitStr := String.ofList (bits.reverse.map fun
      | .concrete true _ => '1'
      | .concrete false _ => '0'
      | .poison | .undef => '!')
    s!"b{w} {bitStr}"
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

/-! ### Provenance tags (executable-only, `llubi`'s `Context::getTag`) -/

mutual
/-- `(allocId, addrWidth)` of the memory objects of the pointers inside a value, in serialization
order (the objects whose provenance tag `llubi` needs when the value is written as bytes). -/
def taggedPtrs : RegisterValue → List (Nat × Nat)
  | .ptr _ (.value p) =>
    match p.prov with
    | .concrete id => [(id, p.addrWidth)]
    | .wildcard _ (some id) _ => [(id, p.addrWidth)]
    | _ => []
  | .vector _ es => taggedPtrsList es
  | .array _ es => taggedPtrsList es
  | .struct _ _ es => taggedPtrsList es
  | _ => []

def taggedPtrsList : List RegisterValue → List (Nat × Nat)
  | [] => []
  | v :: vs => taggedPtrs v ++ taggedPtrsList vs
end

/-- Draw a provenance tag for object `id` unless it has one (a random `w`-bit value, redrawn
while zero or already used). Tags only record `llubi`'s random-stream consumption and its
printing; they have no semantic effect. -/
def _root_.LeanNanoLlvm.Semantics.drawTag (id w : Nat) (o : OracleState) : OracleState :=
  if o.tags.any (fun (q : Nat × Nat) => q.1 == id) then o
  else
    let rec go : Nat → OracleState → OracleState
      | 0, o0 => o0
      | fuel + 1, o0 =>
        match o0.nextBitVec w with
        | (tg, o1) =>
          if tg.toNat == 0 || o1.tags.any (fun (q : Nat × Nat) => q.2 == tg.toNat) then go fuel o1
          else { o1 with tags := o1.tags ++ [(id, tg.toNat)] }
    go 8 o

/-- Draw the provenance tags needed to serialize `v`. -/
def _root_.LeanNanoLlvm.Semantics.drawPtrTags (v : RegisterValue) (o : OracleState) : OracleState :=
  (taggedPtrs v).foldl (fun o0 (q : Nat × Nat) => drawTag q.1 q.2 o0) o

/-! ### `llubi`-compatible rendering (`llvm::ubi::AnyValue::print`) -/

/-- Value of LSB-first concrete bits (non-concrete bits count as 0). -/
def bitsValue (bits : List MemBit) : Nat :=
  bits.foldr (fun b acc => acc * 2 + (match b with | .concrete true _ => 1 | _ => 0)) 0

/-- `PrintByte` of `ByteValue::print` for one chunk (`bits` LSB-first, at most 8 bits). -/
def llubiByteChunk (bits : List MemBit) (full : Bool) (tags : List (Nat × Nat) := []) : String :=
  let allConcreteNoTag := bits.all fun | .concrete _ none => true | _ => false
  let allPoison := bits.all fun | .concrete .. => false | _ => true
  if full && allConcreteNoTag then "0x" ++ Llubi.hexPadded 2 (bitsValue bits)
  else if full && allPoison then "0x!!"
  else
    let msbFirst := bits.reverse
    let body := String.ofList (msbFirst.map fun
      | .concrete true _ => '1'
      | .concrete false _ => '0'
      | _ => '!')
    if bits.any (fun | .concrete _ (some _) => true | _ => false) then
      let tagBit (p : Provenance) (idx : Nat) : Bool :=
        let id? := match p with
          | .concrete id => some id
          | .wildcard _ (some id) _ => some id
          | _ => none
        match id? with
        | some id => (((tags.find? (fun (q : Nat × Nat) => q.1 == id)).map (fun (q : Nat × Nat) => q.2)).getD 0).testBit idx
        | none => false
      body ++ "(" ++ String.ofList (msbFirst.map fun
        | .concrete _ (some (p, idx)) => if tagBit p idx then '1' else '0'
        | _ => '!') ++ ")"
    else body

/-- A pointer reassembled from LSB-first bits that all carry the same provenance. -/
def pointerOfBits? (bits : List MemBit) : Option Pointer :=
  match bits.head? with
  | some (.concrete _ (some (prov, _))) =>
    if bits.all (fun | .concrete _ (some (p, _)) => p == prov | _ => false) then
      some { prov, addrWidth := bits.length, addr := BitVec.ofNat bits.length (bitsValue bits) }
    else none
  | _ => none

/-- `ByteValue::print` for a `b<w>` value (`bits` LSB-first). -/
def llubiByteString (mem : MemoryState) (dl : DataLayout) (w : Nat) (bits : List MemBit)
    (tags : List (Nat × Nat) := []) : String :=
  let n := (w + 7) / 8
  let chunk (k : Nat) : List MemBit := (bits.drop (8 * k)).take (min 8 (w - 8 * k))
  let order : List Nat := if dl.isLittleEndian then List.range n else (List.range n).reverse
  let isFull (k : Nat) : Bool := w % 8 == 0 || k != n - 1
  let ptrW := dl.getPointerSizeInBits 0
  let body : String :=
    if ptrW % 8 == 0 && ptrW > 0 && w % ptrW == 0 then
      let ptrSz := ptrW / 8
      String.join ((List.range (n / ptrSz)).map fun sIdx =>
        let ks := (order.drop (sIdx * ptrSz)).take ptrSz
        let lo := ks.foldl min (n - 1)
        match pointerOfBits? ((bits.drop (8 * lo)).take ptrW) with
        | some p => mem.ptrString p ++ " "
        | none => String.join (ks.map fun k => llubiByteChunk (chunk k) (isFull k) tags ++ " "))
    else String.join (order.map fun k => llubiByteChunk (chunk k) (isFull k) tags ++ " ")
  s!"b{w} " ++ body

mutual
/-- `AnyValue::print`: `i32 -1`, `T`/`F`, `float 1.500000e+00`, `ptr 0x8 [a]`, `{ ... }`. -/
def llubiStringAux (mem : MemoryState) (dl : DataLayout) (tags : List (Nat × Nat)) : RegisterValue → String
  | .void => "none"
  | .bv _ .poison => "poison"
  | .bv w (.value b) => if w == 1 then (if b.toNat == 1 then "T" else "F") else s!"i{w} {b.toInt}"
  | .byte w bits => llubiByteString mem dl w bits tags
  | .float _ .poison => "poison"
  | .float ft (.value f) => s!"{ft.print} {Llubi.llubiFloatString ft f}"
  | .ptr _ .poison => "poison"
  | .ptr _ (.value p) => mem.ptrString p
  | .vector _ es => "{ " ++ ", ".intercalate (llubiStringList mem dl tags es) ++ " }"
  | .array _ es => "{ " ++ ", ".intercalate (llubiStringList mem dl tags es) ++ " }"
  | .struct _ _ es => "{ " ++ ", ".intercalate (llubiStringList mem dl tags es) ++ " }"

def llubiStringList (mem : MemoryState) (dl : DataLayout) (tags : List (Nat × Nat)) :
    List RegisterValue → List String
  | [] => []
  | v :: vs => llubiStringAux mem dl tags v :: llubiStringList mem dl tags vs
end

/-- `llubi` rendering of a runtime value (`tags`: provenance tags for byte values). -/
def llubiString (v : RegisterValue) (mem : MemoryState) (dl : DataLayout)
    (tags : List (Nat × Nat) := []) : String :=
  llubiStringAux mem dl tags v

mutual
def beq : RegisterValue → RegisterValue → Bool
  | .bv w1 v1, .bv w2 v2 =>
      if h : w1 = w2 then (h ▸ v1) == v2 else false
  | .byte w1 b1, .byte w2 b2 =>
      w1 == w2 && b1 == b2
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
  | .byte w1 b1, .byte w2 b2 =>
    if hw : w1 = w2 then
      if hb : b1 = b2 then isTrue (by rw [hw, hb]) else isFalse (by intro h; cases h; exact hb rfl)
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
  | .bv _ _, .byte _ _ | .bv _ _, .float _ _ | .bv _ _, .ptr _ _ | .bv _ _, .vector _ _ | .bv _ _, .array _ _ | .bv _ _, .struct _ _ _ | .bv _ _, .void
  | .byte _ _, .bv _ _ | .byte _ _, .float _ _ | .byte _ _, .ptr _ _ | .byte _ _, .vector _ _ | .byte _ _, .array _ _ | .byte _ _, .struct _ _ _ | .byte _ _, .void
  | .float _ _, .bv _ _ | .float _ _, .byte _ _ | .float _ _, .ptr _ _ | .float _ _, .vector _ _ | .float _ _, .array _ _ | .float _ _, .struct _ _ _ | .float _ _, .void
  | .ptr _ _, .bv _ _ | .ptr _ _, .byte _ _ | .ptr _ _, .float _ _ | .ptr _ _, .vector _ _ | .ptr _ _, .array _ _ | .ptr _ _, .struct _ _ _ | .ptr _ _, .void
  | .vector _ _, .bv _ _ | .vector _ _, .byte _ _ | .vector _ _, .float _ _ | .vector _ _, .ptr _ _ | .vector _ _, .array _ _ | .vector _ _, .struct _ _ _ | .vector _ _, .void
  | .array _ _, .bv _ _ | .array _ _, .byte _ _ | .array _ _, .float _ _ | .array _ _, .ptr _ _ | .array _ _, .vector _ _ | .array _ _, .struct _ _ _ | .array _ _, .void
  | .struct _ _ _, .bv _ _ | .struct _ _ _, .byte _ _ | .struct _ _ _, .float _ _ | .struct _ _ _, .ptr _ _ | .struct _ _ _, .vector _ _ | .struct _ _ _, .array _ _ | .struct _ _ _, .void
  | .void, .bv _ _ | .void, .byte _ _ | .void, .float _ _ | .void, .ptr _ _ | .void, .vector _ _ | .void, .array _ _ | .void, .struct _ _ _ =>
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

/- Produce the canonical `poison` value of LLVM type `ty`. -/
mutual
def poisonOf : LlvmType → RegisterValue
  | .int w => .bv w .poison
  | .byte w => .byte w (List.replicate w .poison)
  | .float ft => .float ft .poison
  | .ptr as => .ptr as .poison
  | .vector n elem => .vector elem (List.replicate n (poisonOf elem))
  | .array n elem => .array elem (List.replicate n (poisonOf elem))
  | .struct packed fields => .struct packed fields (poisonOfList fields)
  | .function .. | .named _ => .void

def poisonOfList : List LlvmType → List RegisterValue
  | [] => []
  | t :: ts => poisonOf t :: poisonOfList ts
end

/- Produce the canonical zero / null value of LLVM type `ty`. -/
mutual
def nullOf (dl : DataLayout) : LlvmType → RegisterValue
  | .int w => .bv w (.value (BitVec.ofNat w 0))
  | .byte w => .byte w (List.replicate w (.concrete false none))
  | .float ft => .float ft (.value (IEEEFloat.zero ft.format false))
  | .ptr as => .ptr as (.value (Pointer.null dl as))
  | .vector n elem => .vector elem (List.replicate n (nullOf dl elem))
  | .array n elem => .array elem (List.replicate n (nullOf dl elem))
  | .struct packed fields => .struct packed fields (nullOfList dl fields)
  | .function .. | .named _ => .void

def nullOfList (dl : DataLayout) : List LlvmType → List RegisterValue
  | [] => []
  | t :: ts => nullOf dl t :: nullOfList dl ts
end

/- Check whether `v` contains any poison scalar element (for `noundef` attribute checks). -/
mutual
def containsPoison : RegisterValue → Bool
  | .bv _ .poison => true
  | .byte _ bits => bits.any (fun b => !b.isConcrete)
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

@[simp]
def isScalarPoison : RegisterValue → Bool
  | .bv _ .poison => true
  | .byte _ bits => !bits.isEmpty && bits.all (fun b => b.isPoison)
  | .float _ .poison => true
  | .ptr _ .poison => true
  | _ => false

/-- Convert an integer `BitVec w` into a concrete `RegisterValue.byte w` (LSB-first, no provenance). -/
def byteOfBitVec {w : Nat} (bv : BitVec w) : RegisterValue :=
  .byte w ((List.range w).map fun i => .concrete (bv.getLsbD i) none)

/-- Extract boolean tri-state (`poison` or `value b`) from an `i1` `RegisterValue`. -/
def asBool? : RegisterValue → Option (PoisonOr Bool)
  | .bv 1 .poison => some .poison
  | .bv 1 (.value b) => some (.value (b != 0))
  | _ => none

/-! ### Value Refinement (under `MemoryInjection`, poison-aware) -/

@[simp]
def IsRefinedByBits (inj : MemoryInjection) : List MemBit → List MemBit → Prop
  | [], [] => True
  | x :: xs, y :: ys => MemBit.IsRefinedBy inj x y ∧ IsRefinedByBits inj xs ys
  | _, _ => False

theorem IsRefinedByBits.refl : ∀ (bs : List MemBit), IsRefinedByBits .id bs bs
  | [] => trivial
  | b :: bs => ⟨MemBit.IsRefinedBy.refl b, IsRefinedByBits.refl bs⟩

theorem IsRefinedByBits.trans {f g : MemoryInjection} :
    ∀ {xs ys zs : List MemBit},
      IsRefinedByBits f xs ys → IsRefinedByBits g ys zs → IsRefinedByBits (f.comp g) xs zs
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, h12, h23 => ⟨MemBit.IsRefinedBy.trans h12.1 h23.1, IsRefinedByBits.trans h12.2 h23.2⟩
  | [], _ :: _, _, h12, _ | _ :: _, [], _, h12, _ => False.elim h12
  | [], [], _ :: _, _, h23 | _ :: _, _ :: _, [], _, h23 => False.elim h23

theorem IsRefinedByBits.mono {f g : MemoryInjection} (hext : f.Extends g) :
    ∀ {xs ys : List MemBit}, IsRefinedByBits f xs ys → IsRefinedByBits g xs ys
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => ⟨MemBit.IsRefinedBy.mono hext h.1, IsRefinedByBits.mono hext h.2⟩
  | [], _ :: _, h | _ :: _, [], h => False.elim h

mutual
@[simp]
def IsRefinedBy (inj : MemoryInjection) : RegisterValue → RegisterValue → Prop
  | .bv wx vx, .bv wy vy =>
    match vx, vy with
    | .poison, _ => wx = wy
    | .value vx, .value vy => ∃ h : wx = wy, h ▸ vx = vy
    | .value _, .poison => False
  | .byte wx bsx, .byte wy bsy => wx = wy ∧ IsRefinedByBits inj bsx bsy
  | .float ftx fx, .float fty fy =>
    match fx, fy with
    | .poison, _ => ftx = fty
    | .value fx, .value fy => ∃ h : ftx = fty, h ▸ fx = fy
    | .value _, .poison => False
  | .ptr asx px, .ptr asy py =>
    match px, py with
    | .poison, _ => asx = asy
    | .value px, .value py => asx = asy ∧ Pointer.IsRefinedBy inj px py
    | .value _, .poison => False
  | .vector tx esx, .vector ty esy => tx = ty ∧ IsRefinedByList inj esx esy
  | .array tx esx, .array ty esy => tx = ty ∧ IsRefinedByList inj esx esy
  | .struct px tsx fsx, .struct py tsy fsy =>
      px = py ∧ tsx = tsy ∧ IsRefinedByList inj fsx fsy
  | .void, .void => True
  | _, _ => False

@[simp]
def IsRefinedByList (inj : MemoryInjection) : List RegisterValue → List RegisterValue → Prop
  | [], [] => True
  | x :: xs, y :: ys => IsRefinedBy inj x y ∧ IsRefinedByList inj xs ys
  | _, _ => False
end

mutual
theorem IsRefinedBy.refl : ∀ (v : RegisterValue), IsRefinedBy .id v v
  | .bv _ .poison => rfl
  | .bv _ (.value _) => ⟨rfl, rfl⟩
  | .byte _ bs => ⟨rfl, IsRefinedByBits.refl bs⟩
  | .float _ .poison => rfl
  | .float _ (.value _) => ⟨rfl, rfl⟩
  | .ptr _ .poison => rfl
  | .ptr _ (.value p) => ⟨rfl, Pointer.IsRefinedBy.refl p⟩
  | .vector _ elems => ⟨rfl, IsRefinedByList.refl elems⟩
  | .array _ elems => ⟨rfl, IsRefinedByList.refl elems⟩
  | .struct _ _ fields => ⟨rfl, rfl, IsRefinedByList.refl fields⟩
  | .void => trivial

theorem IsRefinedByList.refl : ∀ (vs : List RegisterValue), IsRefinedByList .id vs vs
  | [] => trivial
  | v :: vs => ⟨IsRefinedBy.refl v, IsRefinedByList.refl vs⟩
end

mutual
theorem IsRefinedBy.trans {f g : MemoryInjection} :
    ∀ {v1 v2 v3 : RegisterValue},
      IsRefinedBy f v1 v2 → IsRefinedBy g v2 v3 → IsRefinedBy (f.comp g) v1 v3
  | .bv _ .poison, .bv _ .poison, .bv _ _, h12, h23 => Eq.trans h12 h23
  | .bv _ .poison, .bv _ (.value _), .bv _ (.value _), h12, h23 => Eq.trans h12 h23.1
  | .bv _ .poison, .bv _ (.value _), .bv _ .poison, _, h23 => False.elim h23
  | .bv _ (.value _), .bv _ (.value _), .bv _ (.value _), h12, h23 => by
      obtain ⟨hw12, hv12⟩ := h12; obtain ⟨hw23, hv23⟩ := h23
      subst hw12; subst hw23; exact ⟨rfl, Eq.trans hv12 hv23⟩
  | .bv _ (.value _), .bv _ .poison, .bv _ _, h12, _ => False.elim h12
  | .bv _ (.value _), .bv _ (.value _), .bv _ .poison, _, h23 => False.elim h23
  | .byte _ _, .byte _ _, .byte _ _, h12, h23 =>
      ⟨Eq.trans h12.1 h23.1, IsRefinedByBits.trans h12.2 h23.2⟩
  | .float _ .poison, .float _ .poison, .float _ _, h12, h23 => Eq.trans h12 h23
  | .float _ .poison, .float _ (.value _), .float _ (.value _), h12, h23 => Eq.trans h12 h23.1
  | .float _ .poison, .float _ (.value _), .float _ .poison, _, h23 => False.elim h23
  | .float _ (.value _), .float _ (.value _), .float _ (.value _), h12, h23 => by
      obtain ⟨hf12, hv12⟩ := h12; obtain ⟨hf23, hv23⟩ := h23
      subst hf12; subst hf23; exact ⟨rfl, Eq.trans hv12 hv23⟩
  | .float _ (.value _), .float _ .poison, .float _ _, h12, _ => False.elim h12
  | .float _ (.value _), .float _ (.value _), .float _ .poison, _, h23 => False.elim h23
  | .ptr _ .poison, .ptr _ .poison, .ptr _ _, h12, h23 => Eq.trans h12 h23
  | .ptr _ .poison, .ptr _ (.value _), .ptr _ (.value _), h12, h23 => Eq.trans h12 h23.1
  | .ptr _ .poison, .ptr _ (.value _), .ptr _ .poison, _, h23 => False.elim h23
  | .ptr _ (.value _), .ptr _ (.value _), .ptr _ (.value _), h12, h23 =>
      ⟨Eq.trans h12.1 h23.1, Pointer.IsRefinedBy.trans h12.2 h23.2⟩
  | .ptr _ (.value _), .ptr _ .poison, .ptr _ _, h12, _ => False.elim h12
  | .ptr _ (.value _), .ptr _ (.value _), .ptr _ .poison, _, h23 => False.elim h23
  | .vector t1 es1, .vector t2 es2, .vector t3 es3, h12, h23 => by
    simp only [IsRefinedBy] at h12 h23 ⊢
    exact ⟨h12.1.trans h23.1, IsRefinedByList.trans h12.2 h23.2⟩
  | .array t1 es1, .array t2 es2, .array t3 es3, h12, h23 => by
    simp only [IsRefinedBy] at h12 h23 ⊢
    exact ⟨h12.1.trans h23.1, IsRefinedByList.trans h12.2 h23.2⟩
  | .struct p1 ts1 fs1, .struct p2 ts2 fs2, .struct p3 ts3 fs3, h12, h23 => by
    simp only [IsRefinedBy] at h12 h23 ⊢
    exact ⟨h12.1.trans h23.1, h12.2.1.trans h23.2.1, IsRefinedByList.trans h12.2.2 h23.2.2⟩
  | .void, .void, .void, _, _ => trivial
  | .bv _ _, .byte _ _, _, h12, _ | .bv _ _, .float _ _, _, h12, _ | .bv _ _, .ptr _ _, _, h12, _ | .bv _ _, .vector _ _, _, h12, _
  | .bv _ _, .array _ _, _, h12, _ | .bv _ _, .struct _ _ _, _, h12, _ | .bv _ _, .void, _, h12, _
  | .byte _ _, .bv _ _, _, h12, _ | .byte _ _, .float _ _, _, h12, _ | .byte _ _, .ptr _ _, _, h12, _ | .byte _ _, .vector _ _, _, h12, _
  | .byte _ _, .array _ _, _, h12, _ | .byte _ _, .struct _ _ _, _, h12, _ | .byte _ _, .void, _, h12, _
  | .float _ _, .bv _ _, _, h12, _ | .float _ _, .byte _ _, _, h12, _ | .float _ _, .ptr _ _, _, h12, _ | .float _ _, .vector _ _, _, h12, _
  | .float _ _, .array _ _, _, h12, _ | .float _ _, .struct _ _ _, _, h12, _ | .float _ _, .void, _, h12, _
  | .ptr _ _, .bv _ _, _, h12, _ | .ptr _ _, .byte _ _, _, h12, _ | .ptr _ _, .float _ _, _, h12, _ | .ptr _ _, .vector _ _, _, h12, _
  | .ptr _ _, .array _ _, _, h12, _ | .ptr _ _, .struct _ _ _, _, h12, _ | .ptr _ _, .void, _, h12, _
  | .vector _ _, .bv _ _, _, h12, _ | .vector _ _, .byte _ _, _, h12, _ | .vector _ _, .float _ _, _, h12, _ | .vector _ _, .ptr _ _, _, h12, _
  | .vector _ _, .array _ _, _, h12, _ | .vector _ _, .struct _ _ _, _, h12, _ | .vector _ _, .void, _, h12, _
  | .array _ _, .bv _ _, _, h12, _ | .array _ _, .byte _ _, _, h12, _ | .array _ _, .float _ _, _, h12, _ | .array _ _, .ptr _ _, _, h12, _
  | .array _ _, .vector _ _, _, h12, _ | .array _ _, .struct _ _ _, _, h12, _ | .array _ _, .void, _, h12, _
  | .struct _ _ _, .bv _ _, _, h12, _ | .struct _ _ _, .byte _ _, _, h12, _ | .struct _ _ _, .float _ _, _, h12, _ | .struct _ _ _, .ptr _ _, _, h12, _
  | .struct _ _ _, .vector _ _, _, h12, _ | .struct _ _ _, .array _ _, _, h12, _ | .struct _ _ _, .void, _, h12, _
  | .void, .bv _ _, _, h12, _ | .void, .byte _ _, _, h12, _ | .void, .float _ _, _, h12, _ | .void, .ptr _ _, _, h12, _
  | .void, .vector _ _, _, h12, _ | .void, .array _ _, _, h12, _ | .void, .struct _ _ _, _, h12, _ =>
    False.elim (by cases h12)
  | .bv _ _, .bv _ _, .byte _ _, _, h23 | .bv _ _, .bv _ _, .float _ _, _, h23 | .bv _ _, .bv _ _, .ptr _ _, _, h23 | .bv _ _, .bv _ _, .vector _ _, _, h23
  | .bv _ _, .bv _ _, .array _ _, _, h23 | .bv _ _, .bv _ _, .struct _ _ _, _, h23 | .bv _ _, .bv _ _, .void, _, h23
  | .byte _ _, .byte _ _, .bv _ _, _, h23 | .byte _ _, .byte _ _, .float _ _, _, h23 | .byte _ _, .byte _ _, .ptr _ _, _, h23 | .byte _ _, .byte _ _, .vector _ _, _, h23
  | .byte _ _, .byte _ _, .array _ _, _, h23 | .byte _ _, .byte _ _, .struct _ _ _, _, h23 | .byte _ _, .byte _ _, .void, _, h23
  | .float _ _, .float _ _, .bv _ _, _, h23 | .float _ _, .float _ _, .byte _ _, _, h23 | .float _ _, .float _ _, .ptr _ _, _, h23 | .float _ _, .float _ _, .vector _ _, _, h23
  | .float _ _, .float _ _, .array _ _, _, h23 | .float _ _, .float _ _, .struct _ _ _, _, h23 | .float _ _, .float _ _, .void, _, h23
  | .ptr _ _, .ptr _ _, .bv _ _, _, h23 | .ptr _ _, .ptr _ _, .byte _ _, _, h23 | .ptr _ _, .ptr _ _, .float _ _, _, h23 | .ptr _ _, .ptr _ _, .vector _ _, _, h23
  | .ptr _ _, .ptr _ _, .array _ _, _, h23 | .ptr _ _, .ptr _ _, .struct _ _ _, _, h23 | .ptr _ _, .ptr _ _, .void, _, h23
  | .vector _ _, .vector _ _, .bv _ _, _, h23 | .vector _ _, .vector _ _, .byte _ _, _, h23 | .vector _ _, .vector _ _, .float _ _, _, h23 | .vector _ _, .vector _ _, .ptr _ _, _, h23
  | .vector _ _, .vector _ _, .array _ _, _, h23 | .vector _ _, .vector _ _, .struct _ _ _, _, h23 | .vector _ _, .vector _ _, .void, _, h23
  | .array _ _, .array _ _, .bv _ _, _, h23 | .array _ _, .array _ _, .byte _ _, _, h23 | .array _ _, .array _ _, .float _ _, _, h23 | .array _ _, .array _ _, .ptr _ _, _, h23
  | .array _ _, .array _ _, .vector _ _, _, h23 | .array _ _, .array _ _, .struct _ _ _, _, h23 | .array _ _, .array _ _, .void, _, h23
  | .struct _ _ _, .struct _ _ _, .bv _ _, _, h23 | .struct _ _ _, .struct _ _ _, .byte _ _, _, h23 | .struct _ _ _, .struct _ _ _, .float _ _, _, h23 | .struct _ _ _, .struct _ _ _, .ptr _ _, _, h23
  | .struct _ _ _, .struct _ _ _, .vector _ _, _, h23 | .struct _ _ _, .struct _ _ _, .array _ _, _, h23 | .struct _ _ _, .struct _ _ _, .void, _, h23
  | .void, .void, .bv _ _, _, h23 | .void, .void, .byte _ _, _, h23 | .void, .void, .float _ _, _, h23 | .void, .void, .ptr _ _, _, h23
  | .void, .void, .vector _ _, _, h23 | .void, .void, .array _ _, _, h23 | .void, .void, .struct _ _ _, _, h23 =>
    False.elim (by cases h23)

theorem IsRefinedByList.trans {f g : MemoryInjection} :
    ∀ {xs ys zs : List RegisterValue},
      IsRefinedByList f xs ys → IsRefinedByList g ys zs → IsRefinedByList (f.comp g) xs zs
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, h12, h23 => ⟨IsRefinedBy.trans h12.1 h23.1, IsRefinedByList.trans h12.2 h23.2⟩
  | [], _ :: _, _, h12, _ | _ :: _, [], _, h12, _ => False.elim h12
  | [], [], _ :: _, _, h23 | _ :: _, _ :: _, [], _, h23 => False.elim h23
end

mutual
theorem IsRefinedBy.mono {f g : MemoryInjection} (hext : f.Extends g) :
    ∀ {v1 v2 : RegisterValue}, IsRefinedBy f v1 v2 → IsRefinedBy g v1 v2
  | .bv _ .poison, .bv _ _, h => h
  | .bv _ (.value _), .bv _ (.value _), h => h
  | .bv _ (.value _), .bv _ .poison, h => h
  | .byte _ _, .byte _ _, h => ⟨h.1, IsRefinedByBits.mono hext h.2⟩
  | .float _ .poison, .float _ _, h => h
  | .float _ (.value _), .float _ (.value _), h => h
  | .float _ (.value _), .float _ .poison, h => h
  | .ptr _ .poison, .ptr _ _, h => h
  | .ptr _ (.value _), .ptr _ (.value _), h => ⟨h.1, Pointer.IsRefinedBy.mono hext h.2⟩
  | .ptr _ (.value _), .ptr _ .poison, h => h
  | .vector _ _, .vector _ _, h => ⟨h.1, IsRefinedByList.mono hext h.2⟩
  | .array _ _, .array _ _, h => ⟨h.1, IsRefinedByList.mono hext h.2⟩
  | .struct _ _ _, .struct _ _ _, h => ⟨h.1, h.2.1, IsRefinedByList.mono hext h.2.2⟩
  | .void, .void, _ => trivial
  | .bv _ _, .byte _ _, h | .bv _ _, .float _ _, h | .bv _ _, .ptr _ _, h | .bv _ _, .vector _ _, h
  | .bv _ _, .array _ _, h | .bv _ _, .struct _ _ _, h | .bv _ _, .void, h
  | .byte _ _, .bv _ _, h | .byte _ _, .float _ _, h | .byte _ _, .ptr _ _, h | .byte _ _, .vector _ _, h
  | .byte _ _, .array _ _, h | .byte _ _, .struct _ _ _, h | .byte _ _, .void, h
  | .float _ _, .bv _ _, h | .float _ _, .byte _ _, h | .float _ _, .ptr _ _, h | .float _ _, .vector _ _, h
  | .float _ _, .array _ _, h | .float _ _, .struct _ _ _, h | .float _ _, .void, h
  | .ptr _ _, .bv _ _, h | .ptr _ _, .byte _ _, h | .ptr _ _, .float _ _, h | .ptr _ _, .vector _ _, h
  | .ptr _ _, .array _ _, h | .ptr _ _, .struct _ _ _, h | .ptr _ _, .void, h
  | .vector _ _, .bv _ _, h | .vector _ _, .byte _ _, h | .vector _ _, .float _ _, h | .vector _ _, .ptr _ _, h
  | .vector _ _, .array _ _, h | .vector _ _, .struct _ _ _, h | .vector _ _, .void, h
  | .array _ _, .bv _ _, h | .array _ _, .byte _ _, h | .array _ _, .float _ _, h | .array _ _, .ptr _ _, h
  | .array _ _, .vector _ _, h | .array _ _, .struct _ _ _, h | .array _ _, .void, h
  | .struct _ _ _, .bv _ _, h | .struct _ _ _, .byte _ _, h | .struct _ _ _, .float _ _, h | .struct _ _ _, .ptr _ _, h
  | .struct _ _ _, .vector _ _, h | .struct _ _ _, .array _ _, h | .struct _ _ _, .void, h
  | .void, .bv _ _, h | .void, .byte _ _, h | .void, .float _ _, h | .void, .ptr _ _, h
  | .void, .vector _ _, h | .void, .array _ _, h | .void, .struct _ _ _, h => False.elim h

theorem IsRefinedByList.mono {f g : MemoryInjection} (hext : f.Extends g) :
    ∀ {xs ys : List RegisterValue}, IsRefinedByList f xs ys → IsRefinedByList g xs ys
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => ⟨IsRefinedBy.mono hext h.1, IsRefinedByList.mono hext h.2⟩
  | [], _ :: _, h | _ :: _, [], h => False.elim h
end

end RegisterValue

def castRegValue? (w : Nat) : RegisterValue → Option (IntW w)
  | .bv w' v =>
    if h : w' = w then some (h ▸ v) else none
  | _ => none

/-! ### Bit-level Byte Serialization & Deserialization (`valueToBytes` / `bytesToValue`) -/

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
  | .float _ (.value flt) =>
    writeBitLoop dl offsetInBits
      (fun i => if i < numBits then .concrete (flt.bits.getLsbD i) none else .concrete false none)
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

/-! ### Relational & Executable `freeze` and `undef` Value Generation -/

/-- Per-bit relational specification of `freeze` for byte values (`bN`). -/
inductive FreezeBitRel (cfg : SemanticsConfig) : MemBit → MemBit → Prop where
  | concrete (b : Bool) (p : Option (Provenance × Nat)) :
      FreezeBitRel cfg (.concrete b p) (.concrete b p)
  | poison (b : Bool) :
      (cfg.freezeMode = .zero → b = false) →
      FreezeBitRel cfg .poison (.concrete b none)
  | undef (b : Bool) :
      (cfg.freezeMode = .zero → b = false) →
      FreezeBitRel cfg .undef (.concrete b none)

inductive FreezeBitListRel (cfg : SemanticsConfig) : List MemBit → List MemBit → Prop where
  | nil : FreezeBitListRel cfg [] []
  | cons {b b' : MemBit} {bs bs' : List MemBit} :
      FreezeBitRel cfg b b' → FreezeBitListRel cfg bs bs' →
      FreezeBitListRel cfg (b :: bs) (b' :: bs')

mutual
/-- Relational specification of `freeze`: preserves every non-poison scalar and replaces
    each poison scalar with an arbitrary concrete bitpattern (or `0` when `freezeMode = .zero`). -/
inductive FreezeRel (dl : DataLayout) (cfg : SemanticsConfig) :
    RegisterValue → RegisterValue → Prop where
  | bv_val (w : Nat) (v : BitVec w) :
      FreezeRel dl cfg (.bv w (.value v)) (.bv w (.value v))
  | bv_poison (w : Nat) (bits : BitVec w) :
      (cfg.freezeMode = .zero → bits = BitVec.ofNat w 0) →
      FreezeRel dl cfg (.bv w .poison) (.bv w (.value bits))
  | byte (w : Nat) (bs bs' : List MemBit) :
      FreezeBitListRel cfg bs bs' →
      FreezeRel dl cfg (.byte w bs) (.byte w bs')
  | float_val (ft : FloatType) (f : IEEEFloat ft.format) :
      FreezeRel dl cfg (.float ft (.value f)) (.float ft (.value f))
  | float_poison (ft : FloatType) (bits : BitVec ft.bitWidth) :
      (cfg.freezeMode = .zero → bits = BitVec.ofNat ft.bitWidth 0) →
      FreezeRel dl cfg (.float ft .poison) (.float ft (.value (IEEEFloat.ofBits bits)))
  | ptr_val (as : Nat) (p : Pointer) :
      FreezeRel dl cfg (.ptr as (.value p)) (.ptr as (.value p))
  | ptr_poison (as : Nat) (bits : BitVec (dl.getPointerSizeInBits as)) :
      (cfg.freezeMode = .zero → bits = BitVec.ofNat (dl.getPointerSizeInBits as) 0) →
      FreezeRel dl cfg (.ptr as .poison)
        (.ptr as (.value { prov := .nullary, addrWidth := dl.getPointerSizeInBits as, addr := bits }))
  | vector (elemTy : LlvmType) (es es' : List RegisterValue) :
      FreezeRelList dl cfg es es' →
      FreezeRel dl cfg (.vector elemTy es) (.vector elemTy es')
  | array (elemTy : LlvmType) (es es' : List RegisterValue) :
      FreezeRelList dl cfg es es' →
      FreezeRel dl cfg (.array elemTy es) (.array elemTy es')
  | struct (packed : Bool) (fTys : List LlvmType) (fs fs' : List RegisterValue) :
      FreezeRelList dl cfg fs fs' →
      FreezeRel dl cfg (.struct packed fTys fs) (.struct packed fTys fs')
  | void : FreezeRel dl cfg .void .void

inductive FreezeRelList (dl : DataLayout) (cfg : SemanticsConfig) :
    List RegisterValue → List RegisterValue → Prop where
  | nil : FreezeRelList dl cfg [] []
  | cons {v v' : RegisterValue} {vs vs' : List RegisterValue} :
      FreezeRel dl cfg v v' → FreezeRelList dl cfg vs vs' →
      FreezeRelList dl cfg (v :: vs) (v' :: vs')
end

private def drawFreezeBits (cfg : SemanticsConfig) (w : Nat) (o : OracleState) : BitVec w × OracleState :=
  match cfg.freezeMode with
  | .zero => (BitVec.ofNat w 0, o)
  | .nondet => o.nextBitVec w

private def drawFreezeBool (cfg : SemanticsConfig) (o : OracleState) : Bool × OracleState :=
  match cfg.freezeMode with
  | .zero => (false, o)
  | .nondet => o.nextBool

private theorem drawFreezeBool_zero_spec (cfg : SemanticsConfig) (o : OracleState)
    {b : Bool} {o' : OracleState} (h : drawFreezeBool cfg o = (b, o')) :
    cfg.freezeMode = .zero → b = false := by
  intro hz; unfold drawFreezeBool at h; rw [hz] at h; cases h; rfl

private def freezeMemBits (cfg : SemanticsConfig) : List MemBit → OracleState → List MemBit × OracleState
  | [], o => ([], o)
  | .concrete b p :: rest, o =>
    match freezeMemBits cfg rest o with
    | (rest', o') => (.concrete b p :: rest', o')
  | .poison :: rest, o =>
    match drawFreezeBool cfg o with
    | (b, o1) =>
      match freezeMemBits cfg rest o1 with
      | (rest', o2) => (.concrete b none :: rest', o2)
  | .undef :: rest, o =>
    match drawFreezeBool cfg o with
    | (b, o1) =>
      match freezeMemBits cfg rest o1 with
      | (rest', o2) => (.concrete b none :: rest', o2)

private theorem freezeMemBits_sound (cfg : SemanticsConfig) :
    ∀ (bs : List MemBit) (o : OracleState), FreezeBitListRel cfg bs (freezeMemBits cfg bs o).1
  | [], _ => FreezeBitListRel.nil
  | .concrete b p :: rest, o => by
    unfold freezeMemBits
    exact FreezeBitListRel.cons (FreezeBitRel.concrete b p) (freezeMemBits_sound cfg rest o)
  | .poison :: rest, o => by
    unfold freezeMemBits
    generalize hb : drawFreezeBool cfg o = p1
    cases p1 with
    | mk b o1 =>
      exact FreezeBitListRel.cons (FreezeBitRel.poison b (drawFreezeBool_zero_spec cfg o hb))
        (freezeMemBits_sound cfg rest o1)
  | .undef :: rest, o => by
    unfold freezeMemBits
    generalize hb : drawFreezeBool cfg o = p1
    cases p1 with
    | mk b o1 =>
      exact FreezeBitListRel.cons (FreezeBitRel.undef b (drawFreezeBool_zero_spec cfg o hb))
        (freezeMemBits_sound cfg rest o1)

/-- Map bits with their (logical) index, starting at index `k`. -/
def mapBitsFrom (f : Nat → MemBit → MemBit) : Nat → List MemBit → List MemBit
  | _, [] => []
  | k, b :: bs => f k b :: mapBitsFrom f (k + 1) bs

private theorem mapBitsFrom_rel (cfg : SemanticsConfig) (f : Nat → MemBit → MemBit)
    (hf : ∀ i b, FreezeBitRel cfg b (f i b)) :
    ∀ (k : Nat) (bs : List MemBit), FreezeBitListRel cfg bs (mapBitsFrom f k bs)
  | _, [] => FreezeBitListRel.nil
  | k, b :: bs => FreezeBitListRel.cons (hf k b) (mapBitsFrom_rel cfg f hf (k + 1) bs)

/-- Draw one value per byte (in the data layout's storage order) for the bytes of `bits` that
contain non-concrete bits (`llubi`'s `freeze` of byte values: `Rng() & 255` per such byte). -/
def freezeByteDraws (dl : DataLayout) (cfg : SemanticsConfig) (bits : List MemBit) (o : OracleState) :
    List (Nat × Nat) × OracleState :=
  let n := (bits.length + 7) / 8
  let order := if dl.isLittleEndian then List.range n else (List.range n).reverse
  order.foldl (fun (acc, o0) k =>
    let chunk := (bits.drop (8 * k)).take 8
    if chunk.all MemBit.isConcrete || cfg.freezeMode == .zero then (acc, o0)
    else
      match o0.nextNat with
      | (r, o1) => ((k, r) :: acc, o1)) ([], o)

/-- Resolve a non-concrete bit `i` of a frozen byte value from the per-byte draws. -/
def frozenBit (cfg : SemanticsConfig) (draws : List (Nat × Nat)) (i : Nat) : MemBit → MemBit
  | .concrete b p => .concrete b p
  | _ =>
    if cfg.freezeMode == .zero then .concrete false none
    else
      let r := ((draws.find? (·.1 == i / 8)).map (·.2)).getD 0
      .concrete (r.testBit (i % 8)) none

private theorem frozenBit_rel (cfg : SemanticsConfig) (draws : List (Nat × Nat)) :
    ∀ i b, FreezeBitRel cfg b (frozenBit cfg draws i b) := by
  intro i b
  cases b with
  | concrete b p => exact FreezeBitRel.concrete b p
  | poison =>
    unfold frozenBit
    by_cases hz : cfg.freezeMode = .zero
    · simp only [hz, beq_self_eq_true, ↓reduceIte]
      exact FreezeBitRel.poison false (fun _ => rfl)
    · have : (cfg.freezeMode == .zero) = false := by
        cases h : cfg.freezeMode <;> simp_all
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      exact FreezeBitRel.poison _ (fun h => absurd h hz)
  | undef =>
    unfold frozenBit
    by_cases hz : cfg.freezeMode = .zero
    · simp only [hz, beq_self_eq_true, ↓reduceIte]
      exact FreezeBitRel.undef false (fun _ => rfl)
    · have : (cfg.freezeMode == .zero) = false := by
        cases h : cfg.freezeMode <;> simp_all
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      exact FreezeBitRel.undef _ (fun h => absurd h hz)

/-- Executable `freeze` of a byte value's bits with `llubi`'s per-byte draws. -/
def freezeByteBits (dl : DataLayout) (cfg : SemanticsConfig) (bits : List MemBit) (o : OracleState) :
    List MemBit × OracleState :=
  match freezeByteDraws dl cfg bits o with
  | (draws, o') => (mapBitsFrom (frozenBit cfg draws) 0 bits, o')

private theorem freezeByteBits_sound (dl : DataLayout) (cfg : SemanticsConfig)
    (bits : List MemBit) (o : OracleState) :
    FreezeBitListRel cfg bits (freezeByteBits dl cfg bits o).1 := by
  unfold freezeByteBits
  exact mapBitsFrom_rel cfg _ (frozenBit_rel cfg _) 0 bits

private theorem drawFreezeBits_zero_spec (cfg : SemanticsConfig) (w : Nat) (o : OracleState)
    {bits : BitVec w} {o' : OracleState} (h : drawFreezeBits cfg w o = (bits, o')) :
    cfg.freezeMode = .zero → bits = BitVec.ofNat w 0 := by
  intro hz
  unfold drawFreezeBits at h
  rw [hz] at h
  cases h
  rfl

mutual
def freezeValue (dl : DataLayout) (cfg : SemanticsConfig) :
    RegisterValue → OracleState → RegisterValue × OracleState
  | .bv w .poison, oracle =>
    match drawFreezeBits cfg w oracle with
    | (bits, o') => (.bv w (.value bits), o')
  | .bv w (.value v), oracle => (.bv w (.value v), oracle)
  | .byte w bs, oracle =>
    match freezeByteBits dl cfg bs oracle with
    | (bs', o') => (.byte w bs', o')
  | .float ft .poison, oracle =>
    match drawFreezeBits cfg ft.bitWidth oracle with
    | (bits, o') => (.float ft (.value (IEEEFloat.ofBits bits)), o')
  | .float ft (.value f), oracle => (.float ft (.value f), oracle)
  | .ptr as .poison, oracle =>
    match drawFreezeBits cfg (dl.getPointerSizeInBits as) oracle with
    | (bits, o') =>
      (.ptr as (.value { prov := .nullary, addrWidth := dl.getPointerSizeInBits as, addr := bits }), o')
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

mutual
theorem freezeValue_sound (dl : DataLayout) (cfg : SemanticsConfig) :
    ∀ (v : RegisterValue) (o : OracleState),
      FreezeRel dl cfg v (freezeValue dl cfg v o).1
  | .bv w .poison, o => by
    unfold freezeValue
    generalize h : drawFreezeBits cfg w o = p
    cases p with
    | mk bits o' => exact FreezeRel.bv_poison w bits (drawFreezeBits_zero_spec cfg w o h)
  | .bv w (.value b), _ => FreezeRel.bv_val w b
  | .byte w bs, o => by
    unfold freezeValue
    have ih := freezeByteBits_sound dl cfg bs o
    cases h : freezeByteBits dl cfg bs o with
    | mk bs' o' =>
      rw [h] at ih
      exact FreezeRel.byte w bs bs' ih
  | .float ft .poison, o => by
    unfold freezeValue
    generalize h : drawFreezeBits cfg ft.bitWidth o = p
    cases p with
    | mk bits o' => exact FreezeRel.float_poison ft bits (drawFreezeBits_zero_spec cfg ft.bitWidth o h)
  | .float ft (.value f), _ => FreezeRel.float_val ft f
  | .ptr as .poison, o => by
    unfold freezeValue
    generalize h : drawFreezeBits cfg (dl.getPointerSizeInBits as) o = p
    cases p with
    | mk bits o' =>
      exact FreezeRel.ptr_poison as bits (drawFreezeBits_zero_spec cfg (dl.getPointerSizeInBits as) o h)
  | .ptr as (.value p), _ => FreezeRel.ptr_val as p
  | .vector elemTy es, o => by
    unfold freezeValue
    have ih := freezeValueList_sound dl cfg es o
    cases h : freezeValueList dl cfg es o with
    | mk es' o' =>
      rw [h] at ih
      exact FreezeRel.vector elemTy es es' ih
  | .array elemTy es, o => by
    unfold freezeValue
    have ih := freezeValueList_sound dl cfg es o
    cases h : freezeValueList dl cfg es o with
    | mk es' o' =>
      rw [h] at ih
      exact FreezeRel.array elemTy es es' ih
  | .struct packed fTys fs, o => by
    unfold freezeValue
    have ih := freezeValueList_sound dl cfg fs o
    cases h : freezeValueList dl cfg fs o with
    | mk fs' o' =>
      rw [h] at ih
      exact FreezeRel.struct packed fTys fs fs' ih
  | .void, _ => FreezeRel.void

theorem freezeValueList_sound (dl : DataLayout) (cfg : SemanticsConfig) :
    ∀ (vs : List RegisterValue) (o : OracleState),
      FreezeRelList dl cfg vs (freezeValueList dl cfg vs o).1
  | [], _ => FreezeRelList.nil
  | v :: vs, o => by
    unfold freezeValueList
    have ih1 := freezeValue_sound dl cfg v o
    cases h1 : freezeValue dl cfg v o with
    | mk v' o1 =>
      rw [h1] at ih1
      dsimp only
      have ih2 := freezeValueList_sound dl cfg vs o1
      cases h2 : freezeValueList dl cfg vs o1 with
      | mk vs' o2 =>
        rw [h2] at ih2
        exact FreezeRelList.cons ih1 ih2
end

mutual
/-- Relational specification of `undef` value generation (respects `cfg.undefMode`). -/
inductive UndefValRel (dl : DataLayout) (cfg : SemanticsConfig) :
    LlvmType → RegisterValue → Prop where
  | int (w : Nat) (bits : BitVec w) :
      (cfg.undefMode = .zero → bits = BitVec.ofNat w 0) →
      UndefValRel dl cfg (.int w) (.bv w (.value bits))
  | byte (w : Nat) (bits : BitVec w) :
      (cfg.undefMode = .zero → bits = BitVec.ofNat w 0) →
      UndefValRel dl cfg (.byte w) (RegisterValue.byteOfBitVec bits)
  | float (ft : FloatType) (bits : BitVec ft.bitWidth) :
      (cfg.undefMode = .zero → bits = BitVec.ofNat ft.bitWidth 0) →
      UndefValRel dl cfg (.float ft) (.float ft (.value (IEEEFloat.ofBits bits)))
  | ptr (as : Nat) (bits : BitVec (dl.getPointerSizeInBits as)) :
      (cfg.undefMode = .zero → bits = BitVec.ofNat (dl.getPointerSizeInBits as) (dl.getNullPtrValue as)) →
      UndefValRel dl cfg (.ptr as)
        (.ptr as (.value { prov := .nullary, addrWidth := dl.getPointerSizeInBits as, addr := bits }))
  | vector (n : Nat) (elemTy : LlvmType) (es : List RegisterValue) :
      es.length = n →
      UndefValRelUniform dl cfg elemTy es →
      UndefValRel dl cfg (.vector n elemTy) (.vector elemTy es)
  | array (n : Nat) (elemTy : LlvmType) (es : List RegisterValue) :
      es.length = n →
      UndefValRelUniform dl cfg elemTy es →
      UndefValRel dl cfg (.array n elemTy) (.array elemTy es)
  | struct (packed : Bool) (fTys : List LlvmType) (fs : List RegisterValue) :
      UndefValRelList dl cfg fTys fs →
      UndefValRel dl cfg (.struct packed fTys) (.struct packed fTys fs)

inductive UndefValRelUniform (dl : DataLayout) (cfg : SemanticsConfig) :
    LlvmType → List RegisterValue → Prop where
  | nil (elemTy : LlvmType) : UndefValRelUniform dl cfg elemTy []
  | cons {elemTy : LlvmType} {v : RegisterValue} {vs : List RegisterValue} :
      UndefValRel dl cfg elemTy v → UndefValRelUniform dl cfg elemTy vs →
      UndefValRelUniform dl cfg elemTy (v :: vs)

inductive UndefValRelList (dl : DataLayout) (cfg : SemanticsConfig) :
    List LlvmType → List RegisterValue → Prop where
  | nil : UndefValRelList dl cfg [] []
  | cons {t : LlvmType} {v : RegisterValue} {ts : List LlvmType} {vs : List RegisterValue} :
      UndefValRel dl cfg t v → UndefValRelList dl cfg ts vs →
      UndefValRelList dl cfg (t :: ts) (v :: vs)
end

mutual
def genUndefZeroExec (dl : DataLayout) : LlvmType → Except ExecError RegisterValue
  | .int w => .ok (.bv w (.value (BitVec.ofNat w 0)))
  | .byte w => .ok (RegisterValue.byteOfBitVec (BitVec.ofNat w 0))
  | .float ft => .ok (.float ft (.value (IEEEFloat.ofBits (BitVec.ofNat ft.bitWidth 0))))
  | .ptr as =>
    let pw := dl.getPointerSizeInBits as
    .ok (.ptr as (.value { prov := .nullary, addrWidth := pw, addr := BitVec.ofNat pw (dl.getNullPtrValue as) }))
  | .vector n elem =>
    match genUndefZeroExec dl elem with
    | .ok v => .ok (.vector elem (List.replicate n v))
    | .error e => .error e
  | .array n elem =>
    match genUndefZeroExec dl elem with
    | .ok v => .ok (.array elem (List.replicate n v))
    | .error e => .error e
  | .struct packed fields =>
    match genUndefZeroListExec dl fields with
    | .ok fs => .ok (.struct packed fields fs)
    | .error e => .error e
  | .function .. | .named _ => .error (.staticError "Cannot create undef of function or unresolved named type")

def genUndefZeroListExec (dl : DataLayout) : List LlvmType → Except ExecError (List RegisterValue)
  | [] => .ok []
  | t :: ts =>
    match genUndefZeroExec dl t with
    | .error e => .error e
    | .ok v =>
      match genUndefZeroListExec dl ts with
      | .error e => .error e
      | .ok vs => .ok (v :: vs)
end

def genUndefRepeatExec (f : OracleState → Except ExecError (RegisterValue × OracleState)) :
    Nat → OracleState → Except ExecError (List RegisterValue × OracleState)
  | 0, o => .ok ([], o)
  | k + 1, o =>
    match f o with
    | .error e => .error e
    | .ok (v, o1) =>
      match genUndefRepeatExec f k o1 with
      | .error e => .error e
      | .ok (vs, o2) => .ok (v :: vs, o2)

/-- `w` random bits drawn one byte at a time in storage order (`llubi` freezes a poison byte value
with one `Rng() & 255` per byte). -/
def nextByteBits (dl : DataLayout) (w : Nat) (o : OracleState) : BitVec w × OracleState :=
  let n := (w + 7) / 8
  let order := if dl.isLittleEndian then List.range n else (List.range n).reverse
  match order.foldl (fun (acc, o0) k =>
      match o0.nextNat with
      | (r, o1) => (acc ||| ((r % 256) <<< (8 * k)), o1)) (0, o) with
  | (v, o') => (BitVec.ofNat w v, o')

mutual
def genUndefNondetExec (dl : DataLayout) : LlvmType → OracleState → Except ExecError (RegisterValue × OracleState)
  | .int w, o =>
    match o.nextBitVec w with
    | (bv, o') => .ok (.bv w (.value bv), o')
  | .byte w, o =>
    match nextByteBits dl w o with
    | (bv, o') => .ok (RegisterValue.byteOfBitVec bv, o')
  | .float ft, o =>
    match o.nextBitVec ft.bitWidth with
    | (bv, o') => .ok (.float ft (.value (IEEEFloat.ofBits bv)), o')
  | .ptr as, o =>
    let pw := dl.getPointerSizeInBits as
    match o.nextBitVec pw with
    | (addr, o') => .ok (.ptr as (.value { prov := .nullary, addrWidth := pw, addr := addr }), o')
  | .vector n elem, o =>
    match genUndefRepeatExec (genUndefNondetExec dl elem) n o with
    | .ok (es, o') => .ok (.vector elem es, o')
    | .error e => .error e
  | .array n elem, o =>
    match genUndefRepeatExec (genUndefNondetExec dl elem) n o with
    | .ok (es, o') => .ok (.array elem es, o')
    | .error e => .error e
  | .struct packed fields, o =>
    match genUndefListExec dl fields o with
    | .ok (fs, o') => .ok (.struct packed fields fs, o')
    | .error e => .error e
  | .function .., _ | .named _, _ => .error (.staticError "Cannot create undef of function or unresolved named type")

def genUndefListExec (dl : DataLayout) : List LlvmType → OracleState → Except ExecError (List RegisterValue × OracleState)
  | [], o => .ok ([], o)
  | t :: ts, o =>
    match genUndefNondetExec dl t o with
    | .error e => .error e
    | .ok (v, o1) =>
      match genUndefListExec dl ts o1 with
      | .error e => .error e
      | .ok (vs, o2) => .ok (v :: vs, o2)
end

/-- Executable `undef` generator respecting `cfg.undefMode`. -/
def genUndefExec (dl : DataLayout) (cfg : SemanticsConfig) (ty : LlvmType) (o : OracleState) :
    Except ExecError (RegisterValue × OracleState) :=
  match cfg.undefMode with
  | .disabled => .error (.staticError "`undef` is disabled under current SemanticsConfig (use `poison` or enable `undefMode`)")
  | .zero =>
    match genUndefZeroExec dl ty with
    | .ok v => .ok (v, o)
    | .error e => .error e
  | .nondet => genUndefNondetExec dl ty o

private theorem undefValRelUniform_replicate {dl cfg elem v}
    (hv : UndefValRel dl cfg elem v) :
    ∀ n, UndefValRelUniform dl cfg elem (List.replicate n v)
  | 0 => UndefValRelUniform.nil elem
  | n + 1 => UndefValRelUniform.cons hv (undefValRelUniform_replicate hv n)

mutual
private theorem genUndefZeroExec_sound (dl : DataLayout) (cfg : SemanticsConfig) :
    ∀ (ty : LlvmType) {v : RegisterValue},
      genUndefZeroExec dl ty = .ok v → UndefValRel dl cfg ty v
  | .int w, _, h => by
    unfold genUndefZeroExec at h; cases h
    exact UndefValRel.int w (BitVec.ofNat w 0) (fun _ => rfl)
  | .byte w, _, h => by
    unfold genUndefZeroExec at h; cases h
    exact UndefValRel.byte w (BitVec.ofNat w 0) (fun _ => rfl)
  | .float ft, _, h => by
    unfold genUndefZeroExec at h; cases h
    exact UndefValRel.float ft (BitVec.ofNat ft.bitWidth 0) (fun _ => rfl)
  | .ptr as, _, h => by
    unfold genUndefZeroExec at h; cases h
    exact UndefValRel.ptr as (BitVec.ofNat (dl.getPointerSizeInBits as) (dl.getNullPtrValue as)) (fun _ => rfl)
  | .vector n elem, _, h => by
    unfold genUndefZeroExec at h
    cases he : genUndefZeroExec dl elem with
    | error e => rw [he] at h; cases h
    | ok ev =>
      rw [he] at h; cases h
      exact UndefValRel.vector n elem _ List.length_replicate
        (undefValRelUniform_replicate (genUndefZeroExec_sound dl cfg elem he) n)
  | .array n elem, _, h => by
    unfold genUndefZeroExec at h
    cases he : genUndefZeroExec dl elem with
    | error e => rw [he] at h; cases h
    | ok ev =>
      rw [he] at h; cases h
      exact UndefValRel.array n elem _ List.length_replicate
        (undefValRelUniform_replicate (genUndefZeroExec_sound dl cfg elem he) n)
  | .struct packed fields, _, h => by
    unfold genUndefZeroExec at h
    cases hf : genUndefZeroListExec dl fields with
    | error e => rw [hf] at h; cases h
    | ok fs =>
      rw [hf] at h; cases h
      exact UndefValRel.struct packed fields fs (genUndefZeroListExec_sound dl cfg fields hf)
  | .function .., _, h | .named _, _, h => by unfold genUndefZeroExec at h; cases h

private theorem genUndefZeroListExec_sound (dl : DataLayout) (cfg : SemanticsConfig) :
    ∀ (ts : List LlvmType) {vs : List RegisterValue},
      genUndefZeroListExec dl ts = .ok vs → UndefValRelList dl cfg ts vs
  | [], _, h => by unfold genUndefZeroListExec at h; cases h; exact UndefValRelList.nil
  | t :: ts, _, h => by
    unfold genUndefZeroListExec at h
    cases h1 : genUndefZeroExec dl t with
    | error e => rw [h1] at h; cases h
    | ok v =>
      rw [h1] at h
      cases h2 : genUndefZeroListExec dl ts with
      | error e => rw [h2] at h; cases h
      | ok vs =>
        rw [h2] at h; cases h
        exact UndefValRelList.cons (genUndefZeroExec_sound dl cfg t h1) (genUndefZeroListExec_sound dl cfg ts h2)
end

private theorem genUndefRepeatExec_sound {dl cfg elem}
    {f : OracleState → Except ExecError (RegisterValue × OracleState)}
    (hf : ∀ o v o', f o = .ok (v, o') → UndefValRel dl cfg elem v) :
    ∀ n o es o', genUndefRepeatExec f n o = .ok (es, o') →
      es.length = n ∧ UndefValRelUniform dl cfg elem es
  | 0, o, es, o', h => by
    unfold genUndefRepeatExec at h; cases h
    exact ⟨rfl, UndefValRelUniform.nil elem⟩
  | k + 1, o, es, o', h => by
    unfold genUndefRepeatExec at h
    cases h1 : f o with
    | error e => rw [h1] at h; cases h
    | ok p1 =>
      rw [h1] at h
      obtain ⟨v, o1⟩ := p1
      dsimp only at h
      cases h2 : genUndefRepeatExec f k o1 with
      | error e => rw [h2] at h; cases h
      | ok p2 =>
        rw [h2] at h
        obtain ⟨vs, o2⟩ := p2
        cases h
        obtain ⟨hlen, hunif⟩ := genUndefRepeatExec_sound hf k o1 vs _ h2
        exact ⟨by simp [hlen], UndefValRelUniform.cons (hf o v o1 h1) hunif⟩

mutual
private theorem genUndefNondetExec_sound (dl : DataLayout) (cfg : SemanticsConfig)
    (hne : cfg.undefMode ≠ .zero) :
    ∀ (ty : LlvmType) (o : OracleState) {v : RegisterValue} {o' : OracleState},
      genUndefNondetExec dl ty o = .ok (v, o') → UndefValRel dl cfg ty v
  | .int w, o, _, _, h => by
    unfold genUndefNondetExec at h
    cases hnext : o.nextBitVec w with
    | mk bv o1 =>
      rw [hnext] at h; cases h
      exact UndefValRel.int w bv (fun hz => absurd hz hne)
  | .byte w, o, _, _, h => by
    unfold genUndefNondetExec at h
    cases hnext : nextByteBits dl w o with
    | mk bv o1 =>
      rw [hnext] at h; cases h
      exact UndefValRel.byte w bv (fun hz => absurd hz hne)
  | .float ft, o, _, _, h => by
    unfold genUndefNondetExec at h
    cases hnext : o.nextBitVec ft.bitWidth with
    | mk bv o1 =>
      rw [hnext] at h; cases h
      exact UndefValRel.float ft bv (fun hz => absurd hz hne)
  | .ptr as, o, _, _, h => by
    unfold genUndefNondetExec at h
    dsimp only at h
    cases hnext : o.nextBitVec (dl.getPointerSizeInBits as) with
    | mk bv o1 =>
      rw [hnext] at h; cases h
      exact UndefValRel.ptr as bv (fun hz => absurd hz hne)
  | .vector n elem, o, _, _, h => by
    unfold genUndefNondetExec at h
    cases hrep : genUndefRepeatExec (genUndefNondetExec dl elem) n o with
    | error e => rw [hrep] at h; cases h
    | ok p =>
      rw [hrep] at h; cases h
      obtain ⟨hlen, hunif⟩ := genUndefRepeatExec_sound
        (fun o0 v0 o1 h0 => genUndefNondetExec_sound dl cfg hne elem o0 h0) n o p.1 p.2 hrep
      exact UndefValRel.vector n elem p.1 hlen hunif
  | .array n elem, o, _, _, h => by
    unfold genUndefNondetExec at h
    cases hrep : genUndefRepeatExec (genUndefNondetExec dl elem) n o with
    | error e => rw [hrep] at h; cases h
    | ok p =>
      rw [hrep] at h; cases h
      obtain ⟨hlen, hunif⟩ := genUndefRepeatExec_sound
        (fun o0 v0 o1 h0 => genUndefNondetExec_sound dl cfg hne elem o0 h0) n o p.1 p.2 hrep
      exact UndefValRel.array n elem p.1 hlen hunif
  | .struct packed fields, o, _, _, h => by
    unfold genUndefNondetExec at h
    cases hl : genUndefListExec dl fields o with
    | error e => rw [hl] at h; cases h
    | ok p =>
      rw [hl] at h; cases h
      exact UndefValRel.struct packed fields p.1 (genUndefListExec_sound dl cfg hne fields o hl)
  | .function .., _, _, _, h | .named _, _, _, _, h => by unfold genUndefNondetExec at h; cases h

private theorem genUndefListExec_sound (dl : DataLayout) (cfg : SemanticsConfig)
    (hne : cfg.undefMode ≠ .zero) :
    ∀ (ts : List LlvmType) (o : OracleState) {vs : List RegisterValue} {o' : OracleState},
      genUndefListExec dl ts o = .ok (vs, o') → UndefValRelList dl cfg ts vs
  | [], _, _, _, h => by unfold genUndefListExec at h; cases h; exact UndefValRelList.nil
  | t :: ts, o, _, _, h => by
    unfold genUndefListExec at h
    cases h1 : genUndefNondetExec dl t o with
    | error e => rw [h1] at h; cases h
    | ok p1 =>
      rw [h1] at h
      obtain ⟨v, o1⟩ := p1
      dsimp only at h
      cases h2 : genUndefListExec dl ts o1 with
      | error e => rw [h2] at h; cases h
      | ok p2 =>
        rw [h2] at h
        obtain ⟨vs, o2⟩ := p2
        cases h
        exact UndefValRelList.cons
          (genUndefNondetExec_sound dl cfg hne t o h1)
          (genUndefListExec_sound dl cfg hne ts o1 h2)
end

theorem genUndefExec_sound {dl cfg ty o v o'}
    (h : genUndefExec dl cfg ty o = .ok (v, o')) :
    cfg.allowUndef = true ∧ UndefValRel dl cfg ty v := by
  unfold genUndefExec at h
  cases hm : cfg.undefMode with
  | disabled => rw [hm] at h; cases h
  | zero =>
    rw [hm] at h
    cases hz : genUndefZeroExec dl ty with
    | error e => rw [hz] at h; cases h
    | ok vz =>
      rw [hz] at h; cases h
      exact ⟨by simp [SemanticsConfig.allowUndef, hm], genUndefZeroExec_sound dl cfg ty hz⟩
  | nondet =>
    rw [hm] at h
    exact ⟨by simp [SemanticsConfig.allowUndef, hm],
      genUndefNondetExec_sound dl cfg (by rw [hm]; decide) ty o h⟩

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
    if flags.nuw && BitVec.uaddOverflow oldIdx offset then
      (.poison, .poison)
    else
      let nuswBad := flags.hasNUSW &&
        (if !offset.msb then newIdx < oldIdx else oldIdx < newIdx)
      if nuswBad then
        (.poison, .poison)
      else
        let highBits : Nat := (ptr.addr.toNat >>> idxW) <<< idxW
        let newAddrNat := highBits ||| newIdx.toNat
        let newAddr := BitVec.ofNat ptr.addrWidth newAddrNat
        let inboundsCheck : Bool × Provenance :=
          if !flags.inbounds then (true, ptr.prov)
          else match mem.resolveObject? ptr with
            | none => (false, ptr.prov)
            | some mo =>
              if mo.inBounds ptr.addr.toNat && mo.inBounds newAddr.toNat then
                let prov' := match ptr.prov with
                  | .wildcard g none wid => Provenance.wildcard g (some mo.allocId) wid
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

/-- Pure GEP evaluation over evaluated base pointer and index values. -/
def evalGEPValuesPure (dl : DataLayout) (mem : MemoryState) (flags : GEPFlags)
    (baseTy ptrTy : LlvmType) (basePtrVal : RegisterValue) (idxVals : List RegisterValue) :
    Except ExecError RegisterValue := do
  let addrSpace := match ptrTy.scalarType with
    | .ptr as => as
    | _ => 0
  let idxW := dl.getIndexSizeInBits addrSpace
  let initAcc : List (PoisonOr (BitVec idxW)) :=
    match basePtrVal with
    | .vector _ es => List.replicate es.length (.value (BitVec.ofNat idxW 0))
    | _ => [.value (BitVec.ofNat idxW 0)]

  let applyScaled (idxVal : RegisterValue) (scale : Nat)
      (res : RegisterValue) (acc : List (PoisonOr (BitVec idxW))) :
      Except ExecError (RegisterValue × List (PoisonOr (BitVec idxW))) := do
    match res, idxVal with
    | .vector _ ptrs, .vector _ idxs =>
      if ptrs.length != idxs.length then
        .error (.staticError "Mismatched vector lengths in getelementptr")
      let mut newPtrs : List RegisterValue := []
      let mut newAcc : List (PoisonOr (BitVec idxW)) := []
      for i in List.range ptrs.length do
        let pOpt := match ptrs.getD i (.ptr addrSpace .poison) with
          | .ptr _ po => po
          | _ => .poison
        let iOpt := canonicalizeGEPIndex idxW flags (idxs.getD i (.bv idxW .poison))
        let aOpt := acc.getD i .poison
        match computeScaledPtrAdd mem flags pOpt iOpt scale aOpt with
        | (p', a') =>
          newPtrs := newPtrs ++ [.ptr addrSpace p']
          newAcc := newAcc ++ [a']
      .ok (.vector (.ptr addrSpace) newPtrs, newAcc)
    | .vector _ ptrs, scalarIdx =>
      let iOpt := canonicalizeGEPIndex idxW flags scalarIdx
      let mut newPtrs : List RegisterValue := []
      let mut newAcc : List (PoisonOr (BitVec idxW)) := []
      for i in List.range ptrs.length do
        let pOpt := match ptrs.getD i (.ptr addrSpace .poison) with
          | .ptr _ po => po
          | _ => .poison
        let aOpt := acc.getD i .poison
        match computeScaledPtrAdd mem flags pOpt iOpt scale aOpt with
        | (p', a') =>
          newPtrs := newPtrs ++ [.ptr addrSpace p']
          newAcc := newAcc ++ [a']
      .ok (.vector (.ptr addrSpace) newPtrs, newAcc)
    | scalarPtr, .vector _ idxs =>
      let pOpt := match scalarPtr with
        | .ptr _ po => po
        | _ => .poison
      let a0 := acc.headD .poison
      let mut newPtrs : List RegisterValue := []
      let mut newAcc : List (PoisonOr (BitVec idxW)) := []
      for idx in idxs do
        let iOpt := canonicalizeGEPIndex idxW flags idx
        match computeScaledPtrAdd mem flags pOpt iOpt scale a0 with
        | (p', a') =>
          newPtrs := newPtrs ++ [.ptr addrSpace p']
          newAcc := newAcc ++ [a']
      .ok (.vector (.ptr addrSpace) newPtrs, newAcc)
    | scalarPtr, scalarIdx =>
      let pOpt := match scalarPtr with
        | .ptr _ po => po
        | _ => .poison
      let iOpt := canonicalizeGEPIndex idxW flags scalarIdx
      let a0 := acc.headD .poison
      match computeScaledPtrAdd mem flags pOpt iOpt scale a0 with
      | (p', a') => .ok (.ptr addrSpace p', [a'])

  let rec stepIdxs (isFirst : Bool) (curRes : RegisterValue)
      (accOff : List (PoisonOr (BitVec idxW))) (curTy : Option LlvmType) :
      List RegisterValue → Except ExecError RegisterValue
    | [] => .ok curRes
    | idxVal :: rest => do
      if isFirst then
        let stride := dl.typeAllocSize baseTy
        let (r', a') ← applyScaled idxVal stride curRes accOff
        stepIdxs false r' a' (some baseTy) rest
      else
        match curTy with
        | some (.struct packed fieldTys) =>
          let fieldIdx? : Option Nat := match idxVal with
            | .bv _ (.value bv) => some bv.toNat
            | .vector _ ((.bv _ (.value bv)) :: _) => some bv.toNat
            | _ => none
          match fieldIdx? with
          | none => .error (.staticError "Invalid struct index in getelementptr")
          | some fi =>
            match dl.structFieldOffset? packed fieldTys fi, fieldTys[fi]? with
            | some byteOff, some fTy =>
              let offScalar := RegisterValue.bv idxW (.value (BitVec.ofNat idxW byteOff))
              let offVal := match idxVal with
                | .vector _ es => RegisterValue.vector (.int idxW) (List.replicate es.length offScalar)
                | _ => offScalar
              let (r', a') ← applyScaled offVal 1 curRes accOff
              stepIdxs false r' a' (some fTy) rest
            | _, _ => .error (.staticError s!"Struct index {fi} out of bounds in getelementptr")
        | some (.array _ elemTy) =>
          let stride := dl.typeAllocSize elemTy
          let (r', a') ← applyScaled idxVal stride curRes accOff
          stepIdxs false r' a' (some elemTy) rest
        | some (.vector _ elemTy) =>
          let stride := dl.typeAllocSize elemTy
          let (r', a') ← applyScaled idxVal stride curRes accOff
          stepIdxs false r' a' (some elemTy) rest
        | some other =>
          .error (.staticError s!"Cannot index into non-aggregate type {other.print} in getelementptr")
        | none =>
          .error (.staticError "Internal error in getelementptr type traversal")
  stepIdxs true basePtrVal initAcc none idxVals

/-! ### Shared Pure Deterministic Value & Attribute Operations -/

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

private def mapListOracle (f : RegisterValue → OracleState → Except ExecError (RegisterValue × OracleState)) :
    List RegisterValue → OracleState → Except ExecError (List RegisterValue × OracleState)
  | [], o0 => .ok ([], o0)
  | e :: es, o0 =>
    match f e o0 with
    | .error err => .error err
    | .ok (r, o1) =>
      match mapListOracle f es o1 with
      | .error err => .error err
      | .ok (rs, o2) => .ok (r :: rs, o2)

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
          match evalFPConvO dstFt cfg fmf fw o0 with
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
          match evalIntToFPO dstFt cfg false nneg fmf iv o0 with
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
          match evalIntToFPO dstFt cfg true false fmf iv o0 with
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
      let r := evalFloatUnaryOpO op fw o0
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
        let r := evalFloatBinaryOpO cfg op (h ▸ fw1) fw2 o0
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
