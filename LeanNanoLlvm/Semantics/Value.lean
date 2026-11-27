import LeanNanoLlvm.Util.Config
import LeanNanoLlvm.Util.Oracle
import LeanNanoLlvm.Util.AssocMap
import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.DataLayout
import LeanNanoLlvm.AST.Print
import LeanNanoLlvm.Semantics.IntOps
import LeanNanoLlvm.Semantics.FloatOps
import LeanNanoLlvm.Semantics.MemoryRefinement

/-!
# Runtime values

`RegisterValue`, the value of an SSA register (mirroring `llubi::AnyValue`), its decidable
equality and basic queries, and value refinement under a `MemoryInjection`.
-/

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

end LeanNanoLlvm.Semantics
