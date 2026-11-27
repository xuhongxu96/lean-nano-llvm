import LeanNanoLlvm.Util.Config
import LeanNanoLlvm.Util.Oracle
import LeanNanoLlvm.Util.AssocMap
import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.DataLayout
import LeanNanoLlvm.AST.Print
import LeanNanoLlvm.Util.Hex
import LeanNanoLlvm.AST.FloatLiteral
import LeanNanoLlvm.Semantics.Value

/-!
# Provenance tags and `llubi`-style rendering of values

`llubi` prints values with `AnyValue::print`; the same text appears in its diagnostics, so the
semantics' error messages use `RegisterValue.llubiString`. Pointer bytes carry a random
provenance tag, drawn the first time a pointer to an object is serialized; tags only affect
printing (and the oracle stream), never execution.
-/

namespace LeanNanoLlvm.Semantics

open AST

namespace RegisterValue

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

/-! ### `llubi`-compatible rendering (`llvm::ubi::AnyValue::print`) -/

/-- Value of LSB-first concrete bits (non-concrete bits count as 0). -/
def bitsValue (bits : List MemBit) : Nat :=
  bits.foldr (fun b acc => acc * 2 + (match b with | .concrete true _ => 1 | _ => 0)) 0

/-- `PrintByte` of `ByteValue::print` for one chunk (`bits` LSB-first, at most 8 bits). -/
def llubiByteChunk (bits : List MemBit) (full : Bool) (tags : List (Nat × Nat) := []) : String :=
  let allConcreteNoTag := bits.all fun | .concrete _ none => true | _ => false
  let allPoison := bits.all fun | .concrete .. => false | _ => true
  if full && allConcreteNoTag then "0x" ++ Hex.upperPadded 2 (bitsValue bits)
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
  | .float ft (.value f) => s!"{ft.print} {FloatLiteral.llubiString ft f}"
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

end RegisterValue

/-- Draw a provenance tag for object `id` unless it has one (a random `w`-bit value, redrawn
while zero or already used). Tags only record `llubi`'s random-stream consumption and its
printing; they have no semantic effect. -/
def drawTag (id w : Nat) (o : OracleState) : OracleState :=
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
def drawPtrTags (v : RegisterValue) (o : OracleState) : OracleState :=
  (RegisterValue.taggedPtrs v).foldl (fun o0 (q : Nat × Nat) => drawTag q.1 q.2 o0) o

end LeanNanoLlvm.Semantics
