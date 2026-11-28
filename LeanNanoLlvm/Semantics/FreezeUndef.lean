import LeanNanoLlvm.Util.Config
import LeanNanoLlvm.Util.Oracle
import LeanNanoLlvm.Util.AssocMap
import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.DataLayout
import LeanNanoLlvm.AST.Print
import LeanNanoLlvm.Semantics.Bytes

/-!
# `freeze` and `undef`

Relational specifications (`FreezeRel`, `UndefValRel`) of the values `freeze` and `undef` may
produce, and executable generators proven to satisfy them for every oracle.
-/

namespace LeanNanoLlvm.Semantics

open AST

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
      FreezeRel dl cfg (.float ft .poison) (.float ft (.value (IEEEFloat.ofBits bits).readEncoding))
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
    | (bits, o') => (.float ft (.value (IEEEFloat.ofBits bits).readEncoding), o')
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
      UndefValRel dl cfg (.float ft) (.float ft (.value (IEEEFloat.ofBits bits).readEncoding))
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
  | .float ft => .ok (.float ft (.value (IEEEFloat.ofBits (BitVec.ofNat ft.bitWidth 0)).readEncoding))
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
    | (bv, o') => .ok (.float ft (.value (IEEEFloat.ofBits bv).readEncoding), o')
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

end LeanNanoLlvm.Semantics
