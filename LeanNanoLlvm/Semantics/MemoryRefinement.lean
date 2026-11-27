import LeanNanoLlvm.Semantics.Memory

/-!
# Memory injections and memory refinement

CompCert/Alive2-style memory injections between the memories of a source and a target program,
and the induced refinement of bits, bytes and memory states.
-/

namespace LeanNanoLlvm.Semantics

open AST

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
