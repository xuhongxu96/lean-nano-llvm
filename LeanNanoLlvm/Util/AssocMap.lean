namespace LeanNanoLlvm

/-- A pure, kernel-reducible finite map backed by a deduplicated association list.
    Unlike `Std.ExtHashMap` (which wraps `Quot`), `AssocMap` reduces directly inside
    Lean's kernel (`rfl` / `decide`) without relying on `native_decide` or compiler trust. -/
structure AssocMap (α β : Type) : Type where
  entries : List (α × β) := []
deriving Repr, DecidableEq, Inhabited

namespace AssocMap

def empty {α β : Type} : AssocMap α β := ⟨[]⟩

instance {α β : Type} : EmptyCollection (AssocMap α β) := ⟨empty⟩

private def lookupAux {α β : Type} [BEq α] (k : α) : List (α × β) → Option β
  | [] => none
  | (k0, v0) :: rest => if k0 == k then some v0 else lookupAux k rest

private def eraseAux {α β : Type} [BEq α] (k : α) : List (α × β) → List (α × β)
  | [] => []
  | (k0, v0) :: rest => if k0 == k then eraseAux k rest else (k0, v0) :: eraseAux k rest

def get? {α β : Type} [BEq α] (m : AssocMap α β) (k : α) : Option β :=
  lookupAux k m.entries

def insert {α β : Type} [BEq α] (m : AssocMap α β) (k : α) (v : β) : AssocMap α β :=
  ⟨(k, v) :: eraseAux k m.entries⟩

def erase {α β : Type} [BEq α] (m : AssocMap α β) (k : α) : AssocMap α β :=
  ⟨eraseAux k m.entries⟩

def contains {α β : Type} [BEq α] (m : AssocMap α β) (k : α) : Bool :=
  (m.get? k).isSome

def toList {α β : Type} (m : AssocMap α β) : List (α × β) :=
  m.entries

def fold {α β γ : Type} (f : γ → α → β → γ) (init : γ) (m : AssocMap α β) : γ :=
  m.entries.foldl (fun acc (k, v) => f acc k v) init

instance {α β : Type} [BEq α] : GetElem? (AssocMap α β) α β (fun m k => (m.get? k).isSome) where
  getElem m k h := (m.get? k).get h
  getElem? m k := m.get? k

private theorem lookupAux_eraseAux_ne {α β : Type} [BEq α] [LawfulBEq α]
    (k k' : α) (hne : (k == k') = false) :
    ∀ (l : List (α × β)), lookupAux k' (eraseAux k l) = lookupAux k' l
  | [] => rfl
  | (k0, v0) :: rest => by
    simp only [eraseAux, lookupAux]
    by_cases h0 : (k0 == k) = true
    · simp only [h0, ↓reduceIte]
      have hk0 : k0 = k := eq_of_beq h0
      subst hk0
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      exact lookupAux_eraseAux_ne _ k' hne rest
    · have h0f : (k0 == k) = false := Bool.eq_false_iff.mpr h0
      simp only [h0f, Bool.false_eq_true, ↓reduceIte, lookupAux]
      by_cases h1 : (k0 == k') = true
      · simp only [h1, ↓reduceIte]
      · have h1f : (k0 == k') = false := Bool.eq_false_iff.mpr h1
        simp only [h1f, Bool.false_eq_true, ↓reduceIte]
        exact lookupAux_eraseAux_ne k k' hne rest

private theorem lookupAux_eraseAux_eq {α β : Type} [BEq α] [LawfulBEq α]
    (k : α) : ∀ (l : List (α × β)), lookupAux k (eraseAux k l) = none
  | [] => rfl
  | (k0, v0) :: rest => by
    simp only [eraseAux]
    by_cases h0 : (k0 == k) = true
    · simp only [h0, ↓reduceIte]
      exact lookupAux_eraseAux_eq k rest
    · have h0f : (k0 == k) = false := Bool.eq_false_iff.mpr h0
      simp only [h0f, Bool.false_eq_true, ↓reduceIte, lookupAux]
      exact lookupAux_eraseAux_eq k rest

@[simp]
theorem get?_empty {α β : Type} [BEq α] (k : α) :
    (∅ : AssocMap α β).get? k = none := rfl

@[simp]
theorem get?_empty' {α β : Type} [BEq α] (k : α) :
    (AssocMap.empty : AssocMap α β).get? k = none := rfl

@[simp]
theorem get?_mk_nil {α β : Type} [BEq α] (k : α) :
    (AssocMap.mk ([] : List (α × β))).get? k = none := rfl

@[simp]
theorem get?_insert {α β : Type} [BEq α] [LawfulBEq α] (m : AssocMap α β) (k k' : α) (v : β) :
    (m.insert k v).get? k' = if k == k' then some v else m.get? k' := by
  simp only [insert, get?, lookupAux]
  by_cases h : (k == k') = true
  · simp only [h, ↓reduceIte]
  · have hf : (k == k') = false := Bool.eq_false_iff.mpr h
    simp only [hf, Bool.false_eq_true, ↓reduceIte]
    exact lookupAux_eraseAux_ne k k' hf m.entries

@[simp]
theorem get?_erase {α β : Type} [BEq α] [LawfulBEq α] (m : AssocMap α β) (k k' : α) :
    (m.erase k).get? k' = if k == k' then none else m.get? k' := by
  simp only [erase, get?]
  by_cases h : (k == k') = true
  · have heq : k = k' := eq_of_beq h
    subst heq
    simp only [h, ↓reduceIte]
    exact lookupAux_eraseAux_eq _ m.entries
  · have hf : (k == k') = false := Bool.eq_false_iff.mpr h
    simp only [hf, Bool.false_eq_true, ↓reduceIte]
    exact lookupAux_eraseAux_ne k k' hf m.entries

@[simp]
theorem getElem?_eq_get? {α β : Type} [BEq α] (m : AssocMap α β) (k : α) :
    m[k]? = m.get? k := rfl

@[simp]
theorem contains_eq_isSome {α β : Type} [BEq α] (m : AssocMap α β) (k : α) :
    m.contains k = (m.get? k).isSome := rfl

theorem get?_isSome_of_mem_keys {α β : Type} [BEq α] [LawfulBEq α]
    (m : AssocMap α β) {k : α} (hk : k ∈ m.entries.map Prod.fst) :
    ∃ v, m.get? k = some v := by
  cases m with
  | mk entries =>
    dsimp only [get?]
    induction entries with
    | nil => simp at hk
    | cons hd rest ih =>
      obtain ⟨k0, v0⟩ := hd
      simp only [List.map_cons, List.mem_cons] at hk
      unfold lookupAux
      by_cases h0 : (k0 == k) = true
      · rw [if_pos h0]; exact ⟨v0, rfl⟩
      · rw [if_neg h0]
        rcases hk with rfl | hrest
        · exact False.elim (h0 (beq_self_eq_true _))
        · exact ih hrest

private theorem eraseAux_idem {α β : Type} [BEq α] (k : α) :
    ∀ (l : List (α × β)), eraseAux k (eraseAux k l) = eraseAux k l
  | [] => rfl
  | (k0, v0) :: rest => by
    simp only [eraseAux]
    by_cases h0 : (k0 == k) = true
    · rw [if_pos h0]; exact eraseAux_idem k rest
    · rw [if_neg h0]; simp only [eraseAux, if_neg h0, eraseAux_idem k rest]

@[simp]
theorem insert_insert_same {α β : Type} [BEq α] [LawfulBEq α]
    (m : AssocMap α β) (k : α) (v1 v2 : β) :
    (m.insert k v1).insert k v2 = m.insert k v2 := by
  simp only [insert, eraseAux, beq_self_eq_true, ↓reduceIte, eraseAux_idem]

end AssocMap

end LeanNanoLlvm
