abbrev SupplyChain (α : Type) := List α

structure SupplyState (α : Type) where
  supplyChain : SupplyChain α
  supplyIndex : Nat

abbrev UndefM (α : Type) := StateT (SupplyState α) (Except (Nat × Nat))

instance [Inhabited α] : Inhabited (SupplyState α) where
  default := ⟨[], 0⟩

namespace SupplyState

/-- The number of available undefined values from `s` at index `s.supplyIndex`. -/
def isWellFormed (s : SupplyState α) : Prop :=
  s.supplyIndex ≤ s.supplyChain.length

end SupplyState

namespace UndefM

@[match_pattern, simp]
def undef [Inhabited α] : UndefM α α := do
  let s ← get
  match s.supplyChain[s.supplyIndex]? with
  | .some v =>
    set { s with supplyIndex := s.supplyIndex + 1 }
    pure v
  | .none => throw (s.supplyIndex, s.supplyChain.length)

@[match_pattern, simp]
def value (v : α) : UndefM α α := pure v

end UndefM
