/-
Nondeterminism oracle and explicit supply chains for `undef`, `freeze`, and FP nondeterminism.
-/

/-- Finite supply chain (kept for compatibility with list-based tests and proofs). -/
abbrev SupplyChain (α : Type) := List α

structure SupplyState (α : Type) where
  supplyChain : SupplyChain α
  supplyIndex : Nat
deriving Repr, DecidableEq

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

/--
A total nondeterminism oracle mapping draw indices to natural numbers.
Unlike a finite list, a total oracle never runs out of values, avoiding spurious
out-of-supply errors during refinement quantification while remaining executable.
-/
abbrev NondetOracle := Nat → Nat

namespace NondetOracle

/-- Constant zero oracle (useful for deterministic execution). -/
@[simp]
def zero : NondetOracle := fun _ => 0

/-- Construct a total oracle from a finite list, falling back to `fallback` past the end. -/
@[simp]
def ofList (xs : List Nat) (fallback : Nat := 0) : NondetOracle :=
  fun i => xs.getD i fallback

/-- Constant oracle always returning `v`. -/
@[simp]
def const (v : Nat) : NondetOracle := fun _ => v

/-- Shift an oracle by `k` draws. -/
@[simp]
def shift (k : Nat) (o : NondetOracle) : NondetOracle :=
  fun i => o (i + k)

end NondetOracle

/-- Execution state for total nondeterministic draws (`undef`, `freeze`, NaN, `nsz`, denormals). -/
structure OracleState where
  oracle : NondetOracle := NondetOracle.zero
  index  : Nat := 0

instance : Inhabited OracleState where
  default := ⟨NondetOracle.zero, 0⟩

namespace OracleState

@[simp]
def ofList (xs : List Nat) (fallback : Nat := 0) : OracleState :=
  ⟨NondetOracle.ofList xs fallback, 0⟩

/-- Draw the next natural number from the oracle. -/
@[simp]
def nextNat : OracleState → Nat × OracleState
  | ⟨oracle, index⟩ => (oracle index, ⟨oracle, index + 1⟩)

/-- Draw the next boolean from the oracle. -/
@[simp]
def nextBool : OracleState → Bool × OracleState
  | ⟨oracle, index⟩ => (oracle index % 2 == 1, ⟨oracle, index + 1⟩)

/-- Draw a bitvector of width `w` from the oracle. -/
@[simp]
def nextBitVec (w : Nat) : OracleState → BitVec w × OracleState
  | ⟨oracle, index⟩ => (BitVec.ofNat w (oracle index), ⟨oracle, index + 1⟩)

end OracleState
