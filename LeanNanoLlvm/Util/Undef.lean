/-
Total nondeterminism oracle for executable LLVM IR interpretation (`undef`, `freeze`, FP nondeterminism).
-/

/--
A total nondeterminism oracle mapping draw indices to natural numbers.
Unlike a finite list, a total oracle never runs out of values while remaining kernel-reducible.
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

/-- Execution state for total nondeterministic draws in the executable interpreter. -/
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

/-- Allocate a strictly unique positive identifier (monotonic counter for wildcard provenance). -/
@[simp]
def freshId : OracleState → Nat × OracleState
  | ⟨oracle, index⟩ => (index + 1, ⟨oracle, index + 1⟩)

end OracleState
