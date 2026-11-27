/-!
# Nondeterminism oracle

The executable interpreter resolves every nondeterministic choice (`undef` bits, `freeze`, NaN
payloads, provenance tags, ...) by drawing from an `OracleState`. The relational semantics
quantifies over all oracles; the `llubi` frontend feeds `std::mt19937_64` output.
-/

namespace LeanNanoLlvm

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

/-- Execution state for total nondeterministic draws in the executable interpreter.

`index` is the position in the oracle stream; every draw consumes stream entries exactly where
`llubi` consumes outputs of its `std::mt19937_64` (so the stream of a seeded generator reproduces
`llubi`'s choices). `nextId` is a separate counter for fresh identifiers (wildcard provenances),
which do not consume the stream, and `tags` records the provenance tags `llubi` draws the first
time a pointer of a memory object is written as bytes (`allocId ↦ tag`); tags have no semantic
effect and only make the executable stream position (and printing) match `llubi`. -/
structure OracleState where
  oracle : NondetOracle := NondetOracle.zero
  index  : Nat := 0
  nextId : Nat := 0
  tags   : List (Nat × Nat) := []

instance : Inhabited OracleState where
  default := { oracle := NondetOracle.zero, index := 0 }

namespace OracleState

@[simp]
def ofList (xs : List Nat) (fallback : Nat := 0) : OracleState :=
  { oracle := NondetOracle.ofList xs fallback, index := 0 }

/-- Draw the next natural number from the oracle (`Rng()`). -/
@[simp]
def nextNat (o : OracleState) : Nat × OracleState :=
  (o.oracle o.index, { o with index := o.index + 1 })

/-- Draw the next boolean from the oracle (`Rng() & 1`). -/
@[simp]
def nextBool (o : OracleState) : Bool × OracleState :=
  (o.oracle o.index % 2 == 1, { o with index := o.index + 1 })

/-- Draw `n` 64-bit words starting at stream position `i`, least-significant word first. -/
@[simp]
def drawWords (f : NondetOracle) : Nat → Nat → Nat × Nat
  | 0, i => (0, i)
  | k + 1, i =>
    match drawWords f k (i + 1) with
    | (rest, j) => (f i % 2 ^ 64 + rest * 2 ^ 64, j)

/-- Draw a bitvector of width `w` from the oracle, one 64-bit word per started 64 bits
(`llubi`'s `generateRandomAPInt`). -/
@[simp]
def nextBitVec (w : Nat) (o : OracleState) : BitVec w × OracleState :=
  if w ≤ 64 then (BitVec.ofNat w (o.oracle o.index), { o with index := o.index + 1 })
  else
    match drawWords o.oracle ((w + 63) / 64) o.index with
    | (v, j) => (BitVec.ofNat w v, { o with index := j })

/-- Allocate a strictly unique positive identifier (monotonic counter for wildcard provenance);
does not consume the oracle stream. -/
@[simp]
def freshId (o : OracleState) : Nat × OracleState :=
  (o.nextId + 1, { o with nextId := o.nextId + 1 })

/-- Draw a boolean only if `cond` holds (`llubi` draws lazily, only when a choice exists). -/
@[simp]
def boolIf (cond : Bool) (o : OracleState) : Bool × OracleState :=
  if cond then o.nextBool else (false, o)

end OracleState

end LeanNanoLlvm
