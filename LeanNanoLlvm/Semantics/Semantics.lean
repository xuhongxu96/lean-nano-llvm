/-
Released under Apache 2.0 license as described in the LICENSE of Lean-MLIR.
-/

import LeanNanoLlvm.Util.Poison
import LeanNanoLlvm.Tactic

namespace LeanNanoLlvm.Semantics

open PoisonOr (value poison)

def IntW w := PoisonOr <| BitVec w

namespace IntW

instance : Inhabited (IntW w) := by simp [IntW]; infer_instance
instance : DecidableEq (IntW w) := by simp [IntW]; infer_instance

end IntW

@[simp_llvm]
def and? {w : Nat} (x y : BitVec w) : IntW w :=
  .value <| x &&& y

@[simp_llvm_option]
theorem and?_eq : and? a b = .value (a &&& b) := rfl

@[simp_llvm_option]
def and {w : Nat} (x y : IntW w) : IntW w := do
  let x ← x
  let y ← y
  and? x y

@[simp_llvm]
def or? {w : Nat} (x y : BitVec w) : IntW w :=
  .value <| x ||| y

@[simp_llvm_option]
theorem or?_eq : or? a b = .value (a ||| b) := rfl

structure DisjointFlag where
  disjoint : Bool := false
deriving Repr, DecidableEq, Lean.ToExpr

@[simp_llvm_option]
def or {w : Nat} (x y : IntW w) (flag : DisjointFlag := {disjoint := false}) : IntW w := do
  let x ← x
  let y ← y
  if flag.disjoint ∧ x &&& y != 0 then
    .poison
  else
    or? x y

@[simp_llvm]
def xor? {w : Nat} (x y : BitVec w) : IntW w :=
  .value <| x ^^^ y

@[simp_llvm_option]
theorem xor?_eq : xor? a b  = .value (a ^^^ b) := rfl

@[simp_llvm_option]
def xor {w : Nat} (x y : IntW w) : IntW w := do
  let x ← x
  let y ← y
  xor? x y

@[simp_llvm]
def add? {w : Nat} (x y : BitVec w) : IntW w :=
  .value <| x + y

@[simp_llvm_option]
theorem add?_eq : add? a b  = .value (a + b) := rfl

structure NoWrapFlags where
  nuw : Bool := false
  nsw : Bool := false
deriving Repr, DecidableEq, Lean.ToExpr

@[simp_llvm_option]
def add {w : Nat} (x y : IntW w) (flags : NoWrapFlags := {nsw := false , nuw := false}) : IntW w := do
  let x ← x
  let y ← y
  if flags.nsw ∧ BitVec.saddOverflow x y then
    .poison
  else if flags.nuw ∧ BitVec.uaddOverflow x y then
    .poison
  else
    add? x y

@[simp_llvm]
def sub? {w : Nat} (x y : BitVec w) : IntW w :=
  .value <| x - y

@[simp_llvm_option]
theorem sub?_eq : sub? a b  = .value (a - b) := rfl

@[simp_llvm_option]
def sub {w : Nat} (x y : IntW w) (flags : NoWrapFlags := {nsw := false , nuw := false}) : IntW w := do
  let x ← x
  let y ← y
  if flags.nsw ∧ BitVec.ssubOverflow x y then
    .poison
  else if flags.nuw ∧ BitVec.usubOverflow x y then
    .poison
  else
    sub? x y

@[simp_llvm]
def mul? {w : Nat} (x y : BitVec w) : IntW w :=
  .value <| x * y

@[simp_llvm_option]
theorem mul?_eq : mul? a b  = .value (a * b) := rfl

@[simp_llvm_option]
def mul {w : Nat} (x y : IntW w) (flags : NoWrapFlags := {nsw := false , nuw := false}) : IntW w := do
  let x ← x
  let y ← y

  if flags.nsw ∧ BitVec.smulOverflow x y then
    .poison
  else if flags.nuw ∧ BitVec.umulOverflow x y then
    .poison
  else
    mul? x y

@[simp_llvm]
def udiv? {w : Nat} (x y : BitVec w) : IntW w :=
  if y = 0 then
    .poison
  else
    .value <| x / y

structure ExactFlag where
  exact : Bool := false
deriving Repr, DecidableEq, Lean.ToExpr

@[simp_llvm_option]
def udiv {w : Nat} (x y : IntW w) (flag : ExactFlag := {exact := false}) : IntW w := do
  let x ← x
  let y ← y
  if flag.exact ∧ x.umod y ≠ 0 then
    .poison
  else
    udiv? x y

@[simp_llvm]
def sdiv? {w : Nat} (x y : BitVec w) : IntW w :=
  if y == 0 || (w != 1 && x == (BitVec.intMin w) && y == -1) then
    .poison
  else
    .value (x.sdiv y)

theorem sdiv?_denom_zero_eq_poison {w : Nat} (x : BitVec w) :
  sdiv? x 0 = .poison := by
  simp [sdiv?]

theorem sdiv?_eq_value_of_neq_allOnes {x y : BitVec w} (hy : y ≠ 0)
    (hx : BitVec.intMin w ≠ x) : sdiv? x y = .value (BitVec.sdiv x y) := by
  simp [sdiv?]
  intro h
  simp_all

@[simp_llvm_option]
def sdiv {w : Nat} (x y : IntW w) (flag : ExactFlag := {exact := false}) : IntW w := do
  let x ← x
  let y ← y
  if flag.exact ∧ x.smod y ≠ 0 then
    .poison
  else
    sdiv? x y

@[simp_llvm]
theorem sdiv?_eq_div_if {w : Nat} {x y : BitVec w} :
    sdiv? x y =
    if (y = 0) ∨ ((w ≠ 1) ∧ (x = BitVec.intMin w) ∧ (y = -1))
      then .poison
    else .value <| BitVec.sdiv x y
    := by
  simp [sdiv?]
  split <;> try intros; try simp_all
  intro h
  simp_all

@[simp_llvm]
def urem? {w : Nat} (x y : BitVec w) : IntW w :=
  if y = 0 then
    .poison
  else
    .value <| x % y

@[simp_llvm_option]
def urem {w : Nat} (x y : IntW w) : IntW w := do
  let x ← x
  let y ← y
  urem? x y

@[simp_llvm]
def _root_.Int.rem (x y : Int) : Int :=
  if x ≥ 0 then (x % y) else ((x % y) - y.natAbs)

theorem _root_.Int.rem_sign_dividend :
  ∀ x y, Int.rem x y < 0 ↔ x < 0 := by
  intro x y
  constructor <;> simp [Int.rem]; split <;> by_cases (y = 0) <;> rename_i hx hy <;> try grind
  . intro hcontra
    exfalso
    apply (Int.not_le.2 hcontra)
    exact Int.emod_nonneg x hy
  . intro hx
    split
    . omega
    . by_cases (y = 0)
      case pos hy => simp [hy]; exact hx
      case neg hy =>
        suffices x % y < ↑y.natAbs by omega
        by_cases (0 < y)
        case pos hy =>
          have hyleq : 0 ≤ y := by omega
          rw [← Int.eq_natAbs_of_nonneg]
          . simp_all [Int.emod_lt_of_pos]
          . omega
        case neg hy =>
          have hmyneg : 0 < -y := by omega
          have hmynnonpos : 0 ≤ -y := by omega
          rw [← Int.emod_neg, ← Int.natAbs_neg]
          rw [← Int.eq_natAbs_of_nonneg]
          . exact Int.emod_lt_of_pos x hmyneg
          . assumption

@[simp_llvm]
def srem? {w : Nat} (x y : BitVec w) : IntW w :=
  if y == 0 || (w != 1 && x == (BitVec.intMin w) && y == -1) then
    .poison
  else
    .value <| BitVec.srem x y

@[simp_llvm_option]
def srem {w : Nat} (x y : IntW w) : IntW w := do
  let x ← x
  let y ← y
  srem? x y

@[simp_llvm]
def sshr (a : BitVec n) (s : Nat) := BitVec.sshiftRight a s

@[simp_llvm]
def shl? {n} (op1 : BitVec n) (op2 : BitVec n) : IntW n :=
  if op2 >= n
  then .poison
  else .value (op1 <<< op2)


@[simp_llvm_option]
def shl {w : Nat} (x y : IntW w) (flags : NoWrapFlags := {nsw := false , nuw := false}) : IntW w := do
  let x ← x
  let y ← y
    -- "If the nsw keyword is present, then the shift produces a poison value if it shifts out any bits that disagree with the resultant sign bit."
  if flags.nsw ∧ ((x <<< y).sshiftRight' y ≠ x) then
    .poison
  else if flags.nuw ∧ ((x <<< y) >>> y ≠ x) then
    .poison
  else
    shl? x y

@[simp_llvm]
def lshr? {n} (op1 : BitVec n) (op2 : BitVec n) : IntW n :=
  if op2 >= n
  then .poison
  else .value (op1 >>> op2)

@[simp_llvm_option]
def lshr {w : Nat} (x y : IntW w) (flag : ExactFlag := {exact := false}) : IntW w := do
  let x ← x
  let y ← y
  if flag.exact ∧(x >>> y) <<< y ≠ x then
    .poison
  else
    lshr? x y

@[simp_llvm]
def ashr? {n} (op1 : BitVec n) (op2 : BitVec n) : IntW n :=
  if op2 >= n
  then .poison
  else .value (op1.sshiftRight' op2)

@[simp_llvm_option]
def ashr {w : Nat} (x y : IntW w) (flag : ExactFlag := {exact := false}) : IntW w := do
  let x ← x
  let y ← y
  if flag.exact ∧ (x >>> y) <<< y ≠ x then
    .poison
  else
    ashr? x y

@[simp_llvm]
def trunc? {w: Nat} (w': Nat) (x: BitVec w) : IntW w' := do
  .value <| (BitVec.truncate w' x)

@[simp_llvm_option]
def trunc {w: Nat} (w': Nat) (x: IntW w) (noWrapFlags : NoWrapFlags := {nsw := false , nuw := false}) : IntW w' := do
  let x <- x
  if noWrapFlags.nsw ∧ ((x.truncate w').signExtend w ≠ x) then
    .poison
  else if noWrapFlags.nuw ∧ ((x.truncate w').zeroExtend w ≠ x) then
    .poison
  else
    trunc? w' x

structure NonNegFlag where
  nneg : Bool := false
  deriving Repr, DecidableEq, Lean.ToExpr

@[simp_llvm]
def zext? {w: Nat} (w': Nat) (x: BitVec w) : IntW w' := do
  .value <| (BitVec.zeroExtend w' x)

@[simp_llvm_option]
def zext {w: Nat} (w': Nat) (x: IntW w) (flag : NonNegFlag := {nneg := false}) : IntW w' := do
  let x <- x
  if flag.nneg ∧ x.msb then
    .poison
  else
    zext? w' x

@[simp_llvm]
def sext? {w: Nat} (w': Nat) (x: BitVec w) : IntW w' := do
  .value <| (BitVec.signExtend w' x)

@[simp_llvm_option]
def sext {w: Nat} (w': Nat) (x: IntW w) : IntW w' := do
  let x <- x
  sext? w' x

@[simp_llvm_option]
def freeze (x: IntW w) : IntW w := do
  match x with
  | poison => value (0) -- FIXME: is this correct? it should be an arbitrary but fixed value
  | value a => value (a)

end LeanNanoLlvm.Semantics
