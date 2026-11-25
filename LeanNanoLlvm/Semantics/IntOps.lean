/-
Adapted in part from Lean-MLIR.
See LICENSE and NOTICE in this repository for licensing and attribution details.

https://github.com/opencompl/lean-mlir
-/

import LeanNanoLlvm.Util.Poison
import LeanNanoLlvm.Util.Config
import LeanNanoLlvm.AST.AST
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
  split <;> try simp_all
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

/-! ### Immediate-UB-faithful Division and Remainder (matches `llubi::computeDivRem`) -/

/--
LLVM division/remainder with exact Immediate UB precedence:
- Poison RHS → Immediate UB (can refine RHS to 0)
- Zero RHS → Immediate UB
- Signed div/rem with poison LHS and RHS = -1 (all ones) → Immediate UB (can refine LHS to INT_MIN)
- Signed div/rem with LHS = INT_MIN and RHS = -1 → Immediate UB
- Otherwise poison LHS → poison; exact flag violation → poison.
-/
@[simp_llvm]
def evalDivRemUB {w : Nat} (isSigned isRem exact : Bool) (lhs rhs : IntW w) :
    Except ExecError (IntW w) :=
  match rhs with
  | .poison => .error (.immediateUB "Division by zero (poison divisor)")
  | .value y =>
    if y == 0 then
      .error (.immediateUB "Division by zero")
    else match lhs with
    | .poison =>
      if isSigned && y == BitVec.allOnes w then
        .error (.immediateUB "Signed division overflow (poison dividend with divisor -1)")
      else
        .ok .poison
    | .value x =>
      if isSigned && x == BitVec.intMin w && y == BitVec.allOnes w then
        .error (.immediateUB "Signed division overflow (INT_MIN / -1)")
      else if isRem then
        .ok (.value (if isSigned then BitVec.srem x y else x % y))
      else
        let r := if isSigned then BitVec.srem x y else x % y
        if exact && r != 0 then
          .ok .poison
        else
          .ok (.value (if isSigned then BitVec.sdiv x y else x / y))

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
  if y ≥ w then
    .poison
  else if flags.nsw ∧ ((x <<< y).sshiftRight' y ≠ x) then
    .poison
  else if flags.nuw ∧ ((x <<< y) >>> y ≠ x) then
    .poison
  else
    .value (x <<< y)

@[simp_llvm]
def lshr? {n} (op1 : BitVec n) (op2 : BitVec n) : IntW n :=
  if op2 >= n
  then .poison
  else .value (op1 >>> op2)

@[simp_llvm_option]
def lshr {w : Nat} (x y : IntW w) (flag : ExactFlag := {exact := false}) : IntW w := do
  let x ← x
  let y ← y
  if y ≥ w then
    .poison
  else if flag.exact ∧ (x >>> y) <<< y ≠ x then
    .poison
  else
    .value (x >>> y)

@[simp_llvm]
def ashr? {n} (op1 : BitVec n) (op2 : BitVec n) : IntW n :=
  if op2 >= n
  then .poison
  else .value (op1.sshiftRight' op2)

@[simp_llvm_option]
def ashr {w : Nat} (x y : IntW w) (flag : ExactFlag := {exact := false}) : IntW w := do
  let x ← x
  let y ← y
  if y ≥ w then
    .poison
  else if flag.exact ∧ (x.sshiftRight' y) <<< y ≠ x then
    .poison
  else
    .value (x.sshiftRight' y)

@[simp_llvm]
def trunc? {w : Nat} (w' : Nat) (x : BitVec w) : IntW w' := do
  .value <| (BitVec.truncate w' x)

@[simp_llvm_option]
def trunc {w : Nat} (w' : Nat) (x : IntW w) (noWrapFlags : NoWrapFlags := {nsw := false , nuw := false}) : IntW w' := do
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
def zext? {w : Nat} (w' : Nat) (x : BitVec w) : IntW w' := do
  .value <| (BitVec.zeroExtend w' x)

@[simp_llvm_option]
def zext {w : Nat} (w' : Nat) (x : IntW w) (flag : NonNegFlag := {nneg := false}) : IntW w' := do
  let x <- x
  if flag.nneg ∧ x.msb then
    .poison
  else
    zext? w' x

@[simp_llvm]
def sext? {w : Nat} (w' : Nat) (x : BitVec w) : IntW w' := do
  .value <| (BitVec.signExtend w' x)

@[simp_llvm_option]
def sext {w : Nat} (w' : Nat) (x : IntW w) : IntW w' := do
  let x <- x
  sext? w' x

@[simp_llvm_option]
def freeze (x : IntW w) : IntW w := do
  match x with
  | poison => value (0)
  | value a => value (a)

/-! ### Integer Comparison (`icmp`) -/

@[simp_llvm]
def evalICmpPred {w : Nat} (pred : AST.ICmpPred) (x y : BitVec w) : Bool :=
  match pred with
  | .eq  => x == y
  | .ne  => x != y
  | .ugt => y < x
  | .uge => y ≤ x
  | .ult => x < y
  | .ule => x ≤ y
  | .sgt => BitVec.slt y x
  | .sge => BitVec.sle y x
  | .slt => BitVec.slt x y
  | .sle => BitVec.sle x y

@[simp_llvm_option]
def icmp {w : Nat} (samesign : Bool) (pred : AST.ICmpPred) (x y : IntW w) : IntW 1 := do
  let x ← x
  let y ← y
  if samesign && x.msb != y.msb then
    .poison
  else
    .value (BitVec.ofBool (evalICmpPred pred x y))

/-! ### Bit-Manipulation, Overflow, and Saturating Integer Intrinsics -/

def bvCtlz {w : Nat} (x : BitVec w) : BitVec w :=
  let rec go (i : Nat) (acc : Nat) : Nat :=
    match i with
    | 0 => acc
    | k + 1 =>
      if x.getLsbD k then acc else go k (acc + 1)
  BitVec.ofNat w (go w 0)

def bvCttz {w : Nat} (x : BitVec w) : BitVec w :=
  let rec go (i : Nat) : Nat → Nat
    | 0 => w
    | rem + 1 =>
      if x.getLsbD i then i else go (i + 1) rem
  BitVec.ofNat w (go 0 w)

def bvCtpop {w : Nat} (x : BitVec w) : BitVec w :=
  let rec go (i : Nat) (acc : Nat) : Nat :=
    match i with
    | 0 => acc
    | k + 1 => go k (acc + if x.getLsbD k then 1 else 0)
  BitVec.ofNat w (go w 0)

def bvBitReverse {w : Nat} (x : BitVec w) : BitVec w :=
  let rec go (i : Nat) (acc : Nat) : Nat :=
    match i with
    | 0 => acc
    | k + 1 =>
      let bit := if x.getLsbD k then 1 <<< (w - 1 - k) else 0
      go k (acc ||| bit)
  BitVec.ofNat w (go w 0)

def bvBSwap {w : Nat} (x : BitVec w) : BitVec w :=
  let nBytes := w / 8
  let rec go (i : Nat) (acc : Nat) : Nat :=
    match i with
    | 0 => acc
    | k + 1 =>
      let byteVal := (x.toNat >>> (k * 8)) &&& 0xFF
      let dstShift := (nBytes - 1 - k) * 8
      go k (acc ||| (byteVal <<< dstShift))
  BitVec.ofNat w (go nBytes 0)

def bvFshl {w : Nat} (a b amt : BitVec w) : BitVec w :=
  if w == 0 then 0
  else
    let s := amt.toNat % w
    let concat : BitVec (w + w) := BitVec.append a b
    ((concat <<< s).extractLsb' w w)

def bvFshr {w : Nat} (a b amt : BitVec w) : BitVec w :=
  if w == 0 then 0
  else
    let s := amt.toNat % w
    let concat : BitVec (w + w) := BitVec.append a b
    ((concat >>> s).extractLsb' 0 w)

def bvSAddSat {w : Nat} (x y : BitVec w) : BitVec w :=
  if BitVec.saddOverflow x y then
    if x.msb then BitVec.intMin w else BitVec.intMax w
  else x + y

def bvUAddSat {w : Nat} (x y : BitVec w) : BitVec w :=
  if BitVec.uaddOverflow x y then BitVec.allOnes w else x + y

def bvSSubSat {w : Nat} (x y : BitVec w) : BitVec w :=
  if BitVec.ssubOverflow x y then
    if x.msb then BitVec.intMin w else BitVec.intMax w
  else x - y

def bvUSubSat {w : Nat} (x y : BitVec w) : BitVec w :=
  if BitVec.usubOverflow x y then 0 else x - y

end LeanNanoLlvm.Semantics
