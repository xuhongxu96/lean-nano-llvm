import LeanNanoLlvm.Util.Config

namespace LeanNanoLlvm

/-- Parameters defining an IEEE-754 binary floating-point format. -/
structure FloatFormat : Type where
  expBits : Nat
  sigBits : Nat -- trailing significand bits (excluding implicit leading bit)
deriving Repr, DecidableEq, Inhabited

namespace FloatFormat

def half   : FloatFormat := { expBits := 5,  sigBits := 10 }   -- IEEE binary16
def bfloat : FloatFormat := { expBits := 8,  sigBits := 7 }    -- bfloat16
def single : FloatFormat := { expBits := 8,  sigBits := 23 }   -- IEEE binary32 (float)
def double : FloatFormat := { expBits := 11, sigBits := 52 }   -- IEEE binary64 (double)
def fp128  : FloatFormat := { expBits := 15, sigBits := 112 }  -- IEEE binary128 (fp128)

@[simp] def totalBits (fmt : FloatFormat) : Nat := 1 + fmt.expBits + fmt.sigBits
@[simp] def precision (fmt : FloatFormat) : Nat := fmt.sigBits + 1
@[simp] def bias      (fmt : FloatFormat) : Nat := (1 <<< (fmt.expBits - 1)) - 1
@[simp] def expMask   (fmt : FloatFormat) : Nat := (1 <<< fmt.expBits) - 1
@[simp] def sigMask   (fmt : FloatFormat) : Nat := (1 <<< fmt.sigBits) - 1
@[simp] def quietBit  (fmt : FloatFormat) : Nat := 1 <<< (fmt.sigBits - 1)
@[simp] def eMin      (fmt : FloatFormat) : Int := 1 - (fmt.bias : Int)
@[simp] def eMax      (fmt : FloatFormat) : Int := (fmt.bias : Int)

end FloatFormat

/- LLVM `llvm.is.fpclass` classification bitmask constants. -/
namespace FPClassMask
  def snan       : Nat := 1 <<< 0
  def qnan       : Nat := 1 <<< 1
  def negInf     : Nat := 1 <<< 2
  def negNormal  : Nat := 1 <<< 3
  def negSubnorm : Nat := 1 <<< 4
  def negZero    : Nat := 1 <<< 5
  def posZero    : Nat := 1 <<< 6
  def posSubnorm : Nat := 1 <<< 7
  def posNormal  : Nat := 1 <<< 8
  def posInf     : Nat := 1 <<< 9
end FPClassMask

/-- Computable, kernel-reducible bit-level IEEE-754 binary floating-point value. -/
structure IEEEFloat (fmt : FloatFormat) : Type where
  bits : BitVec fmt.totalBits
deriving DecidableEq, Repr

namespace IEEEFloat

variable {fmt : FloatFormat}

instance : Inhabited (IEEEFloat fmt) := ⟨⟨0⟩⟩

@[simp] def ofBits (b : BitVec fmt.totalBits) : IEEEFloat fmt := ⟨b⟩
@[simp] def ofNatBits (n : Nat) : IEEEFloat fmt := ⟨BitVec.ofNat fmt.totalBits n⟩
@[simp] def toBits (x : IEEEFloat fmt) : BitVec fmt.totalBits := x.bits

/-- Pack `(sign, rawExp, rawSig)` into an `IEEEFloat`. -/
def pack (fmt : FloatFormat) (sign : Bool) (rawExp rawSig : Nat) : IEEEFloat fmt :=
  let sBit := if sign then (1 <<< (fmt.expBits + fmt.sigBits)) else 0
  let eBits := (rawExp &&& fmt.expMask) <<< fmt.sigBits
  let mBits := rawSig &&& fmt.sigMask
  ⟨BitVec.ofNat fmt.totalBits (sBit ||| eBits ||| mBits)⟩

@[simp] def sign (x : IEEEFloat fmt) : Bool :=
  ((x.bits.toNat >>> (fmt.expBits + fmt.sigBits)) &&& 1) == 1

@[simp] def rawExp (x : IEEEFloat fmt) : Nat :=
  (x.bits.toNat >>> fmt.sigBits) &&& fmt.expMask

@[simp] def rawSig (x : IEEEFloat fmt) : Nat :=
  x.bits.toNat &&& fmt.sigMask

@[simp] def isZero      (x : IEEEFloat fmt) : Bool := x.rawExp == 0 && x.rawSig == 0
@[simp] def isSubnormal (x : IEEEFloat fmt) : Bool := x.rawExp == 0 && x.rawSig != 0
@[simp] def isNormal    (x : IEEEFloat fmt) : Bool := x.rawExp != 0 && x.rawExp != fmt.expMask
@[simp] def isFinite    (x : IEEEFloat fmt) : Bool := x.rawExp != fmt.expMask
@[simp] def isInf       (x : IEEEFloat fmt) : Bool := x.rawExp == fmt.expMask && x.rawSig == 0
@[simp] def isNaN       (x : IEEEFloat fmt) : Bool := x.rawExp == fmt.expMask && x.rawSig != 0
@[simp] def isQNaN      (x : IEEEFloat fmt) : Bool := x.isNaN && ((x.rawSig &&& fmt.quietBit) != 0)
@[simp] def isSNaN      (x : IEEEFloat fmt) : Bool := x.isNaN && ((x.rawSig &&& fmt.quietBit) == 0)
@[simp] def isNegZero   (x : IEEEFloat fmt) : Bool := x.isZero && x.sign
@[simp] def isPosZero   (x : IEEEFloat fmt) : Bool := x.isZero && !x.sign

def zero (fmt : FloatFormat) (neg : Bool := false) : IEEEFloat fmt :=
  pack fmt neg 0 0

def inf (fmt : FloatFormat) (neg : Bool := false) : IEEEFloat fmt :=
  pack fmt neg fmt.expMask 0

def maxFinite (fmt : FloatFormat) (neg : Bool := false) : IEEEFloat fmt :=
  pack fmt neg (fmt.expMask - 1) fmt.sigMask

def qNaN (fmt : FloatFormat) (neg : Bool := false) (payload : Nat := 0) : IEEEFloat fmt :=
  pack fmt neg fmt.expMask ((payload &&& fmt.sigMask) ||| fmt.quietBit)

def sNaN (fmt : FloatFormat) (neg : Bool := false) (payload : Nat := 1) : IEEEFloat fmt :=
  let p := (payload &&& (fmt.sigMask ^^^ fmt.quietBit))
  let p' := if p == 0 then 1 else p
  pack fmt neg fmt.expMask p'

def makeQuiet (x : IEEEFloat fmt) : IEEEFloat fmt :=
  if x.isNaN then pack fmt x.sign fmt.expMask (x.rawSig ||| fmt.quietBit) else x

/-- Bitwise negation (flips the sign bit, including for NaN and ±0). -/
def neg (x : IEEEFloat fmt) : IEEEFloat fmt :=
  ⟨x.bits ^^^ (1#(fmt.totalBits) <<< (fmt.expBits + fmt.sigBits))⟩

@[simp]
theorem neg_neg (x : IEEEFloat fmt) : x.neg.neg = x := by
  cases x
  simp [neg, BitVec.xor_assoc]
  exact BitVec.xor_zero

/-- Bitwise absolute value (clears the sign bit, including for NaN and -0). -/
def abs (x : IEEEFloat fmt) : IEEEFloat fmt :=
  pack fmt false x.rawExp x.rawSig

/-- Bitwise copysign (magnitude of `mag`, sign bit of `sgn`). -/
def copySign (mag sgn : IEEEFloat fmt) : IEEEFloat fmt :=
  pack fmt sgn.sign mag.rawExp mag.rawSig

/-- Classification mask bit (matches LLVM `llvm.is.fpclass`). -/
def fpClassBit (x : IEEEFloat fmt) : Nat :=
  if x.isSNaN then FPClassMask.snan
  else if x.isQNaN then FPClassMask.qnan
  else if x.isInf then if x.sign then FPClassMask.negInf else FPClassMask.posInf
  else if x.isZero then if x.sign then FPClassMask.negZero else FPClassMask.posZero
  else if x.isSubnormal then if x.sign then FPClassMask.negSubnorm else FPClassMask.posSubnorm
  else if x.sign then FPClassMask.negNormal else FPClassMask.posNormal

/--
Decompose a finite non-zero float into `(sign, mantissa, exp2)` such that its exact
real value is `(-1)^sign * mantissa * 2^exp2` with `mantissa > 0`.
-/
def toDyadic (x : IEEEFloat fmt) : Bool × Nat × Int :=
  if x.rawExp == 0 then
    (x.sign, x.rawSig, fmt.eMin - (fmt.sigBits : Int))
  else
    let m := (1 <<< fmt.sigBits) ||| x.rawSig
    let e := (x.rawExp : Int) - (fmt.bias : Int) - (fmt.sigBits : Int)
    (x.sign, m, e)

/-- Compute `floor(log2(num / den))` exactly for `num > 0, den > 0`. -/
private def floorLog2Rat (num den : Nat) : Int :=
  let d : Int := (Nat.log2 num : Int) - (Nat.log2 den : Int)
  if d ≥ 0 then
    if num < den <<< d.toNat then d - 1 else d
  else
    if num <<< (-d).toNat < den then d - 1 else d

/-- Result of overflow for a given sign and rounding mode. -/
def overflowResult (fmt : FloatFormat) (rm : RoundingMode) (sign : Bool) : IEEEFloat fmt :=
  match rm with
  | .RNE | .RNA => inf fmt sign
  | .RTZ => maxFinite fmt sign
  | .RTP => if sign then maxFinite fmt true else inf fmt false
  | .RTN => if sign then inf fmt true else maxFinite fmt false

/-- Apply IEEE-754 rounding increment decision given `(sign, quot, rem, den, rm)`. -/
private def shouldRoundUp (rm : RoundingMode) (sign : Bool) (quot rem den : Nat) : Bool :=
  if rem == 0 then false
  else match rm with
    | .RTZ => false
    | .RTP => !sign
    | .RTN => sign
    | .RNA => 2 * rem ≥ den
    | .RNE =>
      let twiceRem := 2 * rem
      if twiceRem > den then true
      else if twiceRem < den then false
      else quot % 2 == 1

/--
Exact IEEE-754 rounding of `(-1)^sign * (num / den) * 2^exp2` (with `num > 0, den > 0`)
into format `fmt` under rounding mode `rm`.
-/
def roundExact (fmt : FloatFormat) (rm : RoundingMode) (sign : Bool)
    (num den : Nat) (exp2 : Int) : IEEEFloat fmt :=
  if num == 0 || den == 0 then zero fmt sign
  else
    let e : Int := floorLog2Rat num den + exp2
    if e > fmt.eMax + 1 then
      overflowResult fmt rm sign
    else if e < fmt.eMin - (fmt.sigBits : Int) - 2 then
      -- Strictly less than half the minimum subnormal quantum
      if shouldRoundUp rm sign 0 1 4 then
        pack fmt sign 0 1
      else
        zero fmt sign
    else
      let isSub := e < fmt.eMin
      let q : Int := if isSub then fmt.eMin - (fmt.sigBits : Int) else e - (fmt.sigBits : Int)
      let shift : Int := exp2 - q
      let (n', d') :=
        if shift ≥ 0 then (num <<< shift.toNat, den)
        else (num, den <<< (-shift).toNat)
      let quot := n' / d'
      let rem := n' % d'
      let quot' := if shouldRoundUp rm sign quot rem d' then quot + 1 else quot
      if isSub then
        if quot' == 0 then zero fmt sign
        else if quot' ≥ (1 <<< fmt.sigBits) then
          pack fmt sign 1 0
        else
          pack fmt sign 0 quot'
      else
        let carryLimit := 1 <<< fmt.precision
        if quot' ≥ carryLimit then
          let e' := e + 1
          if e' > fmt.eMax then overflowResult fmt rm sign
          else pack fmt sign (e' + (fmt.bias : Int)).toNat 0
        else
          if e > fmt.eMax then overflowResult fmt rm sign
          else pack fmt sign (e + (fmt.bias : Int)).toNat (quot' - (1 <<< fmt.sigBits))

/-- Exact ordering between two non-NaN IEEE floats (`+0 == -0`). -/
def compareNonNaN (x y : IEEEFloat fmt) : Ordering :=
  if x.isZero && y.isZero then .eq
  else if x.sign != y.sign then
    if x.sign then .lt else .gt
  else
    -- Same sign: compare magnitude by lexicographical (rawExp, rawSig)
    let magCmp :=
      match compare x.rawExp y.rawExp with
      | .eq => compare x.rawSig y.rawSig
      | c => c
    if x.sign then
      match magCmp with
      | .lt => .gt
      | .gt => .lt
      | .eq => .eq
    else
      magCmp

/-- IEEE-754 floating-point addition. -/
def add (rm : RoundingMode) (x y : IEEEFloat fmt) : IEEEFloat fmt :=
  if x.isNaN || y.isNaN then qNaN fmt
  else if x.isInf && y.isInf then
    if x.sign == y.sign then x else qNaN fmt
  else if x.isInf then x
  else if y.isInf then y
  else if x.isZero && y.isZero then
    if x.sign == y.sign then x
    else zero fmt (rm == .RTN)
  else if x.isZero then y
  else if y.isZero then x
  else
    let (sx, mx, ex) := x.toDyadic
    let (sy, my, ey) := y.toDyadic
    -- Short-circuit if exponents differ by more than precision + 4
    let minE := min ex ey
    let vx : Int := (if sx then -1 else 1) * (mx : Int)
    let vy : Int := (if sy then -1 else 1) * (my : Int)
    let diff := ex - ey
    let gapLimit : Int := (fmt.precision : Int) + 4
    if diff > gapLimit then
      -- |y| < 2^(-(precision+3)) * |x|: compress y to a single sticky bit below x
      let stickyExp : Int := ex - gapLimit
      let sum : Int := (vx <<< gapLimit.toNat) + (if sy then -1 else 1)
      roundExact fmt rm (sum < 0) sum.natAbs 1 stickyExp
    else if diff < -gapLimit then
      let stickyExp : Int := ey - gapLimit
      let sum : Int := (vy <<< gapLimit.toNat) + (if sx then -1 else 1)
      roundExact fmt rm (sum < 0) sum.natAbs 1 stickyExp
    else
      let ax : Int := vx * ((1 : Nat) <<< (ex - minE).toNat)
      let ay : Int := vy * ((1 : Nat) <<< (ey - minE).toNat)
      let sum : Int := ax + ay
      if sum == 0 then zero fmt (rm == .RTN)
      else roundExact fmt rm (sum < 0) sum.natAbs 1 minE

/-- IEEE-754 floating-point subtraction. -/
def sub (rm : RoundingMode) (x y : IEEEFloat fmt) : IEEEFloat fmt :=
  add rm x y.neg

/-- IEEE-754 floating-point multiplication. -/
def mul (rm : RoundingMode) (x y : IEEEFloat fmt) : IEEEFloat fmt :=
  let resSign := x.sign != y.sign
  if x.isNaN || y.isNaN then qNaN fmt
  else if (x.isInf && y.isZero) || (x.isZero && y.isInf) then qNaN fmt
  else if x.isInf || y.isInf then inf fmt resSign
  else if x.isZero || y.isZero then zero fmt resSign
  else
    let (_, mx, ex) := x.toDyadic
    let (_, my, ey) := y.toDyadic
    roundExact fmt rm resSign (mx * my) 1 (ex + ey)

/-- IEEE-754 floating-point division. -/
def div (rm : RoundingMode) (x y : IEEEFloat fmt) : IEEEFloat fmt :=
  let resSign := x.sign != y.sign
  if x.isNaN || y.isNaN then qNaN fmt
  else if (x.isInf && y.isInf) || (x.isZero && y.isZero) then qNaN fmt
  else if x.isInf || y.isZero then inf fmt resSign
  else if y.isInf || x.isZero then zero fmt resSign
  else
    let (_, mx, ex) := x.toDyadic
    let (_, my, ey) := y.toDyadic
    roundExact fmt rm resSign mx my (ex - ey)

/-- Modular exponentiation `(base ^ exp) % modulus` for fast exact `frem`. -/
private def powMod (base exp modulus : Nat) : Nat :=
  if modulus == 0 then 0
  else go (base % modulus) exp 1
where
  go (b e acc : Nat) : Nat :=
    if e = 0 then acc
    else
      let acc' := if e % 2 == 1 then (acc * b) % modulus else acc
      go ((b * b) % modulus) (e / 2) acc'
  termination_by e

/-- LLVM `frem` (C `fmod` / `APFloat::mod`): exact remainder preserving sign of dividend `x`. -/
def rem (x y : IEEEFloat fmt) : IEEEFloat fmt :=
  if x.isNaN || y.isNaN then qNaN fmt
  else if x.isInf || y.isZero then qNaN fmt
  else if y.isInf || x.isZero then x
  else
    let (sx, mx, ex) := x.toDyadic
    let (_, my, ey) := y.toDyadic
    if ex ≥ ey then
      let shift := (ex - ey).toNat
      let r := ((mx % my) * powMod 2 shift my) % my
      if r == 0 then zero fmt sx
      else roundExact fmt .RNE sx r 1 ey
    else
      -- ey > ex: check if |x| < |y| first
      let shift := (ey - ex).toNat
      if shift > fmt.precision + 2 then x
      else
        let dy := my <<< shift
        let r := mx % dy
        if r == 0 then zero fmt sx
        else roundExact fmt .RNE sx r 1 ex

/-- IEEE-754 fused multiply-add: `round(a * b + c)` with a single rounding. -/
def fma (rm : RoundingMode) (a b c : IEEEFloat fmt) : IEEEFloat fmt :=
  let prodSign := a.sign != b.sign
  if a.isNaN || b.isNaN || c.isNaN then qNaN fmt
  else if (a.isInf && b.isZero) || (a.isZero && b.isInf) then qNaN fmt
  else if a.isInf || b.isInf then
    if c.isInf && c.sign != prodSign then qNaN fmt
    else inf fmt prodSign
  else if c.isInf then c
  else if a.isZero || b.isZero then
    if c.isZero then
      if prodSign == c.sign then zero fmt prodSign
      else zero fmt (rm == .RTN)
    else c
  else if c.isZero then
    let (_, ma, ea) := a.toDyadic
    let (_, mb, eb) := b.toDyadic
    roundExact fmt rm prodSign (ma * mb) 1 (ea + eb)
  else
    let (_, ma, ea) := a.toDyadic
    let (_, mb, eb) := b.toDyadic
    let (sc, mc, ec) := c.toDyadic
    let mp := ma * mb
    let ep := ea + eb
    let vp : Int := (if prodSign then -1 else 1) * (mp : Int)
    let vc : Int := (if sc then -1 else 1) * (mc : Int)
    let diff := ep - ec
    let gapLimit : Int := 2 * (fmt.precision : Int) + 6
    if diff > gapLimit then
      let stickyExp : Int := ep - gapLimit
      let sum : Int := (vp <<< gapLimit.toNat) + (if sc then -1 else 1)
      roundExact fmt rm (sum < 0) sum.natAbs 1 stickyExp
    else if diff < -gapLimit then
      let stickyExp : Int := ec - gapLimit
      let sum : Int := (vc <<< gapLimit.toNat) + (if prodSign then -1 else 1)
      roundExact fmt rm (sum < 0) sum.natAbs 1 stickyExp
    else
      let minE := min ep ec
      let ap : Int := vp * ((1 : Nat) <<< (ep - minE).toNat)
      let ac : Int := vc * ((1 : Nat) <<< (ec - minE).toNat)
      let sum : Int := ap + ac
      if sum == 0 then zero fmt (rm == .RTN)
      else roundExact fmt rm (sum < 0) sum.natAbs 1 minE

/-- Convert between two IEEE-754 binary formats (`fpext` / `fptrunc`). -/
def convert {srcFmt : FloatFormat} (dstFmt : FloatFormat) (rm : RoundingMode)
    (x : IEEEFloat srcFmt) : IEEEFloat dstFmt :=
  if x.isNaN then
    -- Preserve sign and MSB-aligned payload (matching IEEE-754 / APFloat::convert)
    let payload :=
      if dstFmt.sigBits ≥ srcFmt.sigBits then
        x.rawSig <<< (dstFmt.sigBits - srcFmt.sigBits)
      else
        x.rawSig >>> (srcFmt.sigBits - dstFmt.sigBits)
    qNaN dstFmt x.sign payload
  else if x.isInf then inf dstFmt x.sign
  else if x.isZero then zero dstFmt x.sign
  else
    let (sx, mx, ex) := x.toDyadic
    roundExact dstFmt rm sx mx 1 ex

/-- Convert unsigned bitvector to IEEE-754 float (`uitofp`). -/
def ofUnsignedBitVec (dstFmt : FloatFormat) (rm : RoundingMode) {w : Nat}
    (x : BitVec w) : IEEEFloat dstFmt :=
  let n := x.toNat
  if n == 0 then zero dstFmt false
  else roundExact dstFmt rm false n 1 0

/-- Convert signed bitvector to IEEE-754 float (`sitofp`). -/
def ofSignedBitVec (dstFmt : FloatFormat) (rm : RoundingMode) {w : Nat}
    (x : BitVec w) : IEEEFloat dstFmt :=
  let i := x.toInt
  if i == 0 then zero dstFmt false
  else roundExact dstFmt rm (i < 0) i.natAbs 1 0

/--
Truncate IEEE-754 float toward zero to an exact integer magnitude `(sign, truncatedMag)`.
Returns `none` for NaN or Inf.
-/
def truncateToInt? (x : IEEEFloat fmt) : Option Int :=
  if !x.isFinite then none
  else if x.isZero then some 0
  else
    let (sx, mx, ex) := x.toDyadic
    let mag : Nat :=
      if ex ≥ 0 then mx <<< ex.toNat
      else mx >>> (-ex).toNat
    some (if sx then -(mag : Int) else (mag : Int))

/-- Convert IEEE-754 float to unsigned bitvector (`fptoui`). Returns `none` (→ poison) if out of range / NaN / Inf. -/
def toUnsignedBitVec? (w : Nat) (x : IEEEFloat fmt) : Option (BitVec w) :=
  if w == 0 then some (BitVec.ofNat w 0)
  else match x.truncateToInt? with
    | none => none
    | some i =>
      if i < 0 then none
      else
        let n := i.toNat
        if n < (1 <<< w) then some (BitVec.ofNat w n) else none

/-- Convert IEEE-754 float to signed bitvector (`fptosi`). Returns `none` (→ poison) if out of range / NaN / Inf. -/
def toSignedBitVec? (w : Nat) (x : IEEEFloat fmt) : Option (BitVec w) :=
  if w == 0 then some (BitVec.ofNat w 0)
  else match x.truncateToInt? with
    | none => none
    | some i =>
      let minS : Int := -((1 : Nat) <<< (w - 1) : Int)
      let maxS : Int := ((1 : Nat) <<< (w - 1) : Int) - 1
      if minS ≤ i && i ≤ maxS then
        some (BitVec.ofInt w i)
      else
        none

/-- Saturating `fptoui.sat` (NaN → 0, < 0 → 0, > max → max). -/
def toUnsignedBitVecSat (w : Nat) (x : IEEEFloat fmt) : BitVec w :=
  if w == 0 then BitVec.ofNat w 0
  else if x.isNaN then 0
  else if x.isInf then if x.sign then 0 else BitVec.allOnes w
  else match x.truncateToInt? with
    | none => 0
    | some i =>
      if i ≤ 0 then 0
      else
        let n := i.toNat
        if n ≥ (1 <<< w) then BitVec.allOnes w else BitVec.ofNat w n

/-- Saturating `fptosi.sat` (NaN → 0, < min → min, > max → max). -/
def toSignedBitVecSat (w : Nat) (x : IEEEFloat fmt) : BitVec w :=
  if w == 0 then BitVec.ofNat w 0
  else if x.isNaN then 0
  else if x.isInf then if x.sign then BitVec.intMin w else BitVec.intMax w
  else match x.truncateToInt? with
    | none => 0
    | some i =>
      let minS : Int := -((1 : Nat) <<< (w - 1) : Int)
      let maxS : Int := ((1 : Nat) <<< (w - 1) : Int) - 1
      if i ≤ minS then BitVec.intMin w
      else if i ≥ maxS then BitVec.intMax w
      else BitVec.ofInt w i

/-- IEEE-754 `minimum` (propagates NaN, `-0 < +0`). -/
def minimum (x y : IEEEFloat fmt) : IEEEFloat fmt :=
  if x.isNaN || y.isNaN then qNaN fmt
  else if x.isZero && y.isZero then if x.sign || y.sign then zero fmt true else zero fmt false
  else match compareNonNaN x y with
    | .gt => y
    | _ => x

/-- IEEE-754 `maximum` (propagates NaN, `-0 < +0`). -/
def maximum (x y : IEEEFloat fmt) : IEEEFloat fmt :=
  if x.isNaN || y.isNaN then qNaN fmt
  else if x.isZero && y.isZero then if x.sign && y.sign then zero fmt true else zero fmt false
  else match compareNonNaN x y with
    | .lt => y
    | _ => x

/-- IEEE-754 `minimumnum` / `minnum` (returns non-NaN operand if one is NaN; `-0 < +0`). -/
def minimumnum (x y : IEEEFloat fmt) : IEEEFloat fmt :=
  if x.isNaN && y.isNaN then qNaN fmt
  else if x.isNaN then y
  else if y.isNaN then x
  else if x.isZero && y.isZero then if x.sign || y.sign then zero fmt true else zero fmt false
  else match compareNonNaN x y with
    | .gt => y
    | _ => x

/-- IEEE-754 `maximumnum` / `maxnum` (returns non-NaN operand if one is NaN; `-0 < +0`). -/
def maximumnum (x y : IEEEFloat fmt) : IEEEFloat fmt :=
  if x.isNaN && y.isNaN then qNaN fmt
  else if x.isNaN then y
  else if y.isNaN then x
  else if x.isZero && y.isZero then if x.sign && y.sign then zero fmt true else zero fmt false
  else match compareNonNaN x y with
    | .lt => y
    | _ => x

/-- Exact, kernel-reducible conversion from decimal `(-1)^neg * mantissa * 10^exp10` to `IEEEFloat fmt`. -/
def ofDecimal (fmt : FloatFormat) (rm : RoundingMode) (neg : Bool)
    (mantissa : Nat) (exp10 : Int) : IEEEFloat fmt :=
  if mantissa == 0 then zero fmt neg
  else if exp10 ≥ 0 then
    roundExact fmt rm neg (mantissa * (10 ^ exp10.toNat)) 1 0
  else
    roundExact fmt rm neg mantissa (10 ^ (-exp10).toNat) 0

/-- Convert a Lean `Float` (IEEE binary64) to `IEEEFloat .double` via exact bit pattern. -/
def ofLeanFloat (f : Float) : IEEEFloat .double :=
  ⟨BitVec.ofNat 64 f.toBits.toNat⟩

/-- Convert an `IEEEFloat .double` back to a Lean `Float`. -/
def toLeanFloat (x : IEEEFloat .double) : Float :=
  Float.ofBits x.bits.toNat.toUInt64

/-- Construct an `IEEEFloat fmt` from a Lean `Float` (via binary64 bit pattern + exact IEEE conversion). -/
def fromLeanFloat (fmt : FloatFormat) (f : Float) (rm : RoundingMode := .RNE) : IEEEFloat fmt :=
  (ofLeanFloat f).convert fmt rm

/-- Pretty-print an `IEEEFloat` in LLVM-style hex/special notation. -/
def toStringHex (x : IEEEFloat fmt) : String :=
  if x.isInf then if x.sign then "-Inf" else "+Inf"
  else if x.isNaN then
    let kind := if x.isSNaN then "snan" else "qnan"
    let sgn := if x.sign then "-" else "+"
    s!"{sgn}{kind}"
  else
    let hexDigits := (fmt.totalBits + 3) / 4
    let raw := String.ofList (Nat.toDigits 16 x.bits.toNat)
    let pad := String.ofList (List.replicate (hexDigits - raw.length) '0')
    s!"0x{pad}{raw}"

instance : ToString (IEEEFloat fmt) where
  toString := toStringHex

end IEEEFloat

end LeanNanoLlvm
