import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.Util.Hex

/-!
# Floating-point literals in LLVM's textual formats

Bit-exact re-implementations of the two LLVM routines that `llubi --verbose` relies on when
printing floating-point numbers:

* `APFloat::toString(Str, FormatPrecision, /*FormatMaxPadding=*/0, /*TruncateZero=*/false)`,
  including its two-stage truncation (`AdjustToPrecision` on the binary significand, then
  round-half-up on the decimal digit buffer), and
* the `AsmWriter` constant printer `writeAPFloatInternal` (`+inf`, `+qnan`, `-snan(0x..)`,
  round-trip decimal, or `f0x...` bit pattern).

`x86_fp80` values are stored with an implicit integer bit in `IEEEFloat`; `bits80` rebuilds the
explicit-integer-bit 80-bit encoding that LLVM's `bitcastToAPInt` produces.
-/

namespace LeanNanoLlvm.AST.FloatLiteral


/-- Number of significant bits of `n` (`APInt::getActiveBits`). -/
def activeBits (n : Nat) : Nat := if n == 0 then 0 else Nat.log2 n + 1

private def trailingZeros (n : Nat) : Nat := Id.run do
  if n == 0 then return 0
  let mut k := 0
  let mut m := n
  while m % 2 == 0 do
    m := m / 2
    k := k + 1
  return k

/-- `AdjustToPrecision(APInt &significand, int &exp, unsigned FormatPrecision)`. -/
private def adjustSigToPrecision (sig : Nat) (exp : Int) (prec : Nat) : Nat × Int :=
  let bits := activeBits sig
  let bitsRequired := (prec * 196 + 58) / 59
  if bits ≤ bitsRequired then (sig, exp)
  else
    let tens := (bits - bitsRequired) * 59 / 196
    if tens == 0 then (sig, exp)
    else (sig / 10 ^ tens, exp + tens)

/-- `AdjustToPrecision(SmallVectorImpl<char> &buffer, ...)`: `buf` holds decimal digits
least-significant first. Rounds half-up to `prec` digits, dropping trailing zeros. -/
private def adjustBufToPrecision (buf : Array Nat) (exp : Int) (prec : Nat) : Array Nat × Int := Id.run do
  let n := buf.size
  if n ≤ prec then return (buf, exp)
  let mut first := n - prec
  if buf[first - 1]! < 5 then
    while first < n && buf[first]! == 0 do
      first := first + 1
    return (buf.extract first n, exp + first)
  -- round up with carry
  let mut b := buf
  let mut i := first
  let mut done := false
  while i < n && !done do
    if b[i]! == 9 then
      first := first + 1
      i := i + 1
    else
      b := b.set! i (b[i]! + 1)
      done := true
  if first == n then
    return (#[1], exp + first)
  return (b.extract first n, exp + first)

/-- `IEEEFloat::toString(Str, prec, 0, false)` for a finite non-zero value
`(-1)^neg * mant * 2^exp2`. -/
def toStringFinite (neg : Bool) (mant : Nat) (exp2 : Int) (prec : Nat := 6) : String := Id.run do
  let tz := trailingZeros mant
  let m := mant >>> tz
  let e2 := exp2 + tz
  let (sig0, exp0) : Nat × Int :=
    if e2 ≥ 0 then (m <<< e2.toNat, 0) else (m * 5 ^ (-e2).toNat, e2)
  let (sig1, exp1) := adjustSigToPrecision sig0 exp0 prec
  -- Fill the digit buffer (least significant first), dropping trailing zeros.
  let mut buf : Array Nat := #[]
  let mut exp := exp1
  let mut s := sig1
  let mut inTrail := true
  while s != 0 do
    let d := s % 10
    s := s / 10
    if inTrail && d == 0 then exp := exp + 1
    else
      buf := buf.push d
      inTrail := false
  let (buf2, exp2') := adjustBufToPrecision buf exp prec
  let nd := buf2.size
  let expSci : Int := exp2' + (nd - 1 : Nat)
  let digit (i : Nat) : Char := Char.ofNat ('0'.toNat + buf2[i]!)
  let mut out := if neg then "-" else ""
  out := out.push (digit (nd - 1))
  out := out.push '.'
  for i in [1:nd] do
    out := out.push (digit (nd - 1 - i))
  if prec + 1 > nd then
    out := out ++ String.ofList (List.replicate (prec - nd + 1) '0')
  out := out.push 'e'
  out := out.push (if expSci ≥ 0 then '+' else '-')
  let ae := expSci.natAbs
  let es := toString ae
  out := out ++ (if es.length < 2 then "0" ++ es else es)
  return out

/-- `APFloat::toString(Str, 6, 0, false)` of an `IEEEFloat`. -/
def apToString {fmt : FloatFormat} (x : IEEEFloat fmt) (prec : Nat := 6) : String :=
  if x.isInf then if x.sign then "-Inf" else "+Inf"
  else if x.isNaN then "NaN"
  else if x.isZero then
    (if x.sign then "-" else "") ++ "0.0" ++ String.ofList (List.replicate (prec - 1) '0') ++ "e+00"
  else
    let (s, m, e) := x.toDyadic
    toStringFinite s m e prec

/-- Parse back a string produced by `apToString` (mirrors `APFloat::convertFromString` with
round-to-nearest-even for the strings `apToString` can produce). -/
def parseBack (fmt : FloatFormat) (str : String) : Option (IEEEFloat fmt) :=
  if str == "NaN" then some (IEEEFloat.qNaN fmt)
  else if str == "+Inf" then some (IEEEFloat.inf fmt false)
  else if str == "-Inf" then some (IEEEFloat.inf fmt true)
  else
    let (neg, body) := if str.startsWith "-" then (true, (str.drop 1).toString) else (false, str)
    match body.splitOn "e" with
    | [mantStr, expStr] =>
      let digits := mantStr.toList.filter Char.isDigit
      let fracLen := match mantStr.splitOn "." with
        | [_, f] => f.length
        | _ => 0
      let mant := digits.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
      let (eneg, eStr) :=
        if expStr.startsWith "-" then (true, (expStr.drop 1).toString)
        else if expStr.startsWith "+" then (false, (expStr.drop 1).toString)
        else (false, expStr)
      match eStr.toNat? with
      | some ev =>
        let e10 : Int := (if eneg then -(ev : Int) else ev) - fracLen
        some (IEEEFloat.ofDecimal fmt .RNE neg mant e10)
      | none => none
    | _ => none

/-- `APFloat::toStringRoundTrip(Str, 6, 0, false)`: the decimal string if it round-trips. -/
def apToStringRoundTrip? {fmt : FloatFormat} (x : IEEEFloat fmt) : Option String :=
  let s := apToString x
  match parseBack fmt s with
  | some y => if y.bits.toNat == x.bits.toNat then some s else none
  | none => none

/-- `bitcastToAPInt` value and bit width of a float of LLVM type `ft`. -/
def bitcastBits (ft : FloatType) (x : IEEEFloat ft.format) : Nat × Nat :=
  match ft with
  | .x86_fp80 =>
    let intBit := if x.rawExp == 0 then 0 else 1
    let sgn := if x.sign then 1 else 0
    ((sgn <<< 79) ||| (x.rawExp <<< 64) ||| (intBit <<< 63) ||| x.rawSig, 80)
  | _ => (x.bits.toNat, ft.bitWidth)

/-- `ppc_fp128` (double-double) decimal rendering if it round-trips: the high double carries the
whole value (low double zero) and its 6-digit decimal is exact. Lean stores `ppc_fp128` as a
128-bit pattern whose low 64 bits are the high double. -/
def ppcDecimal? (bits : Nat) : Option String :=
  let hiD : IEEEFloat .double := IEEEFloat.ofNatBits (bits &&& ((1 <<< 64) - 1))
  let loD := bits >>> 64
  if loD != 0 then none
  else
    let str := apToString hiD
    if hiD.isNaN || hiD.isInf then some str
    else
      match parseBack .fp128 str with
      | some y =>
        if y.bits.toNat == (IEEEFloat.convert .fp128 .RNE hiD).bits.toNat then some str else none
      | none => none

/-- `llubi` (`AnyValue::print`) rendering of a non-poison float payload (without the type). -/
def llubiString (ft : FloatType) (x : IEEEFloat ft.format) : String :=
  if ft == .ppc_fp128 then
    match ppcDecimal? x.bits.toNat with
    | some s => s
    | none => "0x" ++ Hex.upperPadded 32 x.bits.toNat
  else
  match apToStringRoundTrip? x with
  | some s => s
  | none =>
    let (bits, w) := bitcastBits ft x
    "0x" ++ Hex.upperPadded ((w + 3) / 4) bits

/-- `writeAPFloatInternal` for a float of a non-`ppc_fp128` type. -/
private def asmStringIEEE (ft : FloatType) (x : IEEEFloat ft.format) : String :=
  if x.isInf then (if x.sign then "-" else "+") ++ "inf"
  else if x.isNaN then
    let sgn := if x.sign then "-" else "+"
    let fmt := ft.format
    let payload := x.rawSig
    if payload == fmt.quietBit then sgn ++ "qnan"
    else
      let s := if x.isSNaN then "s" else ""
      let p := payload &&& (fmt.quietBit - 1)
      let digits := max ((activeBits p + 3) / 4) 1
      sgn ++ s ++ "nan(0x" ++ Hex.upperPadded digits p ++ ")"
  else
    let str := apToString x
    match parseBack ft.format str with
    | some y =>
      if y.bits.toNat == x.bits.toNat then str
      else
        let (bits, w) := bitcastBits ft x
        "f0x" ++ Hex.upperPadded ((w + 3) / 4) bits
    | none =>
      let (bits, w) := bitcastBits ft x
      "f0x" ++ Hex.upperPadded ((w + 3) / 4) bits

/-- LLVM `AsmWriter` rendering of a floating-point constant (`writeAPFloatInternal`). A
`ppc_fp128` whose low double is zero prints as its high double when that is infinite or NaN. -/
def asmString (ft : FloatType) (x : IEEEFloat ft.format) : String :=
  if ft == .ppc_fp128 then
    let bits := x.bits.toNat
    let hiD : IEEEFloat .double := IEEEFloat.ofNatBits (bits &&& ((1 <<< 64) - 1))
    if (bits >>> 64) == 0 && (hiD.isInf || hiD.isNaN) then asmStringIEEE .double hiD
    else match ppcDecimal? bits with
      | some s => s
      | none => "f0x" ++ Hex.upperPadded 32 bits
  else asmStringIEEE ft x

end LeanNanoLlvm.AST.FloatLiteral
