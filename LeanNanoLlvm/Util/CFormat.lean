import LeanNanoLlvm.Util.IEEEFloat

/-!
# Exact C `printf` conversions

Total, exact implementations of the C99 `printf` conversions that `llubi`'s `printf` supports
(it forwards to the host C library with default precision): `%d %i %u %o %x %X %c` on 64-bit
values and `%f %F %e %E %g %G %a %A` on IEEE doubles, with the `-`, ` `, `#`, `0` flags and a
field width. Decimal conversions are correctly rounded (round-half-even on the exact binary value,
as glibc does), so the produced text — and thus `printf`'s return value — is exact.
-/

namespace LeanNanoLlvm.CFormat

/-- Parsed conversion flags/width. -/
structure Spec where
  leftAlign : Bool := false
  space     : Bool := false
  alt       : Bool := false
  zeroPad   : Bool := false
  width     : Nat := 0
deriving Inhabited

/-- Round `num / den` to the nearest integer, ties to even. -/
def roundHalfEven (num den : Nat) : Nat :=
  let q := num / den
  let r := num % den
  if 2 * r > den then q + 1
  else if 2 * r < den then q
  else if q % 2 == 1 then q + 1 else q

private def padZerosLeft (s : String) (n : Nat) : String :=
  String.ofList (List.replicate (n - s.length) '0') ++ s

/-- `⌊log10 (num / den)⌋` for `num, den > 0` (bounded search). -/
def floorLog10 (num den : Nat) : Int :=
  if num ≥ den then ((Nat.toDigits 10 (num / den)).length : Int) - 1
  else
    -- smallest k ≥ 1 with num * 10^k ≥ den; result is -k
    let rec go (k : Nat) (fuel : Nat) : Int :=
      match fuel with
      | 0 => -(k : Int)
      | fuel' + 1 => if num * 10 ^ k ≥ den then -(k : Int) else go (k + 1) fuel'
    go 1 (Nat.log2 den + 2)

/-- Fixed notation with `prec` decimals of `num / den`. -/
def fixedDigits (num den prec : Nat) : String :=
  let n := roundHalfEven (num * 10 ^ prec) den
  let s := toString n
  let s := padZerosLeft s (prec + 1)
  let intPart := (s.take (s.length - prec)).toString
  let frac := (s.drop (s.length - prec)).toString
  if prec == 0 then intPart else intPart ++ "." ++ frac

/-- Scientific notation `d.ddd…e±XX` with `prec` decimals of `num / den` (`num > 0`). -/
def sciDigits (num den prec : Nat) (upper : Bool) : String :=
  let x0 := floorLog10 num den
  let scaled (x : Int) : Nat :=
    let k : Int := (prec : Int) - x
    if k ≥ 0 then roundHalfEven (num * 10 ^ k.toNat) den
    else roundHalfEven num (den * 10 ^ (-k).toNat)
  let n0 := scaled x0
  let (n, x) := if n0 ≥ 10 ^ (prec + 1) then (scaled (x0 + 1), x0 + 1) else (n0, x0)
  let s := toString n
  let mant := if prec == 0 then s else (s.take 1).toString ++ "." ++ (s.drop 1).toString
  let es := toString x.natAbs
  mant ++ (if upper then "E" else "e") ++ (if x < 0 then "-" else "+") ++
    (if es.length < 2 then "0" ++ es else es)

/-- Strip trailing zeros (and a trailing `.`) of the fractional part (for `%g`). -/
def stripFracZeros (s : String) : String :=
  if !s.contains '.' then s
  else
    let cs := (s.toList.reverse.dropWhile (· == '0'))
    let cs := match cs with | '.' :: rest => rest | other => other
    String.ofList cs.reverse

/-- Apply sign, width and padding. `body` excludes the sign; `prefixLen` digits of `body` are a
radix prefix (`0x`) that zero padding must follow. -/
def pad (sp : Spec) (sign : String) (body : String) (numeric : Bool) (prefixLen : Nat := 0) : String :=
  let total := sign.length + body.length
  if total ≥ sp.width then sign ++ body
  else
    let fill := sp.width - total
    if sp.leftAlign then sign ++ body ++ String.ofList (List.replicate fill ' ')
    else if sp.zeroPad && numeric then
      sign ++ (body.take prefixLen).toString ++ String.ofList (List.replicate fill '0') ++ (body.drop prefixLen).toString
    else String.ofList (List.replicate fill ' ') ++ sign ++ body

/-- `%d` / `%i` on a signed 64-bit value. -/
def fmtSigned (sp : Spec) (v : Int) : String :=
  let sign := if v < 0 then "-" else if sp.space then " " else ""
  pad sp sign (toString v.natAbs) true

/-- `%u %o %x %X` on an unsigned value. -/
def fmtUnsigned (sp : Spec) (spec : Char) (v : Nat) : String :=
  let base := if spec == 'o' then 8 else if spec == 'u' then 10 else 16
  let digits := String.ofList ((Nat.toDigits base v).map fun c => if spec == 'X' then c.toUpper else c)
  if spec == 'o' && sp.alt && !digits.startsWith "0" then pad sp "" ("0" ++ digits) true
  else if (spec == 'x' || spec == 'X') && sp.alt && v != 0 then
    pad sp "" ((if spec == 'X' then "0X" else "0x") ++ digits) true 2
  else pad sp "" digits true

/-- `%f %F %e %E %g %G %a %A` on an IEEE double. -/
def fmtDouble (sp : Spec) (spec : Char) (x : IEEEFloat FloatFormat.double) : String :=
  let upper := spec == 'F' || spec == 'E' || spec == 'G' || spec == 'A'
  let sign := if x.sign then "-" else if sp.space then " " else ""
  let up (s : String) := if upper then s.toUpper else s
  if x.isNaN then pad sp sign (up "nan") false
  else if x.isInf then pad sp sign (up "inf") false
  else
    let (_, m, e) := if x.isZero then (x.sign, 0, (0 : Int)) else x.toDyadic
    let (num, den) : Nat × Nat := if e ≥ 0 then (m * 2 ^ e.toNat, 1) else (m, 2 ^ (-e).toNat)
    match spec with
    | 'f' | 'F' =>
      let s := fixedDigits num den 6
      pad sp sign (if sp.alt && !s.contains '.' then s ++ "." else s) true
    | 'e' | 'E' =>
      let s := if num == 0 then "0.000000" ++ (if upper then "E+00" else "e+00") else sciDigits num den 6 upper
      pad sp sign s true
    | 'g' | 'G' =>
      let p : Nat := 6
      let s :=
        if num == 0 then (if sp.alt then "0.00000" else "0")
        else
          -- exponent after rounding to p significant digits
          let sci := sciDigits num den (p - 1) upper
          let xStr := (sci.splitOn (if upper then "E" else "e")).getD 1 "+00"
          let xv : Int := match (xStr.drop 1).toString.toNat? with
            | some n => if xStr.startsWith "-" then -(n : Int) else n
            | none => 0
          if xv < (p : Int) && xv ≥ -4 then
            let r := fixedDigits num den (p - 1 - xv).toNat
            if sp.alt then r else stripFracZeros r
          else
            if sp.alt then sci
            else
              match sci.splitOn (if upper then "E" else "e") with
              | [mant, ex] => stripFracZeros mant ++ (if upper then "E" else "e") ++ ex
              | _ => sci
      pad sp sign s true
    | _ =>
      -- `%a` / `%A`
      let pfx := if upper then "0X" else "0x"
      let body :=
        if x.isZero then "0" ++ (if sp.alt then "." else "") ++ "p+0"
        else
          let (lead, sig, ex) : Nat × Nat × Int :=
            if x.rawExp == 0 then (0, x.rawSig, -1022) else (1, x.rawSig, (x.rawExp : Int) - 1023)
          let hex := padZerosLeft (String.ofList (Nat.toDigits 16 sig)) 13
          let hex := String.ofList (hex.toList.reverse.dropWhile (· == '0')).reverse
          toString lead ++ (if hex.isEmpty && !sp.alt then "" else "." ++ hex) ++
            "p" ++ (if ex < 0 then "-" else "+") ++ toString ex.natAbs
      pad sp sign (pfx ++ up body) true 2

end LeanNanoLlvm.CFormat
