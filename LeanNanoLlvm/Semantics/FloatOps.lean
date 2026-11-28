import LeanNanoLlvm.Util.Poison
import LeanNanoLlvm.Util.Config
import LeanNanoLlvm.Util.IEEEFloat
import LeanNanoLlvm.Util.Oracle
import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.Tactic

namespace LeanNanoLlvm.Semantics

open AST

/-- Poison-aware IEEE floating-point value of a specific LLVM `FloatType`. -/
abbrev FloatW (ft : FloatType) := PoisonOr (IEEEFloat ft.format)

/-- The denormal mode for values of format `fmt`: the `float:` override (`denormalModeF32`) for
32-bit floats (the only type of format `single`), the function's mode otherwise. -/
@[simp] def _root_.LeanNanoLlvm.SemanticsConfig.denormalModeFmt (cfg : SemanticsConfig) (fmt : FloatFormat) : DenormalMode :=
  match cfg.denormalModeF32 with
  | some m => if fmt == FloatFormat.single then m else cfg.denormalMode
  | none => cfg.denormalMode

/-- Flush subnormal floats according to `DenormalModeKind` (matches `llubi::handleDenormal`). -/

def handleDenormal {fmt : FloatFormat} (mode : DenormalModeKind) (isInput : Bool)
    (preserveInputChoice : Bool) (x : IEEEFloat fmt) : IEEEFloat fmt :=
  if !x.isSubnormal then x
  else if isInput && preserveInputChoice then x
  else match mode with
    | .positiveZero => IEEEFloat.zero fmt false
    | .preserveSign => IEEEFloat.zero fmt x.sign
    | .ieee         => x

/-- Apply Fast-Math Flags (`nnan`, `ninf`, `nsz`) to a scalar float (matches `llubi::handleFMFFlags`). -/
def handleFMF {fmt : FloatFormat} (fmf : FastMathFlags) (isInput : Bool)
    (flipZeroSign : Bool) (x : IEEEFloat fmt) : PoisonOr (IEEEFloat fmt) :=
  if fmf.nnan && x.isNaN then .poison
  else if fmf.ninf && x.isInf then .poison
  else if isInput && fmf.nsz && x.isZero then
    .value (IEEEFloat.zero fmt (x.sign != flipZeroSign))
  else
    .value x

/-- Unpack a 128-bit `ppc_fp128` (`lo64 || hi64` in LLVM APInt order) into `(hi, lo)` IEEE doubles. -/
def unpackPPC128 (x : IEEEFloat .fp128) : IEEEFloat .double × IEEEFloat .double :=
  let n := x.bits.toNat
  let hi := IEEEFloat.ofNatBits (fmt := .double) (n &&& ((1 <<< 64) - 1))
  let lo := IEEEFloat.ofNatBits (fmt := .double) (n >>> 64)
  (hi, lo)

/-- Pack `(hi, lo)` IEEE doubles into 128-bit `ppc_fp128` (`lo64 || hi64` in LLVM APInt order). -/
def packPPC128 (hi lo : IEEEFloat .double) : IEEEFloat .fp128 :=
  IEEEFloat.ofNatBits (fmt := .fp128) ((lo.bits.toNat <<< 64) ||| hi.bits.toNat)

/-- The value of a `ppc_fp128` (a pair of doubles, `hi + lo`) as an IEEE binary128: exact, since
both doubles and their sum fit binary128's 113-bit significand. -/
def ppcToQuad (x : IEEEFloat .fp128) : IEEEFloat .fp128 :=
  let (hi, lo) := unpackPPC128 x
  if !hi.isFinite then hi.convert .fp128 .RNE
  else IEEEFloat.add .RNE (hi.convert .fp128 .RNE) (lo.convert .fp128 .RNE)

/-- A binary128 value as a `ppc_fp128`: `hi` is the value rounded to double (with `rm`), `lo` the
remainder rounded to double (LLVM `APFloat` double-double layout). -/
def quadToPPC (rm : RoundingMode) (q : IEEEFloat .fp128) (loSignOfHi : Bool := false) :
    IEEEFloat .fp128 :=
  IEEEFloat.quadToDoubleDouble rm q loSignOfHi

/-- `llvm.fabs` on a stored float of type `ft`. A `ppc_fp128` is negative when its high double
is, and changing its sign flips both doubles (`DoubleAPFloat::clearSign`/`changeSign`). -/
def floatAbs {ft : FloatType} (x : IEEEFloat ft.format) : IEEEFloat ft.format :=
  match ft, x with
  | .ppc_fp128, x =>
    let (hi, lo) := unpackPPC128 x
    if hi.sign then packPPC128 hi.neg lo.neg else x
  | _, x => x.abs

/-- `llvm.copysign` on stored floats of type `ft` (`ppc_fp128`: the sign of the high double; a
sign change flips both doubles, as `DoubleAPFloat::copySign` does). -/
def floatCopySign {ft : FloatType} (mag sgn : IEEEFloat ft.format) : IEEEFloat ft.format :=
  match ft, mag, sgn with
  | .ppc_fp128, m, s =>
    let (hi, lo) := unpackPPC128 m
    if hi.sign != (unpackPPC128 s).1.sign then packPPC128 hi.neg lo.neg else m
  | _, m, s => m.copySign s

/-- The IEEE value a stored float of type `ft` denotes (`ppc_fp128` is stored as its double pair). -/
def toSemantic {ft : FloatType} (x : IEEEFloat ft.format) : IEEEFloat ft.format :=
  match ft, x with
  | .ppc_fp128, x => ppcToQuad x
  | _, x => x

/-- The stored form of an IEEE value of type `ft` (inverse of `toSemantic`). -/
def fromSemantic {ft : FloatType} (rm : RoundingMode) (x : IEEEFloat ft.format)
    (loSignOfHi : Bool := false) : IEEEFloat ft.format :=
  match ft, x with
  | .ppc_fp128, x => quadToPPC rm x loSignOfHi
  | _, x => x

private def ppcAdd (rm : RoundingMode) (a aa c cc : IEEEFloat .double) :
    IEEEFloat .double × IEEEFloat .double :=
  let z := IEEEFloat.add rm a c
  if !z.isFinite then (z, IEEEFloat.zero .double false)
  else
    let q := IEEEFloat.sub rm a z
    let qz := IEEEFloat.add rm q z
    let qza := (IEEEFloat.sub rm qz a).neg
    let zz := IEEEFloat.add rm (IEEEFloat.add rm (IEEEFloat.add rm (IEEEFloat.add rm q c) qza) aa) cc
    if zz.isZero && !zz.sign then (z, IEEEFloat.zero .double false)
    else
      let hi := IEEEFloat.add rm z zz
      if !hi.isFinite then (hi, IEEEFloat.zero .double false)
      else
        let lo := IEEEFloat.add rm (IEEEFloat.sub rm z hi) zz
        (hi, lo)

private def ppcMul (rm : RoundingMode) (a aa c cc : IEEEFloat .double) :
    IEEEFloat .double × IEEEFloat .double :=
  let p := IEEEFloat.mul rm a c
  if !p.isFinite then (p, IEEEFloat.zero .double false)
  else
    let err := IEEEFloat.fma rm a c p.neg
    let t := IEEEFloat.add rm err (IEEEFloat.add rm (IEEEFloat.mul rm a cc) (IEEEFloat.mul rm aa c))
    let hi := IEEEFloat.add rm p t
    if !hi.isFinite then (hi, IEEEFloat.zero .double false)
    else
      let lo := IEEEFloat.add rm (IEEEFloat.sub rm p hi) t
      (hi, lo)

/-- LLVM's `semPPCDoubleDoubleLegacy`: an IEEE-style format with a 106-bit significand and
double's exponent field, in which `APFloat` divides and takes remainders of `ppc_fp128` values
(`DoubleAPFloat::divide`/`mod` convert to it and back). Its normal range in LLVM ends at
2^-969 (`minExponent = -1022 + 53`), not 2^-1022 as in this format; see `ppcLegacyDiv`. -/
def ppcLegacyFormat : FloatFormat := { expBits := 11, sigBits := 105 }

/-- Division in LLVM's `semPPCDoubleDoubleLegacy`. That format's normal range ends at 2^-969, below
which its values are subnormal: multiples of 2^-1074. At exponent -969 its 106-bit precision has
the same quantum, so any quotient of magnitude below 2^-968 is rounded to a multiple of 2^-1074,
which `ppcLegacyFormat` (normal down to 2^-1022) would round more finely. Every multiple of
2^-1074 below 2^-968 is exact in `ppcLegacyFormat`, so the result is computed exactly there.
(Inputs need no such care: a double pair is a multiple of 2^-1074, and so is a remainder.) -/
def ppcLegacyDiv (rm : RoundingMode) (x y : IEEEFloat ppcLegacyFormat) : IEEEFloat ppcLegacyFormat :=
  let r := IEEEFloat.div rm x y
  -- special operands (NaN, infinity, zero) and overflow are as in `IEEEFloat.div`
  if !(x.isFinite && !x.isZero && y.isFinite && !y.isZero) || !r.isFinite then r
  -- |r| < 2^-968 ⇔ r's unbiased exponent < -968 (raw exponent < 1023 - 968 = 55, or subnormal)
  else if r.rawExp ≥ 55 then r
  else
    let (_, mx, ex) := x.toDyadic
    let (_, my, ey) := y.toDyadic
    let sign := x.sign != y.sign
    -- k = round(|x/y| / 2^-1074) = round(mx * 2^(ex - ey + 1074) / my)
    let sh : Int := ex - ey + 1074
    let (n, d) := if sh ≥ 0 then (mx <<< sh.toNat, my) else (mx, my <<< (-sh).toNat)
    let q := n / d
    let rem := n % d
    let up := if rem == 0 then false else match rm with
      | .RTZ => false
      | .RTP => !sign
      | .RTN => sign
      | .RNA => 2 * rem ≥ d
      | .RNE => 2 * rem > d || (2 * rem == d && q % 2 == 1)
    let k := if up then q + 1 else q
    -- k * 2^-1074, exact in `ppcLegacyFormat`
    IEEEFloat.roundExact ppcLegacyFormat rm sign k 1 (-1074)

/-- A `ppc_fp128` operation as `APFloat` performs it in `ppcLegacyFormat`: both pairs rounded to
106 bits, the operation, then the result split back into a double pair (high double rounded to
nearest, low double the remainder). -/
private def ppcViaLegacy (f : IEEEFloat ppcLegacyFormat → IEEEFloat ppcLegacyFormat → IEEEFloat ppcLegacyFormat)
    (a aa c cc : IEEEFloat .double) : IEEEFloat .double × IEEEFloat .double :=
  let toL (h l : IEEEFloat .double) : IEEEFloat ppcLegacyFormat :=
    (ppcToQuad (packPPC128 h l)).convert ppcLegacyFormat .RNE
  let r := f (toL a aa) (toL c cc)
  unpackPPC128 (IEEEFloat.quadToDoubleDouble .RNE (r.convert .fp128 .RNE))

/-- Evaluate LLVM `fcmp` predicate on two non-poison floats (matches `llvm::FCmpInst::compare`). -/
def evalFCmpPred {fmt : FloatFormat} (pred : FCmpPred) (x y : IEEEFloat fmt) : Bool :=
  let unordered := x.isNaN || y.isNaN
  match pred with
  | .ffalse => false
  | .ftrue  => true
  | .ord    => !unordered
  | .uno    => unordered
  | .oeq    => !unordered && IEEEFloat.compareNonNaN x y == .eq
  | .ogt    => !unordered && IEEEFloat.compareNonNaN x y == .gt
  | .oge    => !unordered && IEEEFloat.compareNonNaN x y != .lt
  | .olt    => !unordered && IEEEFloat.compareNonNaN x y == .lt
  | .ole    => !unordered && IEEEFloat.compareNonNaN x y != .gt
  | .one    => !unordered && IEEEFloat.compareNonNaN x y != .eq
  | .ueq    => unordered || IEEEFloat.compareNonNaN x y == .eq
  | .ugt    => unordered || IEEEFloat.compareNonNaN x y == .gt
  | .uge    => unordered || IEEEFloat.compareNonNaN x y != .lt
  | .ult    => unordered || IEEEFloat.compareNonNaN x y == .lt
  | .ule    => unordered || IEEEFloat.compareNonNaN x y != .gt
  | .une    => unordered || IEEEFloat.compareNonNaN x y != .eq

/-- Evaluate `fcmp` with FMF and input denormal flushing. -/
def evalFCmp {ft : FloatType} (cfg : SemanticsConfig) (fmf : FastMathFlags)
    (pred : FCmpPred) (flipL flipR denormL denormR : Bool)
    (lhs rhs : FloatW ft) : PoisonOr (BitVec 1) := do
  let x ← lhs
  let y ← rhs
  match ft, x, y with
  | .ppc_fp128, x, y =>
    let (a, aa) := unpackPPC128 x
    let (c, cc) := unpackPPC128 y
    let a ← handleFMF fmf true flipL a
    let c ← handleFMF fmf true flipR c
    let unordered := a.isNaN || c.isNaN
    let cmpOrd : Ordering :=
      match IEEEFloat.compareNonNaN a c with
      | .eq => IEEEFloat.compareNonNaN aa cc
      | other => other
    let b : Bool := match pred with
      | .ffalse => false
      | .ftrue  => true
      | .ord    => !unordered
      | .uno    => unordered
      | .oeq    => !unordered && cmpOrd == .eq
      | .ogt    => !unordered && cmpOrd == .gt
      | .oge    => !unordered && cmpOrd != .lt
      | .olt    => !unordered && cmpOrd == .lt
      | .ole    => !unordered && cmpOrd != .gt
      | .one    => !unordered && cmpOrd != .eq
      | .ueq    => unordered || cmpOrd == .eq
      | .ugt    => unordered || cmpOrd == .gt
      | .uge    => unordered || cmpOrd != .lt
      | .ult    => unordered || cmpOrd == .lt
      | .ule    => unordered || cmpOrd != .gt
      | .une    => unordered || cmpOrd != .eq
    pure (BitVec.ofBool b)
  | _, x, y =>
    let x ← handleFMF fmf true flipL x
    let y ← handleFMF fmf true flipR y
    let fx := handleDenormal (cfg.denormalModeFmt ft.format).input true denormL x
    let fy := handleDenormal (cfg.denormalModeFmt ft.format).input true denormR y
    pure (BitVec.ofBool (evalFCmpPred pred fx fy))

/-- Evaluate `fptoui` / `fptosi` (truncates toward zero, poison on NaN/Inf/out-of-range). -/
def evalFPToInt {ft : FloatType} (dstW : Nat) (isSigned : Bool)
    (v : FloatW ft) : PoisonOr (BitVec dstW) := do
  let x ← v
  let x := toSemantic x
  let res? := if isSigned then x.toSignedBitVec? dstW else x.toUnsignedBitVec? dstW
  match res? with
  | some bv => .value bv
  | none => .poison

/-! ### Lazily drawn nondeterministic choices (in `llubi`'s order)

The executable evaluators below draw from the oracle only when a choice actually exists and in
the order `llubi` consumes its random generator, so that a seeded `std::mt19937_64` stream
reproduces `llubi` exactly. The relational semantics quantifies over all oracles (`∃ o`), so the
set of allowed behaviours is unchanged: every choice still ranges over all its possibilities. -/

/-- Input fast-math flags (`handleFMFFlags(.., IsInput=true)`): `nnan`/`ninf` produce poison and
`nsz` picks the sign of a zero (one draw, only for zeros). -/
def fmfIn {fmt : FloatFormat} (fmf : FastMathFlags) (x : IEEEFloat fmt) (o : OracleState) :
    PoisonOr (IEEEFloat fmt) × OracleState :=
  if fmf.nnan && x.isNaN then (.poison, o)
  else if fmf.ninf && x.isInf then (.poison, o)
  else if fmf.nsz && x.isZero then
    match o.nextBool with
    | (b, o') => (.value (IEEEFloat.zero fmt (x.sign != b)), o')
  else (.value x, o)

/-- Input denormal handling (`handleDenormal(.., IsInput=true)`): a subnormal input is either kept
or flushed per `mode` (one draw, only for subnormals). -/
def denormIn {fmt : FloatFormat} (mode : DenormalModeKind) (x : IEEEFloat fmt) (o : OracleState) :
    IEEEFloat fmt × OracleState :=
  if !x.isSubnormal then (x, o)
  else
    match o.nextBool with
    | (keep, o') => (handleDenormal mode true keep x, o')

/-- Append `c` unless a bitwise-identical candidate is present (`addNaNCandidate`). -/
def pushNaNCandidate {fmt : FloatFormat} (acc : List (IEEEFloat fmt)) (c : IEEEFloat fmt) :
    List (IEEEFloat fmt) :=
  if acc.any (fun a => a.bits == c.bits) then acc else acc ++ [c]

/-- `llubi`'s `applyNaNPropagation`: for a NaN result, draw the sign, build the candidate set of
the NaN mode (deduplicated, in `llubi`'s order) and pick one (one draw) when there is a choice. -/
def nanPropagate {fmt : FloatFormat} (mode : NaNPropagationMode) (res : IEEEFloat fmt)
    (inputs : List (IEEEFloat fmt)) (o : OracleState) : IEEEFloat fmt × OracleState :=
  if !res.isNaN then (res, o)
  else
    match o.nextBool with
    | (sign, o1) =>
      let preferred := IEEEFloat.qNaN fmt sign 0
      let prop (quiet : Bool) : List (IEEEFloat fmt) :=
        (inputs.filter IEEEFloat.isNaN).map fun n =>
          let n' := if sign then n.neg else n
          if quiet && n'.isSNaN then n'.makeQuiet else n'
      let dedup (cs : List (IEEEFloat fmt)) : List (IEEEFloat fmt) :=
        cs.foldl pushNaNCandidate []
      let pick (cands : List (IEEEFloat fmt)) (o0 : OracleState) : IEEEFloat fmt × OracleState :=
        match cands with
        | [] => (preferred, o0)
        | _ =>
          match o0.nextNat with
          | (k, o') => (cands.getD (k % cands.length) preferred, o')
      match mode with
      | .preferred => (preferred, o1)
      | .quieting => pick (dedup (prop true)) o1
      | .unchanged => pick (dedup (prop false)) o1
      | .nondet => pick (dedup (preferred :: (prop true ++ prop false))) o1
      | .sparcPreferred => pick [IEEEFloat.qNaN fmt sign fmt.sigMask] o1
      | .wasm =>
        if inputs.any (fun n => n.isNaN && (n.isSNaN || n.rawSig != fmt.quietBit)) then
          match o1.nextBitVec fmt.sigBits with
          | (payload, o2) => pick [IEEEFloat.qNaN fmt sign payload.toNat] o2
        else (preferred, o1)

/-- Scalar `fneg` with lazily drawn choices. -/
def evalFloatUnaryOp {ft : FloatType} (op : FloatUnaryOp) (v : FloatW ft) (o : OracleState) :
    FloatW ft × OracleState :=
  match v with
  | .poison => (.poison, o)
  | .value x =>
    match op with
    | .fneg fmf =>
      match ft with
      | .ppc_fp128 =>
        let (hi, lo) := unpackPPC128 x
        match fmfIn fmf hi o with
        | (.poison, o1) => (.poison, o1)
        | (.value hi', o1) =>
          (match handleFMF fmf false false hi'.neg with
            | .poison => .poison
            | .value h => .value (packPPC128 h lo.neg), o1)
      | _ =>
        let rx := fmfIn fmf x o
        match rx.1 with
        | .poison => (.poison, rx.2)
        | .value x' => (handleFMF fmf false false x'.neg, rx.2)

@[simp] theorem fmfIn_none {fmt : FloatFormat} (x : IEEEFloat fmt) (o : OracleState) :
    fmfIn {} x o = (.value x, o) := by
  simp [fmfIn]

@[simp] theorem denormIn_ieee_fst {fmt : FloatFormat} (x : IEEEFloat fmt) (o : OracleState) :
    (denormIn .ieee x o).1 = x := by
  unfold denormIn
  split
  · rfl
  · show handleDenormal .ieee true (o.oracle o.index % 2 == 1) x = x
    unfold handleDenormal
    split
    · rfl
    · split <;> rfl

@[simp] theorem nanPropagate_not_nan {fmt : FloatFormat} (m : NaNPropagationMode) (r : IEEEFloat fmt)
    (ins : List (IEEEFloat fmt)) (o : OracleState) (h : r.isNaN = false) :
    nanPropagate m r ins o = (r, o) := by
  unfold nanPropagate
  simp only [h, Bool.not_false, ↓reduceIte]

/-- Scalar FP binary op with lazily drawn choices (order of `llubi`'s `visitFPBinOpWithResult`). -/
def evalFloatBinaryOp {ft : FloatType} (cfg : SemanticsConfig) (op : FloatBinaryOp)
    (lhs rhs : FloatW ft) (o : OracleState) : FloatW ft × OracleState :=
  let fmf := match op with
    | .fadd f | .fsub f | .fmul f | .fdiv f | .frem f => f
  match lhs, rhs with
  | .value x, .value y =>
    match ft with
    | .ppc_fp128 =>
      let (a, aa) := unpackPPC128 x
      let (c, cc) := unpackPPC128 y
      match fmfIn fmf a o with
      | (va, o1) =>
        match fmfIn fmf c o1 with
        | (vc, o2) =>
          match va, vc with
          | .value a, .value c =>
            let (rHi, rLo) := match op with
              | .fadd _ => ppcAdd cfg.roundingMode a aa c cc
              | .fsub _ =>
                let (h, l) := ppcAdd cfg.roundingMode a aa c.neg cc.neg
                (h, if l.isZero && !l.sign && aa.isZero && cc.isZero && !a.isZero && !c.isZero then l.neg else l)
              | .fmul _ => ppcMul cfg.roundingMode a aa c cc
              | .fdiv _ => ppcViaLegacy (ppcLegacyDiv cfg.roundingMode) a aa c cc
              | .frem _ => ppcViaLegacy IEEEFloat.rem a aa c cc
            match handleFMF fmf false false rHi with
            | .poison => (.poison, o2)
            | .value rHi =>
              match nanPropagate cfg.nanMode rHi [a, c] o2 with
              | (r, o3) => (.value (packPPC128 r rLo), o3)
          | _, _ => (.poison, o2)
    | _ =>
      let rx := fmfIn fmf x o
      let ry := fmfIn fmf y rx.2
      match rx.1, ry.1 with
      | .value x', .value y' =>
        let dx := denormIn (cfg.denormalModeFmt ft.format).input x' ry.2
        let dy := denormIn (cfg.denormalModeFmt ft.format).input y' dx.2
        let raw := match op with
          | .fadd _ => IEEEFloat.add cfg.roundingMode dx.1 dy.1
          | .fsub _ => IEEEFloat.sub cfg.roundingMode dx.1 dy.1
          | .fmul _ => IEEEFloat.mul cfg.roundingMode dx.1 dy.1
          | .fdiv _ => IEEEFloat.div cfg.roundingMode dx.1 dy.1
          | .frem _ => IEEEFloat.rem dx.1 dy.1
        let flushed := handleDenormal (cfg.denormalModeFmt ft.format).output false false raw
        match handleFMF fmf false false flushed with
        | .poison => (.poison, dy.2)
        | .value r =>
          let np := nanPropagate cfg.nanMode r [dx.1, dy.1] dy.2
          (.value np.1, np.2)
      | _, _ => (.poison, ry.2)
  | _, _ => (.poison, o)

/-- Scalar `fcmp` with lazily drawn choices (`llubi`'s `visitFCmpInst`: the `nsz` draws are made on
both operands, then the denormal draws on the original operands). -/
def evalFCmpO {ft : FloatType} (cfg : SemanticsConfig) (fmf : FastMathFlags) (pred : FCmpPred)
    (lhs rhs : FloatW ft) (o : OracleState) : PoisonOr (BitVec 1) × OracleState :=
  match lhs, rhs with
  | .value x, .value y =>
    match fmfIn fmf x o with
    | (.poison, o1) => (.poison, o1)
    | (.value _, o1) =>
      match fmfIn fmf y o1 with
      | (.poison, o2) => (.poison, o2)
      | (.value _, o2) =>
        match ft with
        | .ppc_fp128 =>
          (evalFCmp (ft := .ppc_fp128) cfg {} pred false false false false (.value x) (.value y), o2)
        | _ =>
          match denormIn (cfg.denormalModeFmt ft.format).input x o2 with
          | (fx, o3) =>
            match denormIn (cfg.denormalModeFmt ft.format).input y o3 with
            | (fy, o4) => (.value (BitVec.ofBool (evalFCmpPred pred fx fy)), o4)
  | _, _ => (.poison, o)

/-- Scalar `fpext`/`fptrunc` with lazily drawn choices (`llubi`'s `visitFPConvInst`). -/
def evalFPConv {srcFt : FloatType} (dstFt : FloatType) (cfg : SemanticsConfig)
    (fmf : FastMathFlags) (v : FloatW srcFt) (o : OracleState) : FloatW dstFt × OracleState :=
  match v with
  | .poison => (.poison, o)
  | .value x =>
    match fmfIn fmf x o with
    | (.poison, o1) => (.poison, o1)
    | (.value x', o1) =>
      match denormIn (cfg.denormalModeFmt srcFt.format).input x' o1 with
      | (fx, o2) =>
        let conv : IEEEFloat dstFt.format :=
          fromSemantic (ft := dstFt) cfg.roundingMode ((toSemantic (ft := srcFt) fx).convert dstFt.format cfg.roundingMode)
        match handleFMF fmf false false conv with
        | .poison => (.poison, o2)
        | .value c =>
          let flushed := handleDenormal (cfg.denormalModeFmt dstFt.format).output false false c
          let inputs := if fx.isNaN then [conv] else []
          match nanPropagate cfg.nanMode flushed inputs o2 with
          | (r, o3) => (.value r, o3)

/-- `uitofp`/`sitofp` with a lazily drawn `nsz` sign choice for a zero result. -/
def evalIntToFP {srcW : Nat} (dstFt : FloatType) (cfg : SemanticsConfig)
    (isSigned nneg : Bool) (fmf : FastMathFlags) (v : PoisonOr (BitVec srcW)) (o : OracleState) :
    FloatW dstFt × OracleState :=
  match v with
  | .poison => (.poison, o)
  | .value x =>
    if !isSigned && nneg && x.msb then (.poison, o)
    else
      let res := fromSemantic (ft := dstFt) cfg.roundingMode (if isSigned
        then IEEEFloat.ofSignedBitVec dstFt.format cfg.roundingMode x
        else IEEEFloat.ofUnsignedBitVec dstFt.format cfg.roundingMode x) (loSignOfHi := true)
      fmfIn fmf res o

/-- IEEE-754 2008 `maxNum`/`minNum` (`APFloat::maxnum`/`minnum`): an sNaN operand yields a qNaN. -/
def maxnum2008 {fmt : FloatFormat} (isMax : Bool) (a b : IEEEFloat fmt) : IEEEFloat fmt :=
  if a.isSNaN then a.makeQuiet
  else if b.isSNaN then b.makeQuiet
  else if a.isNaN then b
  else if b.isNaN then a
  else if a.isZero && b.isZero && a.sign != b.sign then
    if isMax then (if a.sign then b else a) else (if a.sign then a else b)
  else
    match IEEEFloat.compareNonNaN a b with
    | .lt => if isMax then b else a
    | .gt => if isMax then a else b
    | .eq => if isMax then a else b

/-- Kinds of FP min/max operations (`llubi`'s `applyFPMinMax`). -/
inductive FPMinMaxKind where
  | maximum | minimum | maximumnum | minimumnum | maxnum | minnum
deriving DecidableEq, Repr

/-- `llubi`'s `applyFPMinMax`: `nsz` picks between zeros of different signs (one draw); for
`maxnum`/`minnum` each sNaN operand may be quieted first (one draw per sNaN). -/
def applyFPMinMaxO {fmt : FloatFormat} (k : FPMinMaxKind) (nsz : Bool) (a b : IEEEFloat fmt)
    (o : OracleState) : IEEEFloat fmt × OracleState :=
  if nsz && a.isZero && b.isZero && a.sign != b.sign then
    match o.nextBool with
    | (pickA, o') => (if pickA then a else b, o')
  else
    match k with
    | .maximum => (IEEEFloat.maximum a b, o)
    | .minimum => (IEEEFloat.minimum a b, o)
    | .maximumnum => (IEEEFloat.maximumnum a b, o)
    | .minimumnum => (IEEEFloat.minimumnum a b, o)
    | .maxnum | .minnum =>
      match o.boolIf a.isSNaN with
      | (qa, o1) =>
        match o1.boolIf b.isSNaN with
        | (qb, o2) =>
          let a' := if qa then a.makeQuiet else a
          let b' := if qb then b.makeQuiet else b
          (maxnum2008 (k == .maxnum) a' b', o2)

end LeanNanoLlvm.Semantics
