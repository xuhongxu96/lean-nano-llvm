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

/-- Apply NaN propagation mode (matches `llubi::applyNaNPropagation`). -/
def applyNaNPropagation {fmt : FloatFormat} (mode : NaNPropagationMode)
    (res : IEEEFloat fmt) (inputs : List (IEEEFloat fmt))
    (signChoice : Bool) (pickIdx : Nat) : IEEEFloat fmt :=
  if !res.isNaN then res
  else
    let preferred := IEEEFloat.qNaN fmt signChoice 0
    let inputNaNs := inputs.filter IEEEFloat.isNaN
    let quietCandidates := inputNaNs.map fun n =>
      let n' := if signChoice then n.neg else n
      n'.makeQuiet
    let unchangedCandidates := inputNaNs.map fun n =>
      if signChoice then n.neg else n
    let pick (cands : List (IEEEFloat fmt)) : IEEEFloat fmt :=
      match cands with
      | [] => preferred
      | _ => cands.getD (pickIdx % cands.length) preferred
    match mode with
    | .preferred      => preferred
    | .quieting       => pick quietCandidates
    | .unchanged      => pick unchangedCandidates
    | .nondet         => pick (preferred :: quietCandidates ++ unchangedCandidates)
    | .sparcPreferred => IEEEFloat.qNaN fmt signChoice fmt.sigMask
    | .wasm =>
      if inputNaNs.all (fun n => n.isQNaN && n.rawSig == fmt.quietBit) then
        IEEEFloat.qNaN fmt signChoice 0
      else
        IEEEFloat.qNaN fmt signChoice ((pickIdx ||| 1) &&& fmt.sigMask)

/-- Unpack a 128-bit `ppc_fp128` (`lo64 || hi64` in LLVM APInt order) into `(hi, lo)` IEEE doubles. -/
def unpackPPC128 (x : IEEEFloat .fp128) : IEEEFloat .double × IEEEFloat .double :=
  let n := x.bits.toNat
  let hi := IEEEFloat.ofNatBits (fmt := .double) (n &&& ((1 <<< 64) - 1))
  let lo := IEEEFloat.ofNatBits (fmt := .double) (n >>> 64)
  (hi, lo)

/-- Pack `(hi, lo)` IEEE doubles into 128-bit `ppc_fp128` (`lo64 || hi64` in LLVM APInt order). -/
def packPPC128 (hi lo : IEEEFloat .double) : IEEEFloat .fp128 :=
  IEEEFloat.ofNatBits (fmt := .fp128) ((lo.bits.toNat <<< 64) ||| hi.bits.toNat)

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

private def ppcDiv (rm : RoundingMode) (a aa c cc : IEEEFloat .double) :
    IEEEFloat .double × IEEEFloat .double :=
  let q1 := IEEEFloat.div rm a c
  if !q1.isFinite then (q1, IEEEFloat.zero .double false)
  else
    let (p1, p2) := ppcMul rm q1 (IEEEFloat.zero .double false) c cc
    let (r1, _) := ppcAdd rm a aa p1.neg p2.neg
    let q2 := IEEEFloat.div rm r1 c
    let hi := IEEEFloat.add rm q1 q2
    if !hi.isFinite then (hi, IEEEFloat.zero .double false)
    else
      let lo := IEEEFloat.add rm (IEEEFloat.sub rm q1 hi) q2
      (hi, lo)

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

/-- Evaluate bitwise unary FP op (`fneg`) with FMF (no denormal flushing, matches `llubi`). -/
def evalFloatUnaryOp {ft : FloatType} (op : FloatUnaryOp)
    (flipZero : Bool) (v : FloatW ft) : FloatW ft := do
  let x ← v
  match ft, x with
  | .ppc_fp128, x =>
    match op with
    | .fneg fmf =>
      let (hi, lo) := unpackPPC128 x
      let hi ← handleFMF fmf true flipZero hi
      let rHi := hi.neg
      let rLo := lo.neg
      let rHi ← handleFMF fmf false false rHi
      pure (packPPC128 rHi rLo)
  | ft, x =>
    match op with
    | .fneg fmf =>
      let x ← handleFMF fmf true flipZero x
      let r := x.neg
      handleFMF fmf false false r

/-- Evaluate binary FP op (`fadd`/`fsub`/`fmul`/`fdiv`/`frem`) with FMF, denormals, rounding, and NaN propagation. -/
def evalFloatBinaryOp {ft : FloatType} (cfg : SemanticsConfig) (op : FloatBinaryOp)
    (flipL flipR denormL denormR nanSign : Bool) (nanPick : Nat)
    (lhs rhs : FloatW ft) : FloatW ft := do
  let x ← lhs
  let y ← rhs
  let fmf := match op with
    | .fadd f | .fsub f | .fmul f | .fdiv f | .frem f => f
  match ft, x, y with
  | .ppc_fp128, x, y =>
    let (a, aa) := unpackPPC128 x
    let (c, cc) := unpackPPC128 y
    let a ← handleFMF fmf true flipL a
    let c ← handleFMF fmf true flipR c
    let (rHi, rLo) := match op with
      | .fadd _ => ppcAdd cfg.roundingMode a aa c cc
      | .fsub _ =>
        let (h, l) := ppcAdd cfg.roundingMode a aa c.neg cc.neg
        -- Match LLVM DoubleAPFloat::subtract zero-lo sign when subtracting exact doubles
        (h, if l.isZero && !l.sign && aa.isZero && cc.isZero && !a.isZero && !c.isZero then l.neg else l)
      | .fmul _ => ppcMul cfg.roundingMode a aa c cc
      | .fdiv _ => ppcDiv cfg.roundingMode a aa c cc
      | .frem _ => (IEEEFloat.rem a c, IEEEFloat.zero .double false)
    let rHi ← handleFMF fmf false false rHi
    let rHi := applyNaNPropagation cfg.nanMode rHi [a, c] nanSign nanPick
    pure (packPPC128 rHi rLo)
  | ft, x, y =>
    let x ← handleFMF fmf true flipL x
    let y ← handleFMF fmf true flipR y
    let fx := handleDenormal cfg.denormalMode.input true denormL x
    let fy := handleDenormal cfg.denormalMode.input true denormR y
    let raw := match op with
      | .fadd _ => IEEEFloat.add cfg.roundingMode fx fy
      | .fsub _ => IEEEFloat.sub cfg.roundingMode fx fy
      | .fmul _ => IEEEFloat.mul cfg.roundingMode fx fy
      | .fdiv _ => IEEEFloat.div cfg.roundingMode fx fy
      | .frem _ => IEEEFloat.rem fx fy
    let flushed := handleDenormal cfg.denormalMode.output false false raw
    let validated ← handleFMF fmf false false flushed
    let final := applyNaNPropagation cfg.nanMode validated [fx, fy] nanSign nanPick
    pure final

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
  | ft, x, y =>
    let x ← handleFMF fmf true flipL x
    let y ← handleFMF fmf true flipR y
    let fx := handleDenormal cfg.denormalMode.input true denormL x
    let fy := handleDenormal cfg.denormalMode.input true denormR y
    pure (BitVec.ofBool (evalFCmpPred pred fx fy))

/-- Evaluate `fpext` / `fptrunc` with FMF, denormals, rounding, and NaN propagation. -/
def evalFPConv {srcFt : FloatType} (dstFt : FloatType) (cfg : SemanticsConfig)
    (fmf : FastMathFlags) (flipIn denormIn nanSign : Bool) (nanPick : Nat)
    (v : FloatW srcFt) : FloatW dstFt := do
  let x ← v
  let x ← handleFMF fmf true flipIn x
  let fx := handleDenormal cfg.denormalMode.input true denormIn x
  let conv := fx.convert dstFt.format cfg.roundingMode
  let validated ← handleFMF fmf false false conv
  let flushed := handleDenormal cfg.denormalMode.output false false validated
  -- NaN propagation in destination format
  let inputConvNaNs := if fx.isNaN then [conv] else []
  pure (applyNaNPropagation cfg.nanMode flushed inputConvNaNs nanSign nanPick)

/-- Evaluate `fptoui` / `fptosi` (truncates toward zero, poison on NaN/Inf/out-of-range). -/
def evalFPToInt {ft : FloatType} (dstW : Nat) (isSigned : Bool)
    (v : FloatW ft) : PoisonOr (BitVec dstW) := do
  let x ← v
  let res? := if isSigned then x.toSignedBitVec? dstW else x.toUnsignedBitVec? dstW
  match res? with
  | some bv => .value bv
  | none => .poison

/-- Evaluate `uitofp` / `sitofp` with `nneg` (for `uitofp`) and `FMF`. -/
def evalIntToFP {srcW : Nat} (dstFt : FloatType) (cfg : SemanticsConfig)
    (isSigned nneg : Bool) (fmf : FastMathFlags) (flipZero : Bool)
    (v : PoisonOr (BitVec srcW)) : FloatW dstFt := do
  let x ← v
  if !isSigned && nneg && x.msb then
    .poison
  else
    let res := if isSigned
      then IEEEFloat.ofSignedBitVec dstFt.format cfg.roundingMode x
      else IEEEFloat.ofUnsignedBitVec dstFt.format cfg.roundingMode x
    -- `nsz` applies to the output zero of int-to-fp (matches `llubi::visitIntToFPInst`)
    handleFMF fmf true flipZero res

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
def evalFloatUnaryOpO {ft : FloatType} (op : FloatUnaryOp) (v : FloatW ft) (o : OracleState) :
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
def evalFloatBinaryOpO {ft : FloatType} (cfg : SemanticsConfig) (op : FloatBinaryOp)
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
              | .fdiv _ => ppcDiv cfg.roundingMode a aa c cc
              | .frem _ => (IEEEFloat.rem a c, IEEEFloat.zero .double false)
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
        let dx := denormIn cfg.denormalMode.input x' ry.2
        let dy := denormIn cfg.denormalMode.input y' dx.2
        let raw := match op with
          | .fadd _ => IEEEFloat.add cfg.roundingMode dx.1 dy.1
          | .fsub _ => IEEEFloat.sub cfg.roundingMode dx.1 dy.1
          | .fmul _ => IEEEFloat.mul cfg.roundingMode dx.1 dy.1
          | .fdiv _ => IEEEFloat.div cfg.roundingMode dx.1 dy.1
          | .frem _ => IEEEFloat.rem dx.1 dy.1
        let flushed := handleDenormal cfg.denormalMode.output false false raw
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
          match denormIn cfg.denormalMode.input x o2 with
          | (fx, o3) =>
            match denormIn cfg.denormalMode.input y o3 with
            | (fy, o4) => (.value (BitVec.ofBool (evalFCmpPred pred fx fy)), o4)
  | _, _ => (.poison, o)

/-- Scalar `fpext`/`fptrunc` with lazily drawn choices (`llubi`'s `visitFPConvInst`). -/
def evalFPConvO {srcFt : FloatType} (dstFt : FloatType) (cfg : SemanticsConfig)
    (fmf : FastMathFlags) (v : FloatW srcFt) (o : OracleState) : FloatW dstFt × OracleState :=
  match v with
  | .poison => (.poison, o)
  | .value x =>
    match fmfIn fmf x o with
    | (.poison, o1) => (.poison, o1)
    | (.value x', o1) =>
      match denormIn cfg.denormalMode.input x' o1 with
      | (fx, o2) =>
        let conv := fx.convert dstFt.format cfg.roundingMode
        match handleFMF fmf false false conv with
        | .poison => (.poison, o2)
        | .value c =>
          let flushed := handleDenormal cfg.denormalMode.output false false c
          let inputs := if fx.isNaN then [conv] else []
          match nanPropagate cfg.nanMode flushed inputs o2 with
          | (r, o3) => (.value r, o3)

/-- `uitofp`/`sitofp` with a lazily drawn `nsz` sign choice for a zero result. -/
def evalIntToFPO {srcW : Nat} (dstFt : FloatType) (cfg : SemanticsConfig)
    (isSigned nneg : Bool) (fmf : FastMathFlags) (v : PoisonOr (BitVec srcW)) (o : OracleState) :
    FloatW dstFt × OracleState :=
  match v with
  | .poison => (.poison, o)
  | .value x =>
    if !isSigned && nneg && x.msb then (.poison, o)
    else
      let res := if isSigned
        then IEEEFloat.ofSignedBitVec dstFt.format cfg.roundingMode x
        else IEEEFloat.ofUnsignedBitVec dstFt.format cfg.roundingMode x
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
