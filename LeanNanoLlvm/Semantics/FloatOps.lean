import LeanNanoLlvm.Util.Poison
import LeanNanoLlvm.Util.Config
import LeanNanoLlvm.Util.IEEEFloat
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

end LeanNanoLlvm.Semantics
