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
    | .preferred => preferred
    | .quieting  => pick quietCandidates
    | .unchanged => pick unchangedCandidates
    | .nondet    => pick (preferred :: quietCandidates ++ unchangedCandidates)

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
