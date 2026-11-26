namespace LeanNanoLlvm

/-- Controls how deprecated `undef` values and uninitialized memory are handled. -/
inductive UndefMode : Type where
  /-- `undef` is disallowed (modern LLVM direction); uninitialized memory/padding is `poison`. -/
  | disabled
  /-- `undef` draws nondeterministically from the execution oracle (legacy LLVM semantics). -/
  | nondet
  /-- `undef` deterministically evaluates to zero (matches `llubi --undef-behavior=zero`). -/
  | zero
deriving Repr, DecidableEq, Inhabited

/-- Controls how `freeze` resolves `poison` values. -/
inductive FreezeMode : Type where
  /-- `freeze poison` draws an arbitrary fixed value from the execution oracle (faithful LLVM). -/
  | nondet
  /-- `freeze poison` deterministically returns zero (matches `llubi --deterministic`). -/
  | zero
deriving Repr, DecidableEq, Inhabited

/-- Controls NaN propagation behavior (mirrors `llubi::NaNPropagationBehavior`). -/
inductive NaNPropagationMode : Type where
  /-- Canonical quiet NaN with zero payload. -/
  | preferred
  /-- Quiet bit set; payload propagated from an input NaN if present. -/
  | quieting
  /-- Payload and quiet bit copied unchanged from an input NaN if present. -/
  | unchanged
  /-- Nondeterministically pick among valid IEEE-754 / LLVM NaN propagation results via oracle. -/
  | nondet
deriving Repr, DecidableEq, Inhabited

/-- Denormal flushing behavior for FP inputs/outputs (mirrors `llvm::DenormalMode`). -/
inductive DenormalModeKind : Type where
  | ieee
  | preserveSign
  | positiveZero
deriving Repr, DecidableEq, Inhabited

structure DenormalMode : Type where
  input  : DenormalModeKind := .ieee
  output : DenormalModeKind := .ieee
deriving Repr, DecidableEq, Inhabited

/-- IEEE-754 rounding modes. -/
inductive RoundingMode : Type where
  | RNE  -- roundTiesToEven (default)
  | RNA  -- roundTiesToAway
  | RTP  -- roundTowardPositive (+∞)
  | RTN  -- roundTowardNegative (-∞)
  | RTZ  -- roundTowardZero
deriving Repr, DecidableEq, Inhabited

/-- Execution errors, cleanly separating LLVM Immediate UB from static/resource errors. -/
inductive ExecError : Type where
  /-- Genuine LLVM Immediate Undefined Behavior (can be refined by any behavior). -/
  | immediateUB (msg : String)
  /-- Malformed IR, type/width error, uninstantiated symbolic width, or disabled `undef`. -/
  | staticError (msg : String)
  /-- Execution step budget exceeded (non-termination / fuel exhaustion; not UB). -/
  | outOfFuel
  /-- Memory allocation budget exceeded. -/
  | outOfMemory
  /-- Call stack depth limit exceeded. -/
  | stackOverflow
deriving Repr, DecidableEq

instance : ToString ExecError where
  toString
    | .immediateUB msg => s!"Immediate UB: {msg}"
    | .staticError msg => s!"Static error: {msg}"
    | .outOfFuel => "Execution step limit exceeded"
    | .outOfMemory => "Memory limit exceeded"
    | .stackOverflow => "Maximum call stack depth exceeded"

def ExecError.isImmediateUB : ExecError → Bool
  | .immediateUB _ => true
  | _ => false

instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b =>
    if h : a = b then isTrue (by rw [h]) else isFalse (by intro heq; cases heq; exact h rfl)
  | .error e1, .error e2 =>
    if h : e1 = e2 then isTrue (by rw [h]) else isFalse (by intro heq; cases heq; exact h rfl)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

/-- Top-level semantic configuration for interpreting and proving refinement of LLVM IR. -/
structure SemanticsConfig : Type where
  /-- Toggle for deprecated `undef` support (default: disabled). -/
  undefMode     : UndefMode := .disabled
  /-- How `freeze poison` picks a concrete value. -/
  freezeMode    : FreezeMode := .nondet
  /-- How floating-point NaNs propagate. -/
  nanMode       : NaNPropagationMode := .preferred
  /-- Active floating-point rounding mode. -/
  roundingMode  : RoundingMode := .RNE
  /-- Active denormal mode for FP operations. -/
  denormalMode  : DenormalMode := {}
  /-- Step budget for multi-block loops and recursive calls (0 = default bounded). -/
  maxSteps      : Nat := 10000
  /-- Maximum call stack depth. -/
  maxStackDepth : Nat := 256
  /-- Maximum allocated bytes across all live objects. -/
  maxMem        : Nat := 1 <<< 28
  /-- Runtime `vscale` multiplier for scalable vectors `<vscale x N x T>`. -/
  vscale        : Nat := 1
  /-- Whether `llvm.fmuladd` fuses multiply-add (like `fma`) or rounds separately. -/
  fuseFMulAdd   : Bool := true
deriving Repr, DecidableEq

namespace SemanticsConfig

/-- Modern LLVM mode: `undef` disabled (uninit memory is `poison`), nondeterministic `freeze`. -/
def modern : SemanticsConfig := {}

/-- Full legacy-compatible mode with nondeterministic `undef` enabled. -/
def withUndef : SemanticsConfig := { undefMode := .nondet }

/-- Deterministic execution mode (matches `llubi --deterministic`). -/
def deterministic : SemanticsConfig :=
  { undefMode := .zero, freezeMode := .zero, nanMode := .preferred }

/-- Legacy compatibility preset matching earlier `lean-nano-llvm` tests (`undef` enabled, `freeze poison = 0`). -/
def legacyCompat : SemanticsConfig :=
  { undefMode := .nondet, freezeMode := .zero, nanMode := .preferred }

instance : Inhabited SemanticsConfig := ⟨.modern⟩

@[simp]
def allowUndef (cfg : SemanticsConfig) : Bool :=
  cfg.undefMode != .disabled

end SemanticsConfig

end LeanNanoLlvm
