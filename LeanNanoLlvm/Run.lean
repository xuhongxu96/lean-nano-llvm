import LeanNanoLlvm.AST
import LeanNanoLlvm.Semantics
import LeanNanoLlvm.Util.Hex

/-!
# `lean-nano-llvm run`

Parses a `.ll` module and executes one of its functions with the executable interpreter
(`execStep`), printing the result as `OK: <value>` or a diagnostic. Exit codes: `0` success,
`1` immediate UB, `2` static error, `3` resource exhaustion, `4` usage or parse error.
-/

namespace LeanNanoLlvm.Run

open AST Semantics

/-! ### Options -/

structure Options where
  file              : String := "-"
  entry             : String := "main"
  cfg               : SemanticsConfig := .modern
  seed?             : Option Nat := none
  verbose           : Bool := false
  disableVerify     : Bool := false
  /-- `--nan-behavior=target-specific`: choose the NaN mode from the module's target triple. -/
  nanTargetSpecific : Bool := false

/-- Options without a value. -/
private def setFlag (opts : Options) : String → Option Options
  | "--verbose" => some { opts with verbose := true }
  | "--disable-verify" => some { opts with disableVerify := true }
  | "--undef" => some { opts with cfg.undefMode := .nondet }
  | "--zero-undef" => some { opts with cfg.undefMode := .zero }
  | "--fuse-fmuladd" => some { opts with cfg.fuseFMulAdd := true }
  | "--deterministic" =>
    some { opts with cfg.undefMode := .zero, cfg.freezeMode := .zero, cfg.nanMode := .preferred }
  | _ => none

private def natValue (name v : String) : Except String Nat :=
  match v.toNat? with
  | some n => .ok n
  | none => .error s!"invalid {name} value: {v}"

/-- Options with a value; `none` if `name` is not one. -/
private def setValue (opts : Options) (name v : String) : Option (Except String Options) :=
  match name with
  | "--entry" | "--entry-function" => some (.ok { opts with entry := v })
  | "--seed" => some do return { opts with seed? := some (← natValue name v) }
  | "--max-steps" => some do return { opts with cfg.maxSteps := ← natValue name v }
  | "--max-stack-depth" => some do return { opts with cfg.maxStackDepth := ← natValue name v }
  | "--max-mem" => some do return { opts with cfg.maxMem := ← natValue name v }
  | "--vscale" => some do return { opts with cfg.vscale := max 1 (← natValue name v) }
  | "--fuse-fmuladd" => some (.ok { opts with cfg.fuseFMulAdd := v != "false" && v != "0" })
  | "--nan-behavior" =>
    let set (m : NaNPropagationMode) (targetSpecific := false) : Except String Options :=
      .ok { opts with cfg.nanMode := m, nanTargetSpecific := targetSpecific }
    some <| match v with
      | "preferred" => set .preferred
      | "quieting" => set .quieting
      | "unchanged" => set .unchanged
      | "nondet" => set .nondet
      | "target-specific" => set .preferred (targetSpecific := true)
      | _ => .error s!"invalid --nan-behavior value: {v}"
  | "--undef-behavior" =>
    some <| match v with
      | "zero" => .ok { opts with cfg.undefMode := .zero }
      | "nondet" => .ok { opts with cfg.undefMode := .nondet }
      | "disabled" | "poison" => .ok { opts with cfg.undefMode := .disabled }
      | _ => .error s!"invalid --undef-behavior value: {v}"
  | _ => none

/-- Parse the arguments of `run`: options (`--name value` or `--name=value`) and one input file
(`-` or none for standard input). -/
def parseArgs (args : List String) : Except String Options :=
  go {} args
where
  go (opts : Options) : List String → Except String Options
    | [] => .ok opts
    | arg :: rest =>
      if arg.startsWith "--" then
        match arg.splitOn "=" with
        | name :: v :: vs =>
          match setValue opts name ("=".intercalate (v :: vs)) with
          | some r => do go (← r) rest
          | none => .error s!"unknown option: {arg}"
        | _ =>
          if let some opts' := setFlag opts arg then go opts' rest
          else match rest with
            | v :: rest' =>
              match setValue opts arg v with
              | some r => do go (← r) rest'
              | none => .error s!"unknown option: {arg}"
            | [] => .error s!"unknown option: {arg}"
      else if arg != "-" && arg.startsWith "-" then .error s!"unknown option: {arg}"
      else go { opts with file := arg } rest
  termination_by args => args.length

def usage : String := "\
Options of `run`:
  --verbose                  Print per-instruction SSA values (`VAL: %x => ...`)
  --entry <name>             Entry function name (default: main)
  --entry-function=<name>    Alias for --entry
  --undef                    Enable nondeterministic `undef` mode
  --zero-undef               Enable deterministic-zero `undef` mode
  --deterministic            Deterministic execution (`undef=0`, `freeze=0`, preferred NaN)
  --nan-behavior=<mode>      NaN mode: preferred | quieting | unchanged | target-specific | nondet
  --undef-behavior=<mode>    Undef mode: zero | nondet | disabled
  --max-steps=<N>            Step fuel limit
  --max-stack-depth=<N>      Call stack depth limit
  --max-mem=<N>              Memory allocation byte limit
  --vscale=<N>               Scalable vector vscale multiplier
  --fuse-fmuladd[=bool]      Control `llvm.fmuladd` fusion
  --disable-verify           Skip the module verifier
  --seed <N>                 Oracle PRNG seed"

/-! ### Output -/

/-- The CLI rendering of a value: its type and payload, with integers in decimal and floats and
pointers as hexadecimal bit patterns. -/
partial def formatValue : RegisterValue → String
  | .void => "void"
  | .bv w pv => s!"i{w} {poisonOr pv fun bv => toString bv.toNat}"
  | .byte w bits =>
    let bitChar : MemBit → Char
      | .concrete true _ => '1'
      | .concrete false _ => '0'
      | _ => '!'
    s!"b{w} {String.ofList (bits.reverse.map bitChar)}"
  | .float ft pv =>
    s!"{ft.print} {poisonOr pv fun f => "0x" ++ Hex.lowerPadded ((ft.bitWidth + 3) / 4) f.bits.toNat}"
  | .ptr as pv => s!"ptr(as={as}) {poisonOr pv fun p => "0x" ++ Hex.lower p.addr.toNat}"
  | .vector _ elems => "<" ++ list elems ++ ">"
  | .array _ elems => "[" ++ list elems ++ "]"
  | .struct packed _ fields => if packed then "<{ " ++ list fields ++ " }>" else "{ " ++ list fields ++ " }"
where
  poisonOr {α : Type} (pv : PoisonOr α) (f : α → String) : String :=
    match pv with
    | .poison => "poison"
    | .value v => f v
  list (vs : List RegisterValue) : String := ", ".intercalate (vs.map formatValue)

/-- Report an execution error on stderr and return its exit code. -/
def reportError : ExecError → IO UInt32
  | .immediateUB msg => do IO.eprintln s!"UB: {msg}"; return 1
  | .staticError msg => do IO.eprintln s!"STATIC_ERROR: {msg}"; return 2
  | .outOfFuel => do IO.eprintln "RESOURCE_ERROR: out of fuel"; return 3
  | .outOfMemory => do IO.eprintln "RESOURCE_ERROR: out of memory"; return 3
  | .stackOverflow => do IO.eprintln "RESOURCE_ERROR: stack overflow"; return 3

/-! ### Execution -/

/-- The SSA value defined by the step from `st` to `c'`, if any: the result of a non-call
instruction (same frame depth), or the result of a call when its callee returns. -/
def definedValue? (st : MachineState) (c' : Config) : Option (RawId × RegisterValue) := do
  let .running st' := c' | none
  let fr ← st.frames.head?
  let fr' ← st'.frames.head?
  match fr.remainingCode.head? with
  | some (.id rid, _) =>
    guard (st'.frames.length == st.frames.length)
    return (rid, ← fr'.registers.get? (.local_id rid))
  | some (.void _, _) => none
  | none =>
    -- a `ret` popped the frame: the caller binds the call's result
    guard (st'.frames.length + 1 == st.frames.length)
    let caller ← st.frames[1]?
    let rd ← caller.returnDest?
    let .id rid := rd.destId | none
    return (rid, ← fr'.registers.get? (.local_id rid))

/-- Run `execStep` until the configuration is final or `fuel` is exhausted; with `verbose`,
print `VAL: %x => v` for every SSA value defined. -/
def runVerbose (verbose : Bool) : Nat → OracleState → Config → IO Config
  | 0, _, .running _ => return .resourceError .outOfFuel
  | fuel + 1, o, c@(.running st) => do
    let (_, c', o') := execStep o c
    if verbose then
      if let some (rid, v) := definedValue? st c' then
        IO.println s!"VAL: %{rid} => {formatValue v}"
    runVerbose verbose fuel o' c'
  | _, _, c => return c

/-- The module verifier's check for `phi` nodes listing a predecessor twice with different values. -/
def hasConflictingPhi (m : TopLevel) : Bool :=
  m.entities.any fun
    | .definition defn =>
      defn.blocks.any fun blk => blk.code.any fun
        | (_, .phi _ _ inc _) => inc.any fun (e1, b1) => inc.any fun (e2, b2) => b1 == b2 && e1.print != e2.print
        | _ => false
    | _ => false

/-- The NaN propagation mode `--nan-behavior=target-specific` selects for `triple`. -/
def targetNaNMode (triple : String) : NaNPropagationMode :=
  if triple.startsWith "sparc" then .sparcPreferred
  else if triple.startsWith "wasm" then .wasm
  else .preferred

/-- Arguments for an entry function of type `(iN, ptr)`: `argc = 1` and a zeroed `argv`. -/
def entryArgs (dl : DataLayout) (cfg : SemanticsConfig) (mem : MemoryState) (defn : Definition) :
    MemoryState × List RegisterValue :=
  match defn.prototype.type with
  | .function _ [.int w, .ptr as] _ =>
    let argc := RegisterValue.bv w (.value (BitVec.ofNat w 1))
    let ptrBytes := (dl.getPointerSizeInBits as + 7) / 8
    match mem.allocate dl cfg (ptrBytes * 2) (dl.getPointerABIAlign as) "argv" as .zeroed .global false with
    | .ok (argv, mem') => (mem', [argc, .ptr as (.value (MemoryState.derivePointer dl argv))])
    | .error _ => (mem, [argc, .ptr as (.value (Pointer.null dl as))])
  | _ => (mem, [])

/-- `lean-nano-llvm run <args>`. -/
def main (args : List String) : IO UInt32 := do
  let opts ← match parseArgs args with
    | .ok opts => pure opts
    | .error msg =>
      IO.eprintln s!"CLI_ERROR: {msg}"
      IO.eprintln usage
      return 4
  let src ← if opts.file == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile opts.file
  let parsed ← match Parser.parseLlvmModule src opts.cfg.vscale with
    | .ok parsed => pure parsed
    | .error msg =>
      IO.eprintln s!"PARSE_ERROR: {msg}"
      return 4
  if !opts.disableVerify && hasConflictingPhi parsed.topLevel then
    IO.eprintln "STATIC_ERROR: PHINode should have one entry for each predecessor (input module is broken!)"
    return 2
  let dl := parsed.dataLayout
  let cfg := if opts.nanTargetSpecific then { opts.cfg with nanMode := targetNaNMode dl.targetTriple }
    else opts.cfg
  -- a fixed linear-congruential stream per seed (the `llubi` frontend uses `mt19937_64` instead)
  let oracle : OracleState := match opts.seed? with
    | none => default
    | some s => { oracle := fun i => (s * 6364136223846793005 + i * 1442695040888963407 + 1) % 2 ^ 64 }
  let (mem, fns, decls, oracle) ← match initModuleExec parsed.topLevel cfg dl oracle with
    | .ok r => pure r
    | .error e => return ← reportError e
  let some defn := fns.get? (.name opts.entry)
    | IO.eprintln s!"STATIC_ERROR: Function @{opts.entry} not found in module"; return 2
  let (mem, args) := entryArgs dl cfg mem defn
  let final ← runVerbose opts.verbose cfg.maxSteps oracle (initCallConfig cfg dl mem fns decls defn args)
  match final.toExcept with
  | .error e => reportError e
  | .ok val =>
    if opts.entry == "main" && val.containsPoison then
      IO.eprintln "STATIC_ERROR: Execution of function 'main' resulted in poison return value."
      return 2
    IO.println s!"OK: {formatValue val}"
    return 0

end LeanNanoLlvm.Run
