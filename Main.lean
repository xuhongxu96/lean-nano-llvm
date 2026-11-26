import LeanNanoLlvm
import LeanNanoLlvm.AST.Test
import LeanNanoLlvm.Semantics.Test
import LeanNanoLlvm.Refinement.Test
import LeanNanoLlvm.Llubi

open LeanNanoLlvm
open LeanNanoLlvm.AST
open LeanNanoLlvm.Semantics

private def formatPoison {α : Type} (fmt : α → String) : PoisonOr α → String
  | .poison => "poison"
  | .value v => fmt v

private def padHex (width : Nat) (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  let pad := if s.length < width then String.ofList (List.replicate (width - s.length) '0') else ""
  pad ++ s

private def formatRegisterValue : RegisterValue → String
  | .void => "void"
  | .bv w pv => s!"i{w} {formatPoison (fun bv => toString bv.toNat) pv}"
  | .byte w bits =>
    let bitStr := String.ofList (bits.reverse.map fun
      | .concrete true _ => '1'
      | .concrete false _ => '0'
      | .poison | .undef => '!')
    s!"b{w} {bitStr}"
  | .float ft pv =>
    let hexW := (ft.bitWidth + 3) / 4
    s!"{ft.print} {formatPoison (fun f => s!"0x{padHex hexW f.bits.toNat}") pv}"
  | .ptr as pv =>
    s!"ptr(as={as}) {formatPoison (fun p => s!"0x{String.ofList (Nat.toDigits 16 p.addr.toNat)}") pv}"
  | .vector _ elems =>
    let body := String.intercalate ", " (elems.map formatRegisterValue)
    s!"<{body}>"
  | .array _ elems =>
    let body := String.intercalate ", " (elems.map formatRegisterValue)
    s!"[{body}]"
  | .struct packed _ fields =>
    let body := String.intercalate ", " (fields.map formatRegisterValue)
    if packed then s!"<\{ {body} }>" else s!"\{ {body} }"

private structure RunOpts where
  file              : String := ""
  entry             : String := "main"
  cfg               : SemanticsConfig := SemanticsConfig.modern
  seed?             : Option Nat := none
  verbose           : Bool := false
  disableVerify     : Bool := false
  nanTargetSpecific : Bool := false
deriving Inhabited

private def parseKeyVal (arg : String) : Option (String × String) :=
  match arg.splitOn "=" with
  | [k, v] => some (k, v)
  | k :: rest => if rest.isEmpty then none else some (k, String.intercalate "=" rest)
  | [] => none

private def applyNanBehavior (opts : RunOpts) (v : String) : Except String RunOpts :=
  match v with
  | "preferred" => .ok { opts with cfg := { opts.cfg with nanMode := .preferred }, nanTargetSpecific := false }
  | "quieting" => .ok { opts with cfg := { opts.cfg with nanMode := .quieting }, nanTargetSpecific := false }
  | "unchanged" => .ok { opts with cfg := { opts.cfg with nanMode := .unchanged }, nanTargetSpecific := false }
  | "target-specific" => .ok { opts with cfg := { opts.cfg with nanMode := .preferred }, nanTargetSpecific := true }
  | "nondet" => .ok { opts with cfg := { opts.cfg with nanMode := .nondet }, nanTargetSpecific := false }
  | _ => .error s!"invalid --nan-behavior value: {v}"

private def applyUndefBehavior (cfg : SemanticsConfig) (v : String) : Except String SemanticsConfig :=
  match v with
  | "zero" => .ok { cfg with undefMode := .zero }
  | "nondet" => .ok { cfg with undefMode := .nondet }
  | "disabled" | "poison" => .ok { cfg with undefMode := .disabled }
  | _ => .error s!"invalid --undef-behavior value: {v}"

private def parseRunArgs (args : List String) : Except String RunOpts :=
  let rec go (opts : RunOpts) : List String → Except String RunOpts
    | [] => .ok opts
    | "--verbose" :: rest => go { opts with verbose := true } rest
    | "--deterministic" :: rest =>
      go { opts with cfg := { opts.cfg with undefMode := .zero, freezeMode := .zero, nanMode := .preferred } } rest
    | "--undef" :: rest => go { opts with cfg := { opts.cfg with undefMode := .nondet } } rest
    | "--zero-undef" :: rest => go { opts with cfg := { opts.cfg with undefMode := .zero } } rest
    | "--disable-verify" :: rest => go { opts with disableVerify := true } rest
    | "--fuse-fmuladd" :: rest => go { opts with cfg := { opts.cfg with fuseFMulAdd := true } } rest
    | "--entry" :: name :: rest | "--entry-function" :: name :: rest =>
      go { opts with entry := name } rest
    | "--seed" :: s :: rest =>
      match s.toNat? with
      | some n => go { opts with seed? := some n } rest
      | none => .error s!"invalid --seed value: {s}"
    | "--max-steps" :: s :: rest =>
      match s.toNat? with
      | some n => go { opts with cfg := { opts.cfg with maxSteps := n } } rest
      | none => .error s!"invalid --max-steps value: {s}"
    | "--max-stack-depth" :: s :: rest =>
      match s.toNat? with
      | some n => go { opts with cfg := { opts.cfg with maxStackDepth := n } } rest
      | none => .error s!"invalid --max-stack-depth value: {s}"
    | "--max-mem" :: s :: rest =>
      match s.toNat? with
      | some n => go { opts with cfg := { opts.cfg with maxMem := n } } rest
      | none => .error s!"invalid --max-mem value: {s}"
    | "--vscale" :: s :: rest =>
      match s.toNat? with
      | some n => go { opts with cfg := { opts.cfg with vscale := if n == 0 then 1 else n } } rest
      | none => .error s!"invalid --vscale value: {s}"
    | "--nan-behavior" :: v :: rest =>
      match applyNanBehavior opts v with
      | .ok o' => go o' rest
      | .error e => .error e
    | "--undef-behavior" :: v :: rest =>
      match applyUndefBehavior opts.cfg v with
      | .ok c => go { opts with cfg := c } rest
      | .error e => .error e
    | arg :: rest =>
      if arg.startsWith "--" then
        match parseKeyVal arg with
        | some ("--entry", v) | some ("--entry-function", v) => go { opts with entry := v } rest
        | some ("--max-steps", s) =>
          match s.toNat? with
          | some n => go { opts with cfg := { opts.cfg with maxSteps := n } } rest
          | none => .error s!"invalid --max-steps value: {s}"
        | some ("--max-stack-depth", s) =>
          match s.toNat? with
          | some n => go { opts with cfg := { opts.cfg with maxStackDepth := n } } rest
          | none => .error s!"invalid --max-stack-depth value: {s}"
        | some ("--max-mem", s) =>
          match s.toNat? with
          | some n => go { opts with cfg := { opts.cfg with maxMem := n } } rest
          | none => .error s!"invalid --max-mem value: {s}"
        | some ("--vscale", s) =>
          match s.toNat? with
          | some n => go { opts with cfg := { opts.cfg with vscale := if n == 0 then 1 else n } } rest
          | none => .error s!"invalid --vscale value: {s}"
        | some ("--nan-behavior", v) =>
          match applyNanBehavior opts v with
          | .ok o' => go o' rest
          | .error e => .error e
        | some ("--undef-behavior", v) =>
          match applyUndefBehavior opts.cfg v with
          | .ok c => go { opts with cfg := c } rest
          | .error e => .error e
        | some ("--fuse-fmuladd", v) =>
          go { opts with cfg := { opts.cfg with fuseFMulAdd := v != "false" && v != "0" } } rest
        | some ("--seed", s) =>
          match s.toNat? with
          | some n => go { opts with seed? := some n } rest
          | none => .error s!"invalid --seed value: {s}"
        | _ => .error s!"unknown option: {arg}"
      else if arg == "-" then
        go { opts with file := "-" } rest
      else if arg.startsWith "-" then
        .error s!"unknown option: {arg}"
      else
        go { opts with file := arg } rest
  go {} args

/-- Run `execStep` step-by-step, optionally printing `VAL: %id => <val>` for each SSA result. -/
private def runStepsVerbose (fuel : Nat) (verbose : Bool) (o : OracleState) (c : Config) : IO Config := do
  let rec go : Nat → OracleState → Config → IO Config
    | 0, _, .running _ => return .resourceError .outOfFuel
    | 0, _, cfg => return cfg
    | rem + 1, o, cfg => do
      match cfg with
      | .running st =>
        let beforeDepth := st.frames.length
        let beforeInstr? := match st.frames with
          | fr :: _ =>
            match fr.remainingCode with
            | (iid, _) :: _ => some iid
            | [] => none
          | [] => none
        let (_, cfg', o') := execStep o cfg
        if verbose then
          match beforeInstr?, cfg' with
          | some (.id rid), .running st' =>
            if st'.frames.length == beforeDepth then
              match st'.frames with
              | fr' :: _ =>
                match fr'.registers.get? (.local_id rid) with
                | some val => IO.println s!"VAL: %{rid.ToString} => {formatRegisterValue val}"
                | none => pure ()
              | [] => pure ()
          | none, .running st' =>
            -- Returning from a callee frame into caller frame: check if caller got returnDest written
            if st'.frames.length + 1 == beforeDepth then
              match st.frames with
              | _ :: caller :: _ =>
                match caller.returnDest?, st'.frames with
                | some rd, caller' :: _ =>
                  match rd.destId with
                  | .id rid =>
                    match caller'.registers.get? (.local_id rid) with
                    | some val => IO.println s!"VAL: %{rid.ToString} => {formatRegisterValue val}"
                    | none => pure ()
                  | .void _ => pure ()
                | _, _ => pure ()
              | _ => pure ()
          | _, _ => pure ()
        go rem o' cfg'
      | other => return other
  go fuel o c

private def printUsage : IO Unit := do
  IO.println "Usage:"
  IO.println "  lean-nano-llvm                                      Run built-in demo"
  IO.println "  lean-nano-llvm run [file.ll | -] [options]          Parse and execute a .ll module"
  IO.println "  lean-nano-llvm llubi [llubi options] [file.ll | -]  llubi-compatible frontend (same output format)"
  IO.println "Options:"
  IO.println "  --verbose                  Print per-instruction SSA values (`VAL: %x => ...`)"
  IO.println "  --entry <name>             Entry function name (default: main)"
  IO.println "  --entry-function=<name>    Alias for --entry"
  IO.println "  --undef                    Enable nondeterministic `undef` mode"
  IO.println "  --zero-undef               Enable deterministic-zero `undef` mode"
  IO.println "  --deterministic            Deterministic execution (`undef=0`, `freeze=0`, preferred NaN)"
  IO.println "  --nan-behavior=<mode>      NaN mode: preferred | quieting | target-specific | nondet"
  IO.println "  --undef-behavior=<mode>    Undef mode: zero | nondet | disabled"
  IO.println "  --max-steps=<N>            Step fuel limit"
  IO.println "  --max-stack-depth=<N>      Call stack depth limit"
  IO.println "  --max-mem=<N>              Memory allocation byte limit"
  IO.println "  --vscale=<N>               Scalable vector vscale multiplier"
  IO.println "  --fuse-fmuladd[=bool]      Control `llvm.fmuladd` fusion"
  IO.println "  --seed <N>                 Oracle PRNG seed"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.println s!"Hello, LeanNanoLlvm!"
    IO.println llvm_0_plus_1.print
    return 0
  | ["--help"] | ["-h"] =>
    printUsage
    return 0
  | "llubi" :: rest =>
    -- llubi-compatible frontend (same options, trace format, diagnostics and exit codes)
    LeanNanoLlvm.Llubi.llubiMain rest
  | "run" :: rest =>
    match parseRunArgs rest with
    | .error msg =>
      IO.eprintln s!"CLI_ERROR: {msg}"
      printUsage
      return 4
    | .ok opts =>
      let src ←
        if opts.file.isEmpty || opts.file == "-" then
          (← IO.getStdin).readToEnd
        else
          IO.FS.readFile opts.file
      match Parser.parseLlvmModule src opts.cfg.vscale with
      | .error msg =>
        IO.eprintln s!"PARSE_ERROR: {msg}"
        return 4
      | .ok parsed =>
        if !opts.disableVerify then
          let hasBadPhi := parsed.topLevel.entities.any fun
            | .definition defn =>
              defn.blocks.any fun blk =>
                blk.code.any fun (_, instr) =>
                  match instr with
                  | .phi _ _ inc _ =>
                    -- Check for duplicate predecessor blocks with different incoming expressions
                    inc.any fun (e1, b1) =>
                      inc.any fun (e2, b2) => b1 == b2 && e1.print != e2.print
                  | _ => false
            | _ => false
          if hasBadPhi then
            IO.eprintln "STATIC_ERROR: PHINode should have one entry for each predecessor (input module is broken!)"
            return 2
        let effCfg : SemanticsConfig :=
          if opts.nanTargetSpecific then
            let tr := parsed.dataLayout.targetTriple
            let nm :=
              if tr.startsWith "sparc" then NaNPropagationMode.sparcPreferred
              else if tr.startsWith "wasm" then NaNPropagationMode.wasm
              else NaNPropagationMode.preferred
            { opts.cfg with nanMode := nm }
          else opts.cfg
        let oracle : OracleState := match opts.seed? with
          | none => default
          | some s => { oracle := fun i => (s * 6364136223846793005 + i * 1442695040888963407 + 1) % (2 ^ 64) }
        match initModuleExec parsed.topLevel effCfg parsed.dataLayout oracle with
        | .error (.immediateUB msg) =>
          IO.eprintln s!"UB: {msg}"
          return 1
        | .error (.staticError msg) =>
          IO.eprintln s!"STATIC_ERROR: {msg}"
          return 2
        | .error .outOfFuel =>
          IO.eprintln "RESOURCE_ERROR: out of fuel"
          return 3
        | .error .outOfMemory =>
          IO.eprintln "RESOURCE_ERROR: out of memory"
          return 3
        | .error .stackOverflow =>
          IO.eprintln "RESOURCE_ERROR: stack overflow"
          return 3
        | .ok (mem, fns, decls, o1) =>
          match fns.get? (.name opts.entry) with
          | none =>
            IO.eprintln s!"STATIC_ERROR: Function @{opts.entry} not found in module"
            return 2
          | some defn =>
            let (mem', entryArgs) : MemoryState × List RegisterValue :=
              match defn.prototype.type with
              | .function _ [.int w, .ptr as] _ =>
                let ptrSz := (parsed.dataLayout.getPointerSizeInBits as + 7) / 8
                let ptrAlign := parsed.dataLayout.getPointerABIAlign as
                match mem.allocate parsed.dataLayout effCfg (ptrSz * 2) ptrAlign "argv" as .zeroed .global false with
                | .ok (argvObj, m1) =>
                  (m1, [.bv w (.value (BitVec.ofNat w 1)), .ptr as (.value (MemoryState.derivePointer parsed.dataLayout argvObj))])
                | .error _ =>
                  (mem, [.bv w (.value (BitVec.ofNat w 1)), .ptr as (.value (Pointer.null parsed.dataLayout as))])
              | _ => (mem, [])
            let initCfg := initCallConfig effCfg parsed.dataLayout mem' fns decls defn entryArgs
            let finalCfg ← runStepsVerbose effCfg.maxSteps opts.verbose o1 initCfg
            match finalCfg.toExcept with
            | .ok val =>
              if opts.entry == "main" && val.containsPoison then
                IO.eprintln s!"STATIC_ERROR: Execution of function 'main' resulted in poison return value."
                return 2
              else
                IO.println s!"OK: {formatRegisterValue val}"
                return 0
            | .error (.immediateUB msg) =>
              IO.eprintln s!"UB: {msg}"
              return 1
            | .error (.staticError msg) =>
              IO.eprintln s!"STATIC_ERROR: {msg}"
              return 2
            | .error .outOfFuel =>
              IO.eprintln "RESOURCE_ERROR: out of fuel"
              return 3
            | .error .outOfMemory =>
              IO.eprintln "RESOURCE_ERROR: out of memory"
              return 3
            | .error .stackOverflow =>
              IO.eprintln "RESOURCE_ERROR: stack overflow"
              return 3
  | _ =>
    IO.eprintln s!"CLI_ERROR: unknown command '{String.intercalate " " args}'"
    printUsage
    return 4
