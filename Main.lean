import LeanNanoLlvm
import LeanNanoLlvm.AST.Test
import LeanNanoLlvm.Semantics.Test
import LeanNanoLlvm.Refinement.Test

open LeanNanoLlvm
open LeanNanoLlvm.AST
open LeanNanoLlvm.Semantics

private def formatPoison {α : Type} (fmt : α → String) : PoisonOr α → String
  | .poison => "poison"
  | .value v => fmt v

private def formatRegisterValue : RegisterValue → String
  | .void => "void"
  | .bv w pv => s!"i{w} {formatPoison (fun bv => toString bv.toNat) pv}"
  | .float ft pv => s!"{ft.print} {formatPoison (fun f => s!"0x{String.ofList (Nat.toDigits 16 f.bits.toNat)}") pv}"
  | .ptr as pv => s!"ptr(as={as}) {formatPoison (fun p => s!"0x{String.ofList (Nat.toDigits 16 p.addr.toNat)}") pv}"
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
  file  : String := ""
  entry : String := "main"
  cfg   : SemanticsConfig := SemanticsConfig.modern
  seed? : Option Nat := none
deriving Inhabited

private def parseRunArgs : List String → Except String RunOpts
  | [] => .error "missing <file.ll> argument"
  | args =>
    let rec goPos (opts : RunOpts) : List String → Except String RunOpts
      | [] =>
        if opts.file.isEmpty then .error "missing <file.ll> argument"
        else .ok opts
      | "--entry" :: name :: rest => goPos { opts with entry := name } rest
      | "--undef" :: rest => goPos { opts with cfg := { opts.cfg with undefMode := .nondet } } rest
      | "--zero-undef" :: rest => goPos { opts with cfg := { opts.cfg with undefMode := .zero } } rest
      | "--seed" :: s :: rest =>
        match s.toNat? with
        | some n => goPos { opts with seed? := some n } rest
        | none => .error s!"invalid --seed value: {s}"
      | "--max-steps" :: s :: rest =>
        match s.toNat? with
        | some n => goPos { opts with cfg := { opts.cfg with maxSteps := n } } rest
        | none => .error s!"invalid --max-steps value: {s}"
      | arg :: rest =>
        if arg.startsWith "-" then .error s!"unknown option: {arg}"
        else goPos { opts with file := arg } rest
    goPos {} args

private def printUsage : IO Unit := do
  IO.println "Usage:"
  IO.println "  lean-nano-llvm                                      Run built-in demo"
  IO.println "  lean-nano-llvm run <file.ll> [options]              Parse and execute a .ll module"
  IO.println "Options:"
  IO.println "  --entry <name>     Entry function name (default: main)"
  IO.println "  --undef            Enable nondeterministic `undef` mode"
  IO.println "  --zero-undef       Enable deterministic-zero `undef` mode"
  IO.println "  --seed <N>         Oracle PRNG seed"
  IO.println "  --max-steps <N>    Step fuel limit"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.println s!"Hello, LeanNanoLlvm!"
    IO.println llvm_0_plus_1.print
    return 0
  | ["--help"] | ["-h"] =>
    printUsage
    return 0
  | "run" :: rest =>
    match parseRunArgs rest with
    | .error msg =>
      IO.eprintln s!"CLI_ERROR: {msg}"
      printUsage
      return 4
    | .ok opts =>
      let src ← IO.FS.readFile opts.file
      match Parser.parseLlvmModule src with
      | .error msg =>
        IO.eprintln s!"PARSE_ERROR: {msg}"
        return 4
      | .ok parsed =>
        let oracle : OracleState := match opts.seed? with
          | none => default
          | some s => ⟨fun i => (s * 6364136223846793005 + i * 1442695040888963407 + 1) % (2 ^ 64), 0⟩
        match runModuleFunction parsed.topLevel (.name opts.entry) [] opts.cfg parsed.dataLayout oracle with
        | .ok val =>
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
