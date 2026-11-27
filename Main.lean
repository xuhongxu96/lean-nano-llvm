import LeanNanoLlvm

/-!
# `lean-nano-llvm`

* `lean-nano-llvm run [options] [file.ll | -]`: execute a module (`LeanNanoLlvm.Run`).
* `lean-nano-llvm llubi [llubi options] [file.ll | -]`: the `llubi`-compatible frontend
  (`LeanNanoLlvm.Llubi`), with `llubi`'s options, output, diagnostics and exit codes.
-/

open LeanNanoLlvm

def usage : String := "\
Usage:
  lean-nano-llvm run [options] [file.ll | -]          Parse and execute a .ll module
  lean-nano-llvm llubi [llubi options] [file.ll | -]  llubi-compatible frontend

" ++ Run.usage

def main : List String → IO UInt32
  | "run" :: args => Run.main args
  | "llubi" :: args => Llubi.llubiMain args
  | [] | ["--help"] | ["-h"] => do IO.println usage; return 0
  | args => do
    IO.eprintln s!"CLI_ERROR: unknown command '{" ".intercalate args}'"
    IO.eprintln usage
    return 4
