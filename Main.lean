import LeanNanoLlvm
import LeanNanoLlvm.AST.Test
import LeanNanoLlvm.Semantics.Test
import LeanNanoLlvm.Refinement.Test

def main : IO Unit := do
  IO.println s!"Hello, LeanNanoLlvm!"
  IO.println llvm_0_plus_1.print
