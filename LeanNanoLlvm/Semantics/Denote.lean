import LeanNanoLlvm.Semantics.Semantics
import LeanNanoLlvm.AST
import Std.Data.ExtHashMap

namespace LeanNanoLlvm.Semantics

open Std

variable {φ : Nat}

inductive RegisterValue : Type where
  | bv (w : Nat) (val : BitVec w)

abbrev State := ExtHashMap AST.Identifier RegisterValue

def denoteNanoLlvmTopLevel (state : State) (topLevel : AST.TopLevel φ) : State :=
  sorry

end LeanNanoLlvm.Semantics
