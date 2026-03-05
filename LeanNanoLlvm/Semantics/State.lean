import LeanNanoLlvm.Semantics.Semantics
import LeanNanoLlvm.AST.AST
import Std.Data.ExtHashMap

namespace LeanNanoLlvm.Semantics

open Std

inductive RegisterValue : Type where
  | bv (w : Nat) (val : IntW w)
  | void

instance : ToString RegisterValue where
  toString
    | .bv w .poison => "poison"
    | .bv w (.value v) => s!"{v}"
    | .void => "void"

 def castRegValue? (w : Nat) : RegisterValue → Option (IntW w)
  | .bv w' v =>
    if h : w' = w then some (h ▸ v) else none
  | .void => none

structure NanoLlvmState : Type where
  (registers : ExtHashMap AST.Identifier RegisterValue)
  (undefs : ExtHashMap AST.RawId RegisterValue)
  -- TODO: memory
  -- (memory : ExtHashMap MemoryAddress MemoryValue)

deriving instance Inhabited for NanoLlvmState

abbrev NanoLlvmStateM (retTy: Type) := StateT NanoLlvmState (Except String) retTy

end LeanNanoLlvm.Semantics
