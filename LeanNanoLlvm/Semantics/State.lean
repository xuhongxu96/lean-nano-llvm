import LeanNanoLlvm.Semantics.Semantics
import LeanNanoLlvm.AST.AST
import Std.Data.ExtHashMap
import LeanNanoLlvm.Util.Undef

namespace LeanNanoLlvm.Semantics

open Std

inductive RegisterValue : Type where
  | bv (w : Nat) (val : IntW w)
  | void
deriving DecidableEq

instance : ToString RegisterValue where
  toString
    | .bv _w .poison => "poison"
    | .bv _w (.value v) => s!"{v}"
    | .void => "void"

 def castRegValue? (w : Nat) : RegisterValue → Option (IntW w)
  | .bv w' v =>
    if h : w' = w then some (h ▸ v) else none
  | .void => none

structure NanoLlvmState : Type where
  (registers : ExtHashMap AST.Identifier RegisterValue)
  -- TODO: memory
  -- (memory : ExtHashMap MemoryAddress MemoryValue)

deriving instance Inhabited for NanoLlvmState

abbrev UndefChain : Type := SupplyChain Nat
abbrev UndefState : Type := SupplyState Nat
abbrev NanoLlvmStateM (retTy : Type) := StateT NanoLlvmState (StateT UndefState (Except String)) retTy

@[simp]
def runNanoLlvmStateM {α : Type} (m : NanoLlvmStateM α) (st : NanoLlvmState := default)
    (uState : UndefState := default) : Except String α :=
  ((m.run st).run uState).map (fun ((a, _), _) => a)

@[simp]
def runNanoLlvmStateMWithState {α : Type} (m : NanoLlvmStateM α) (st : NanoLlvmState := default)
    (uState : UndefState := default) : Except String ((α × NanoLlvmState) × UndefState) :=
  (m.run st).run uState

end LeanNanoLlvm.Semantics
