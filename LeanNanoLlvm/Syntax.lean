import LeanNanoLlvm.Util.ConcreteOrMVar

open Lean PrettyPrinter

namespace LeanNanoLlvm.Syntax

abbrev Width φ := ConcreteOrMVar Nat φ
abbrev Width.concrete : Nat -> Width φ := ConcreteOrMVar.concrete
abbrev Width.mvar : Fin φ -> Width φ := ConcreteOrMVar.mvar


inductive RawId : Type where
  | name (s : String) -- Named identifiers: %arg, %val, %x
  | anonymom (n : Nat) -- Anonymous identifiers: %0, %1
deriving Repr, DecidableEq

def RawId.ToString (s : RawId) : String :=
  match s with
  | .name str => str
  | .anonymom i => s!"{i}"

instance : ToString RawId where
  toString := RawId.ToString


inductive Identifier : Type where
  | global_id (id : RawId) -- @id
  | local_id (id: RawId) -- %id
deriving Repr, DecidableEq


/--
  `void` is omitted because it is only used as return type, which should be mutually defined
  See https://github.com/vellvm/vellvm/blob/42b6b6578a3867a69aa68d576d576c10be9014c0/src/rocq/Syntax/LLVMAst.v#L297
--/
inductive LlvmType (φ : Nat := 0) : Type where
  | int (w : Width φ)
  | pointer
  | identifier (id:Identifier)
deriving Repr, DecidableEq

instance : ToFormat (Width φ) := ⟨repr⟩
instance : ToFormat (LlvmType φ) := ⟨repr⟩

def LlvmType.i (w : Width φ) : LlvmType φ := .int w

abbrev LlvmType.i1 : LlvmType φ := .i 1
abbrev LlvmType.i32 : LlvmType φ := .i 1


abbrev TypedIdentifier (φ := 0) := Identifier × (LlvmType φ)


inductive IntBinaryOp : Type where
  | add (nuw : Bool) (nsw : Bool)
  | sub (nuw : Bool) (nsw : Bool)
  | mul (nuw : Bool) (nsw : Bool)
  | shl (nuw : Bool) (nsw : Bool)
  | udiv (exact : Bool)
  | sdiv (exact : Bool)
  | lshr (exact : Bool)
  | ashr (exact : Bool)
  | urem
  | srem
  | and
  | or (disjoint : Bool)
  | xor
deriving Repr, DecidableEq

inductive ConversionOp : Type where
  | trunc (nuw : Bool) (nsw : Bool)
  | zext (nneg : Bool)
  | sext
deriving Repr, DecidableEq

end LeanNanoLlvm.Syntax
