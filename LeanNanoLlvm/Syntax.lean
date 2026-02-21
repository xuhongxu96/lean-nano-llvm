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
  | local_id (id : RawId) -- %id
deriving Repr, DecidableEq


abbrev LocalId := RawId
abbrev GlobalId := RawId
abbrev BlockId := RawId
abbrev FunctionId := GlobalId

inductive InstructionId
  | id (id : RawId)
  | void (n : Nat) -- give unique ids to instructions that have void return type, such as `store`, terminators, etc.
deriving Repr, DecidableEq

section

variable (φ : Nat)

mutual

inductive LlvmRetType : Type where
  | void
  | ret (type : LlvmType)

inductive LlvmType : Type where
  | int (w : Width φ)
  | identifier (id : Identifier)
  | function (ret : LlvmRetType) (args : List LlvmType)
deriving Repr

end

end

instance : ToFormat (Width φ) := ⟨repr⟩
instance : ToFormat (LlvmType φ) := ⟨repr⟩

def LlvmType.i (w : Width φ) : LlvmType φ := .int w

abbrev LlvmType.i1 : LlvmType φ := .i 1
abbrev LlvmType.i32 : LlvmType φ := .i 1


abbrev TypedIdentifier φ := Identifier × (LlvmType φ)


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


inductive Exp : Type where
  | identifier (id : Identifier)
  | bool       (b : Bool)
  | int        (x : Int)
  | null
  | undef
  | poison
deriving Repr

abbrev TypedExp φ := LlvmType φ × Exp


variable {φ : Nat}


inductive Instruction : Type where
  | intBinaryOp   (op : IntBinaryOp) (t : LlvmType φ) (v1 : Exp) (v2 : Exp)
  | conversionOp  (op : ConversionOp) (fromTy: LlvmType φ) (v : Exp) (toTy : LlvmType φ)
  | freeze        (v : LlvmType φ × Exp)


inductive Terminator : Type where
  | retVoid
  | ret (v : TypedExp φ)


structure Declaration where
  (name : FunctionId)
  (type : LlvmType φ)

abbrev Code := List (InstructionId × @Instruction φ)

structure Block where
  (id : BlockId)
  (code : @Code φ)
  (terminator : InstructionId × @Terminator φ)

structure Definition where
  (prototype : @Declaration φ)
  (args : List LocalId)
  (body : @Block φ) -- FIXME: Only support a single block

inductive TopLevelEntity where
  | declaration (decl : @Declaration φ)
  | definition  (defn : @Definition φ)

abbrev TopLevel (φ : Nat) := List (@TopLevelEntity φ)


end LeanNanoLlvm.Syntax
