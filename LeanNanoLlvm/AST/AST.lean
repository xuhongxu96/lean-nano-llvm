import LeanNanoLlvm.Util.ConcreteOrMVar

namespace LeanNanoLlvm.AST

abbrev Width (φ : Nat) := ConcreteOrMVar Nat φ
abbrev Width.concrete : Nat -> Width φ := ConcreteOrMVar.concrete
abbrev Width.mvar : Fin φ -> Width φ := ConcreteOrMVar.mvar

def Width.print : Width φ → String
  | .concrete w => s!"i{w}"
  | .mvar i => s!"i${i}"

def Width.toNat? : Width φ → Option Nat
  | .concrete w => some w
  | .mvar _ => none

@[simp]
def Width.instantiate (ws : List.Vector Nat φ) : Width φ → Width 0
  | w => .concrete <| ConcreteOrMVar.instantiate ws w

@[simp]
theorem Width.toNat?_concrete (w : Nat) : Width.toNat? (.concrete w : Width φ) = some w := rfl

@[simp]
theorem Width.toNat?_mvar (i : Fin φ) : Width.toNat? (.mvar i : Width φ) = none := rfl


inductive RawId : Type where
  | name (s : String) -- Named identifiers: %arg, %val, %x
  | anonymous (n : Nat) -- Anonymous identifiers: %0, %1
deriving Repr, DecidableEq

deriving instance Hashable for RawId

def RawId.ToString (s : RawId) : String :=
  match s with
  | .name str => str
  | .anonymous i => s!"{i}"

instance : ToString RawId where
  toString := RawId.ToString


inductive Identifier : Type where
  | global_id (id : RawId) -- @id
  | local_id (id : RawId) -- %id
deriving Repr, DecidableEq

deriving instance Hashable for Identifier

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
  | function (ret : LlvmRetType) (args : List LlvmType)
deriving Repr

end

@[simp]
def LlvmRetType.isVoid? : LlvmRetType φ -> Bool
  | .void => true
  | .ret _ => false

@[simp]
def LlvmRetType.asRet? : LlvmRetType φ -> Option (LlvmType φ)
  | .void => none
  | .ret ty => some ty

@[simp]
def LlvmType.asInt? : LlvmType φ -> Option (Width φ)
  | .int w => some w
  | _ => none

@[simp]
def LlvmType.asFunction? : LlvmType φ -> Option ((LlvmRetType φ) × List (LlvmType φ))
  | .function ret argTys => some (ret, argTys)
  | _ => none

end

def LlvmType.i (w : Width φ) : LlvmType φ := .int w

abbrev LlvmType.i1 : LlvmType φ := .i 1
abbrev LlvmType.i32 : LlvmType φ := .i 32

mutual

@[simp]
def LlvmRetType.instantiateWidths (ws : List.Vector Nat φ) : LlvmRetType φ → LlvmRetType 0
  | .void => .void
  | .ret ty => .ret <| ty.instantiateWidths ws

@[simp]
def LlvmType.instantiateWidths (ws : List.Vector Nat φ) : LlvmType φ → LlvmType 0
  | .int w => .int <| Width.instantiate ws w
  | .function ret args => .function (ret.instantiateWidths ws) (args.map (LlvmType.instantiateWidths ws))

end


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
  | undef      (id: RawId)
  | poison
deriving Repr

abbrev TypedExp φ := LlvmType φ × Exp

section

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

structure TopLevel (φ: Nat) where
  (entities : List (@TopLevelEntity φ))

@[simp]
def TypedExp.instantiateWidths (ws : List.Vector Nat φ) : TypedExp φ → TypedExp 0
  | (ty, exp) => (ty.instantiateWidths ws, exp)

@[simp]
def Instruction.instantiateWidths (ws : List.Vector Nat φ) : @Instruction φ → @Instruction 0
  | .intBinaryOp op t v1 v2 => .intBinaryOp op (t.instantiateWidths ws) v1 v2
  | .conversionOp op fromTy v toTy => .conversionOp op (fromTy.instantiateWidths ws) v (toTy.instantiateWidths ws)
  | .freeze (ty, v) => .freeze (ty.instantiateWidths ws, v)

@[simp]
def Terminator.instantiateWidths (ws : List.Vector Nat φ) : @Terminator φ → @Terminator 0
  | .retVoid => .retVoid
  | .ret tv => .ret <| tv.instantiateWidths ws

@[simp]
def Declaration.instantiateWidths (ws : List.Vector Nat φ) : @Declaration φ → @Declaration 0
  | ⟨name, type⟩ => ⟨name, type.instantiateWidths ws⟩

@[simp]
def Code.instantiateWidths (ws : List.Vector Nat φ) : @Code φ → @Code 0
  | code => code.map fun (instrId, instr) => (instrId, instr.instantiateWidths ws)

@[simp]
def Block.instantiateWidths (ws : List.Vector Nat φ) : @Block φ → @Block 0
  | ⟨id, code, terminator⟩ => ⟨id, code.instantiateWidths ws, (terminator.fst, terminator.snd.instantiateWidths ws)⟩

@[simp]
def Definition.instantiateWidths (ws : List.Vector Nat φ) : @Definition φ → @Definition 0
  | ⟨prototype, args, body⟩ => ⟨prototype.instantiateWidths ws, args, body.instantiateWidths ws⟩

@[simp]
def TopLevelEntity.instantiateWidths (ws : List.Vector Nat φ) : @TopLevelEntity φ → @TopLevelEntity 0
  | .declaration decl => .declaration <| decl.instantiateWidths ws
  | .definition defn => .definition <| defn.instantiateWidths ws

@[simp]
def TopLevel.instantiateWidths (ws : List.Vector Nat φ) : @TopLevel φ → @TopLevel 0
  | ⟨entities⟩ => ⟨entities.map (TopLevelEntity.instantiateWidths ws)⟩

end

end LeanNanoLlvm.AST
