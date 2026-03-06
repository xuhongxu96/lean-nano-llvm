import LeanNanoLlvm.Semantics.Denote
import LeanNanoLlvm.Tactic

namespace LeanNanoLlvm
namespace AST

variable {φ : Nat}

@[simp_wellform]
def Exp.WellFormedFor (ty : LlvmType φ) : Exp → Prop
  | .identifier (.local_id _) => ty.asInt?.isSome
  | .identifier (.global_id _) => False
  | .bool _ => ty = LlvmType.i1
  | .int _ => ty.asInt?.isSome
  | .null => False
  | .undef _ => ty.asInt?.isSome
  | .poison => ty.asInt?.isSome

@[simp_wellform]
def Exp.WellScopedTo (locals : List LocalId) : Exp → Prop
  | .identifier (.local_id id) => id ∈ locals
  | .identifier (.global_id _) => False
  | _ => True

@[simp_wellform]
def InstructionId.DefinesLocal : InstructionId → Prop
  | .id _ => True
  | .void _ => False

@[simp_wellform]
def Code.definedIds : @Code φ → List LocalId
  | [] => []
  | (instrId, _) :: rest =>
      match instrId with
      | .id id => id :: Code.definedIds rest
      | .void _ => Code.definedIds rest

@[simp_wellform]
def Width.CanTruncateTo (fromW toW : Width φ) : Prop :=
  match fromW.toNat?, toW.toNat? with
  | some fromW, some toW => toW < fromW
  | _, _ => True

@[simp_wellform]
def Width.CanExtendTo (fromW toW : Width φ) : Prop :=
  match fromW.toNat?, toW.toNat? with
  | some fromW, some toW => fromW < toW
  | _, _ => True

@[simp_wellform]
def Instruction.WellFormedWith (locals : List LocalId) (instrId : InstructionId) :
    @Instruction φ → Prop
  | .intBinaryOp _ (.int w) v1 v2 =>
      instrId.DefinesLocal
      ∧ v1.WellFormedFor (.int w)
      ∧ v2.WellFormedFor (.int w)
      ∧ v1.WellScopedTo locals
      ∧ v2.WellScopedTo locals
  | .intBinaryOp _ _ _ _ => False
  | .conversionOp op (.int fromW) v (.int toW) =>
      instrId.DefinesLocal
      ∧ v.WellFormedFor (.int fromW)
      ∧ v.WellScopedTo locals
      ∧ match op with
        | .trunc _ _ => fromW.CanTruncateTo toW
        | .zext _ => fromW.CanExtendTo toW
        | .sext => fromW.CanExtendTo toW
  | .conversionOp _ _ _ _ => False
  | .freeze ⟨.int w, v⟩ =>
      instrId.DefinesLocal
      ∧ v.WellFormedFor (.int w)
      ∧ v.WellScopedTo locals
  | .freeze _ => False

@[simp_wellform]
def Code.WellFormedFrom (locals : List LocalId) : @Code φ → Prop
  | [] => True
  | (instrId, instr) :: rest =>
      instr.WellFormedWith locals instrId
      ∧ match instrId with
        | .id id => id ∉ locals ∧ Code.WellFormedFrom (id :: locals) rest
        | .void _ => False

@[simp_wellform]
def Terminator.WellFormedWith (retTy : LlvmRetType φ) (locals : List LocalId) :
    (InstructionId × @Terminator φ) → Prop
  | (.void _, .retVoid) => retTy = .void
  | (.void _, .ret ⟨ty, exp⟩) =>
      retTy = .ret ty
      ∧ exp.WellFormedFor ty
      ∧ exp.WellScopedTo locals
  | _ => False

@[simp_wellform]
def Declaration.WellFormedType : LlvmType φ → Prop
  | .function retTy argTys =>
      (retTy.isVoid? ∨ (∃ retRetTy, retTy.asRet? = some retRetTy ∧ retRetTy.asInt?.isSome))
      ∧ (∀ argTy ∈ argTys, argTy.asFunction?.isNone)
  | _ => False

inductive Declaration.WellFormed (decl : @Declaration φ) : Prop where
  | mk : Declaration.WellFormedType decl.type → WellFormed decl

inductive Definition.WellFormed (defn : @Definition φ) : Prop where
  | mk (retTy : LlvmRetType φ) (argTys : List (LlvmType φ)) :
    defn.prototype.WellFormed →
    defn.prototype.type = LlvmType.function retTy argTys →
    defn.args.length = argTys.length →
    defn.args.Nodup →
    defn.body.code.WellFormedFrom defn.args →
    Terminator.WellFormedWith retTy (defn.args ++ Code.definedIds defn.body.code) defn.body.terminator →
    WellFormed defn

@[simp_wellform]
theorem declaration_wellFormed_iff (decl : @Declaration φ) :
    decl.WellFormed ↔ Declaration.WellFormedType decl.type := by
  constructor
  . intro h
    cases h with
    | mk h => exact h
  . intro h
    exact .mk h


@[simp_wellform]
theorem definition_wellFormed_iff (defn : @Definition φ) :
    defn.WellFormed ↔
      ∃ retTy argTys,
        defn.prototype.WellFormed
        ∧ defn.prototype.type = LlvmType.function retTy argTys
        ∧ defn.args.length = argTys.length
        ∧ defn.args.Nodup
        ∧ defn.body.code.WellFormedFrom defn.args
        ∧ Terminator.WellFormedWith retTy (defn.args ++ Code.definedIds defn.body.code) defn.body.terminator := by
  constructor
  . intro h
    cases h with
    | mk retTy argTys hproto htype hlen hnodup hcode hterm =>
      exact ⟨retTy, argTys, hproto, htype, hlen, hnodup, hcode, hterm⟩
  . rintro ⟨retTy, argTys, hproto, htype, hlen, hnodup, hcode, hterm⟩
    exact .mk retTy argTys hproto htype hlen hnodup hcode hterm

end AST

end LeanNanoLlvm
