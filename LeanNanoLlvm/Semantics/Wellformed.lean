import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.Semantics.Value
import LeanNanoLlvm.Tactic

namespace LeanNanoLlvm
namespace AST

@[simp_wellform]
def Exp.WellFormedFor (cfg : SemanticsConfig := .modern) (ty : LlvmType) : Exp → Prop
  | .identifier (.local_id _) => ty.isFirstClass = true
  | .identifier (.global_id _) => ty.asPtr?.isSome = true
  | .bool _ => ty = LlvmType.i1
  | .int _ => ty.asInt?.isSome = true
  | .floatBits _ => ty.asFloat?.isSome = true
  | .floatDec _ _ _ => ty.asFloat?.isSome = true
  | .null => ty.asPtr?.isSome = true
  | .zeroinitializer => ty.isFirstClass = true
  | .undef => cfg.allowUndef = true ∧ ty.isFirstClass = true
  | .poison => ty.isFirstClass = true
  | .array elems =>
      match ty with
      | .array n elemTy => elems.length = n ∧ ∀ p ∈ elems, p.1 = elemTy
      | _ => False
  | .struct packed fields =>
      match ty with
      | .struct p fTys => p = packed ∧ fields.length = fTys.length
      | _ => False
  | .vector elems =>
      match ty with
      | .vector n elemTy => elems.length = n ∧ ∀ p ∈ elems, p.1 = elemTy
      | _ => False
  | .splat (eTy, _) =>
      match ty with
      | .vector _ elemTy => eTy = elemTy
      | _ => False
  | .gepConst _ _ _ _ => ty.isPtrOrPtrVector = true
  | .convConst _ _ _ toTy => ty = toTy
  | .binConst _ cTy _ _ => ty = cTy

mutual
@[simp_wellform]
def Exp.WellScopedTo (locals : List LocalId) : Exp → Prop
  | .identifier (.local_id id) => id ∈ locals
  | .identifier (.global_id _) => True
  | .array elems => Exp.TypedListWellScopedTo locals elems
  | .struct _ fields => Exp.TypedListWellScopedTo locals fields
  | .vector elems => Exp.TypedListWellScopedTo locals elems
  | .splat (_, e) => e.WellScopedTo locals
  | .gepConst _ _ (_, p) idxs => p.WellScopedTo locals ∧ Exp.TypedListWellScopedTo locals idxs
  | .convConst _ _ v _ => v.WellScopedTo locals
  | .binConst _ _ v1 v2 => v1.WellScopedTo locals ∧ v2.WellScopedTo locals
  | _ => True

@[simp_wellform]
def Exp.TypedListWellScopedTo (locals : List LocalId) : List (LlvmType × Exp) → Prop
  | [] => True
  | (_, e) :: rest => e.WellScopedTo locals ∧ Exp.TypedListWellScopedTo locals rest
end

@[simp_wellform]
def InstructionId.DefinesLocal : InstructionId → Prop
  | .id _ => True
  | .void _ => False

@[simp_wellform]
def InstructionId.IsVoid : InstructionId → Prop
  | .id _ => False
  | .void _ => True

@[simp_wellform]
def Code.definedIds : Code → List LocalId
  | [] => []
  | (instrId, _) :: rest =>
      match instrId with
      | .id id => id :: Code.definedIds rest
      | .void _ => Code.definedIds rest

@[simp_wellform]
def Instruction.WellFormedWith (cfg : SemanticsConfig) (locals : List LocalId)
    (labels : List BlockId) (instrId : InstructionId) : Instruction → Prop
  | .intBinaryOp _ ty v1 v2 =>
      instrId.DefinesLocal
      ∧ ty.isIntOrIntVector = true
      ∧ v1.WellFormedFor cfg ty
      ∧ v2.WellFormedFor cfg ty
      ∧ v1.WellScopedTo locals
      ∧ v2.WellScopedTo locals
  | .floatUnaryOp _ ty v =>
      instrId.DefinesLocal
      ∧ ty.isFloatOrFloatVector = true
      ∧ v.WellFormedFor cfg ty
      ∧ v.WellScopedTo locals
  | .floatBinaryOp _ ty v1 v2 =>
      instrId.DefinesLocal
      ∧ ty.isFloatOrFloatVector = true
      ∧ v1.WellFormedFor cfg ty
      ∧ v2.WellFormedFor cfg ty
      ∧ v1.WellScopedTo locals
      ∧ v2.WellScopedTo locals
  | .icmp _ _ ty v1 v2 =>
      instrId.DefinesLocal
      ∧ (ty.isIntOrIntVector = true ∨ ty.isPtrOrPtrVector = true)
      ∧ v1.WellFormedFor cfg ty
      ∧ v2.WellFormedFor cfg ty
      ∧ v1.WellScopedTo locals
      ∧ v2.WellScopedTo locals
  | .fcmp _ _ ty v1 v2 =>
      instrId.DefinesLocal
      ∧ ty.isFloatOrFloatVector = true
      ∧ v1.WellFormedFor cfg ty
      ∧ v2.WellFormedFor cfg ty
      ∧ v1.WellScopedTo locals
      ∧ v2.WellScopedTo locals
  | .conversionOp op fromTy v toTy =>
      instrId.DefinesLocal
      ∧ v.WellFormedFor cfg fromTy
      ∧ v.WellScopedTo locals
      ∧ match op with
        | .trunc _ _ =>
          match fromTy.scalarType, toTy.scalarType with
          | .int fromW, .int toW => toW < fromW
          | _, _ => False
        | .zext _ | .sext =>
          match fromTy.scalarType, toTy.scalarType with
          | .int fromW, .int toW => fromW < toW
          | _, _ => False
        | .fptrunc _ =>
          match fromTy.scalarType, toTy.scalarType with
          | .float f1, .float f2 => f2.bitWidth < f1.bitWidth
          | _, _ => False
        | .fpext _ =>
          match fromTy.scalarType, toTy.scalarType with
          | .float f1, .float f2 => f1.bitWidth < f2.bitWidth
          | _, _ => False
        | .fptoui | .fptosi =>
          fromTy.isFloatOrFloatVector = true ∧ toTy.isIntOrIntVector = true
        | .uitofp _ _ | .sitofp _ =>
          fromTy.isIntOrIntVector = true ∧ toTy.isFloatOrFloatVector = true
        | .ptrtoint | .ptrtoaddr =>
          fromTy.isPtrOrPtrVector = true ∧ toTy.isIntOrIntVector = true
        | .inttoptr =>
          fromTy.isIntOrIntVector = true ∧ toTy.isPtrOrPtrVector = true
        | .bitcast =>
          fromTy.isFirstClass = true ∧ toTy.isFirstClass = true
        | .addrspacecast =>
          fromTy.isPtrOrPtrVector = true ∧ toTy.isPtrOrPtrVector = true
  | .select _ condTy cond valTy tv fv =>
      instrId.DefinesLocal
      ∧ (condTy = .i1 ∨ ∃ n, condTy = .vector n .i1)
      ∧ valTy.isFirstClass = true
      ∧ cond.WellFormedFor cfg condTy ∧ cond.WellScopedTo locals
      ∧ tv.WellFormedFor cfg valTy ∧ tv.WellScopedTo locals
      ∧ fv.WellFormedFor cfg valTy ∧ fv.WellScopedTo locals
  | .phi ty _ incoming _ =>
      instrId.DefinesLocal
      ∧ ty.isFirstClass = true
      ∧ incoming ≠ []
      ∧ ∀ p ∈ incoming, p.1.WellFormedFor cfg ty ∧ p.2 ∈ labels
  | .alloca allocTy numEl? _ _ =>
      instrId.DefinesLocal
      ∧ allocTy.isFirstClass = true
      ∧ match numEl? with
        | none => True
        | some (nTy, nExp) => nTy.asInt?.isSome = true ∧ nExp.WellFormedFor cfg nTy ∧ nExp.WellScopedTo locals
  | .load ty ptrTy ptr _ _ _ _ =>
      instrId.DefinesLocal
      ∧ ty.isFirstClass = true
      ∧ ptrTy.asPtr?.isSome = true
      ∧ ptr.WellFormedFor cfg ptrTy
      ∧ ptr.WellScopedTo locals
  | .store valTy val ptrTy ptr _ _ =>
      instrId.IsVoid
      ∧ valTy.isFirstClass = true
      ∧ ptrTy.asPtr?.isSome = true
      ∧ val.WellFormedFor cfg valTy ∧ val.WellScopedTo locals
      ∧ ptr.WellFormedFor cfg ptrTy ∧ ptr.WellScopedTo locals
  | .getelementptr _ baseTy ptrTy ptr idxs =>
      instrId.DefinesLocal
      ∧ baseTy.isFirstClass = true
      ∧ ptrTy.isPtrOrPtrVector = true
      ∧ ptr.WellFormedFor cfg ptrTy ∧ ptr.WellScopedTo locals
      ∧ ∀ p ∈ idxs, p.1.isIntOrIntVector = true ∧ p.2.WellFormedFor cfg p.1 ∧ p.2.WellScopedTo locals
  | .extractvalue aggTy agg idxs =>
      instrId.DefinesLocal
      ∧ agg.WellFormedFor cfg aggTy ∧ agg.WellScopedTo locals
      ∧ idxs ≠ []
  | .insertvalue aggTy agg valTy val idxs =>
      instrId.DefinesLocal
      ∧ agg.WellFormedFor cfg aggTy ∧ agg.WellScopedTo locals
      ∧ val.WellFormedFor cfg valTy ∧ val.WellScopedTo locals
      ∧ idxs ≠ []
  | .extractelement vecTy vec idxTy idx =>
      instrId.DefinesLocal
      ∧ vecTy.asVector?.isSome = true
      ∧ idxTy.asInt?.isSome = true
      ∧ vec.WellFormedFor cfg vecTy ∧ vec.WellScopedTo locals
      ∧ idx.WellFormedFor cfg idxTy ∧ idx.WellScopedTo locals
  | .insertelement vecTy vec valTy val idxTy idx =>
      instrId.DefinesLocal
      ∧ vecTy.asVector?.isSome = true
      ∧ idxTy.asInt?.isSome = true
      ∧ vec.WellFormedFor cfg vecTy ∧ vec.WellScopedTo locals
      ∧ val.WellFormedFor cfg valTy ∧ val.WellScopedTo locals
      ∧ idx.WellFormedFor cfg idxTy ∧ idx.WellScopedTo locals
  | .shufflevector vecTy v1 v2 mask =>
      instrId.DefinesLocal
      ∧ vecTy.asVector?.isSome = true
      ∧ mask ≠ []
      ∧ v1.WellFormedFor cfg vecTy ∧ v1.WellScopedTo locals
      ∧ v2.WellFormedFor cfg vecTy ∧ v2.WellScopedTo locals
  | .call retTy _ callee args _ _ _ =>
      (match retTy with | .void => instrId.IsVoid | .ret _ => True)
      ∧ callee.WellScopedTo locals
      ∧ ∀ a ∈ args, a.2.1.WellFormedFor cfg a.1 ∧ a.2.1.WellScopedTo locals
  | .freeze ⟨ty, v⟩ =>
      instrId.DefinesLocal
      ∧ ty.isFirstClass = true
      ∧ v.WellFormedFor cfg ty
      ∧ v.WellScopedTo locals

@[simp_wellform]
def Code.WellFormedFrom (cfg : SemanticsConfig) (locals : List LocalId)
    (labels : List BlockId) : Code → Prop
  | [] => True
  | (instrId, instr) :: rest =>
      instr.WellFormedWith cfg locals labels instrId
      ∧ match instrId with
        | .id id => id ∉ locals ∧ Code.WellFormedFrom cfg (id :: locals) labels rest
        | .void _ => Code.WellFormedFrom cfg locals labels rest

@[simp_wellform]
def Terminator.WellFormedWith (cfg : SemanticsConfig) (retTy : LlvmRetType)
    (locals : List LocalId) (labels : List BlockId) :
    (InstructionId × Terminator) → Prop
  | (.void _, .retVoid) => retTy = .void
  | (.void _, .ret ⟨ty, exp⟩) =>
      retTy = .ret ty
      ∧ exp.WellFormedFor cfg ty
      ∧ exp.WellScopedTo locals
  | (.void _, .br dest) => dest ∈ labels
  | (.void _, .condBr cond tDest fDest) =>
      cond.WellFormedFor cfg .i1
      ∧ cond.WellScopedTo locals
      ∧ tDest ∈ labels ∧ fDest ∈ labels
  | (.void _, .switch ty cond defDest cases) =>
      ty.asInt?.isSome = true
      ∧ cond.WellFormedFor cfg ty
      ∧ cond.WellScopedTo locals
      ∧ defDest ∈ labels
      ∧ ∀ c ∈ cases, c.2 ∈ labels
  | (.void _, .unreachable) => True
  | _ => False

@[simp_wellform]
def Declaration.WellFormedType : LlvmType → Prop
  | .function retTy argTys _ =>
      (retTy.isVoid? ∨ (∃ retRetTy, retTy.asRet? = some retRetTy ∧ retRetTy.isFirstClass = true))
      ∧ (∀ argTy ∈ argTys, argTy.isFirstClass = true)
  | _ => False

inductive Declaration.WellFormed (decl : Declaration) : Prop where
  | mk : Declaration.WellFormedType decl.type → WellFormed decl

@[simp_wellform]
def Block.WellFormedWith (cfg : SemanticsConfig) (retTy : LlvmRetType)
    (allLocals : List LocalId) (labels : List BlockId) (blk : Block) : Prop :=
  blk.code.WellFormedFrom cfg allLocals labels
  ∧ Terminator.WellFormedWith cfg retTy (allLocals ++ Code.definedIds blk.code) labels blk.terminator

/-- Config-aware well-formedness for single-block and multi-block LLVM definitions. -/
inductive Definition.WellFormedWith (cfg : SemanticsConfig) (defn : Definition) : Prop where
  | mk (retTy : LlvmRetType) (argTys : List LlvmType) (isVarArg : Bool) :
    defn.prototype.WellFormed →
    defn.prototype.type = LlvmType.function retTy argTys isVarArg →
    defn.args.length = argTys.length →
    defn.args.Nodup →
    defn.blocks ≠ [] →
    (defn.blocks.map Block.id).Nodup →
    (match defn.blocks with
      | [single] =>
          single.code.WellFormedFrom cfg defn.args [single.id]
          ∧ Terminator.WellFormedWith cfg retTy (defn.args ++ Code.definedIds single.code) [single.id] single.terminator
      | blks =>
          let labels := blks.map Block.id
          let allDefined := defn.args ++ (blks.flatMap fun b => Code.definedIds b.code)
          allDefined.Nodup ∧
          ∀ b ∈ blks,
            b.code.WellFormedFrom cfg (allDefined.filter (· ∉ Code.definedIds b.code)) labels
            ∧ Terminator.WellFormedWith cfg retTy allDefined labels b.terminator) →
    WellFormedWith cfg defn

/-- Default well-formedness (`undef` disabled, matching modern LLVM). -/
abbrev Definition.WellFormed (defn : Definition) : Prop :=
  Definition.WellFormedWith .modern defn

@[simp_wellform]
theorem declaration_wellFormed_iff (decl : Declaration) :
    decl.WellFormed ↔ Declaration.WellFormedType decl.type := by
  constructor
  · intro h; cases h with | mk h => exact h
  · intro h; exact .mk h

@[simp_wellform]
theorem definition_wellFormedWith_iff (cfg : SemanticsConfig) (defn : Definition) :
    defn.WellFormedWith cfg ↔
      ∃ retTy argTys isVarArg,
        defn.prototype.WellFormed
        ∧ defn.prototype.type = LlvmType.function retTy argTys isVarArg
        ∧ defn.args.length = argTys.length
        ∧ defn.args.Nodup
        ∧ defn.blocks ≠ []
        ∧ (defn.blocks.map Block.id).Nodup
        ∧ (match defn.blocks with
            | [single] =>
                single.code.WellFormedFrom cfg defn.args [single.id]
                ∧ Terminator.WellFormedWith cfg retTy (defn.args ++ Code.definedIds single.code) [single.id] single.terminator
            | blks =>
                let labels := blks.map Block.id
                let allDefined := defn.args ++ (blks.flatMap fun b => Code.definedIds b.code)
                allDefined.Nodup ∧
                ∀ b ∈ blks,
                  b.code.WellFormedFrom cfg (allDefined.filter (· ∉ Code.definedIds b.code)) labels
                  ∧ Terminator.WellFormedWith cfg retTy allDefined labels b.terminator) := by
  constructor
  · intro h
    cases h with
    | mk retTy argTys isVarArg hproto htype hlen hnodup hne hblks hbody =>
      exact ⟨retTy, argTys, isVarArg, hproto, htype, hlen, hnodup, hne, hblks, hbody⟩
  · rintro ⟨retTy, argTys, isVarArg, hproto, htype, hlen, hnodup, hne, hblks, hbody⟩
    exact .mk retTy argTys isVarArg hproto htype hlen hnodup hne hblks hbody

@[simp_wellform]
theorem definition_wellFormed_iff (defn : Definition) :
    defn.WellFormed ↔ defn.WellFormedWith .modern := Iff.rfl

end AST

namespace Semantics

mutual
@[simp_wellform]
def RegisterValue.WellFormedFor : AST.LlvmType → RegisterValue → Prop
  | .int wTy, .bv wVal _ => wTy = wVal
  | .float ft1, .float ft2 _ => ft1 = ft2
  | .ptr as1, .ptr as2 _ => as1 = as2
  | .vector n elemTy, .vector _ elems =>
      elems.length = n ∧ RegisterValue.WellFormedForUniform elemTy elems
  | .array n elemTy, .array _ elems =>
      elems.length = n ∧ RegisterValue.WellFormedForUniform elemTy elems
  | .struct p1 fTys, .struct p2 _ fields =>
      p1 = p2 ∧ RegisterValue.WellFormedForList fTys fields
  | _, _ => False

@[simp_wellform]
def RegisterValue.WellFormedForUniform (elemTy : AST.LlvmType) : List RegisterValue → Prop
  | [] => True
  | e :: es => RegisterValue.WellFormedFor elemTy e ∧ RegisterValue.WellFormedForUniform elemTy es

@[simp_wellform]
def RegisterValue.WellFormedForList : List AST.LlvmType → List RegisterValue → Prop
  | [], [] => True
  | t :: ts, v :: vs => RegisterValue.WellFormedFor t v ∧ RegisterValue.WellFormedForList ts vs
  | _, _ => False
end

@[simp_wellform]
def Definition.ArgValuesWellFormed (defn : AST.Definition) (argVals : List RegisterValue) : Prop :=
  match defn.prototype.type with
  | .function _ argTys _ => RegisterValue.WellFormedForList argTys argVals
  | _ => False

end Semantics

end LeanNanoLlvm
