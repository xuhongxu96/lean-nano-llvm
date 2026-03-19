import LeanNanoLlvm.Semantics.Semantics
import LeanNanoLlvm.Semantics.State
import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.Print

namespace LeanNanoLlvm.Semantics

open Std

variable {φ : Nat}


@[simp]
def UndefMToStateT {α : Type} [Inhabited α] (a : UndefM α α) :
    StateT (SupplyState α) (Except String) α := fun st =>
  match a.run st with
  | .ok res => pure res
  | .error _ => throw ""

@[simp_llvm]
def genUndef {w : Nat} : NanoLlvmStateM (BitVec w) := do
  let n : Nat ← StateT.lift <| UndefMToStateT (UndefM.undef : UndefM Nat Nat)
  pure (BitVec.ofNat w n)

@[simp_llvm]
private def expectConcreteWidth : AST.Width φ → NanoLlvmStateM Nat
  | .concrete w => pure w
  | .mvar i => throw s!"symbolic width {AST.Width.print (.mvar i)} is not executable; instantiate widths first"

@[simp_llvm]
def evalIntBinaryOp {w : Nat} (op : AST.IntBinaryOp) (x y : IntW w) : IntW w :=
  match op with
  | .add nuw nsw => add x y { nuw := nuw, nsw := nsw }
  | .sub nuw nsw => sub x y { nuw := nuw, nsw := nsw }
  | .mul nuw nsw => mul x y { nuw := nuw, nsw := nsw }
  | .shl nuw nsw => shl x y { nuw := nuw, nsw := nsw }
  | .udiv exact  => udiv x y { exact := exact }
  | .sdiv exact  => sdiv x y { exact := exact }
  | .lshr exact  => lshr x y { exact := exact }
  | .ashr exact  => ashr x y { exact := exact }
  | .urem        => urem x y
  | .srem        => srem x y
  | .and         => Semantics.and x y
  | .or disjoint => Semantics.or x y { disjoint := disjoint }
  | .xor         => xor x y

@[simp_llvm]
def evalConversionOp {fromW toW : Nat} (op : AST.ConversionOp) (v : IntW fromW) : IntW toW :=
  match op with
  | .trunc nuw nsw => trunc toW v { nuw := nuw, nsw := nsw }
  | .zext nneg     => zext toW v { nneg := nneg }
  | .sext          => sext toW v

@[simp_llvm]
def evalExp : AST.Exp → NanoLlvmStateM (IntW w)
  | .identifier id => do
    let st ← get
    match st.registers.get? id with
    | some val => match val with
      | .bv w' val =>
        if h: w = w' then
          pure (h ▸ val)
        else
          throw s!"invalid width: expected [{w}], found [{w'}]"
      | _ => throw s!"unsupported void value"
    | none => throw s!"unknown id [{id.print}]"
  | .bool b =>
    if w = 1 then pure (pure b.toNat)
    else throw s!"invalid width: expected [{w}], found [1] (bool)"
  | .int x => pure (pure x)
  | .null => throw s!"`null` exp is not supported yet"
  | .undef _rawid => do
    pure (.value (← genUndef))
  | .poison => pure .poison

@[simp_llvm]
def evalInstruction (id : AST.InstructionId) : (@AST.Instruction φ) → NanoLlvmStateM Unit
  | .intBinaryOp op t v1 v2 => do
    match t with
    | .int w =>
      let w ← expectConcreteWidth w
      match id with
      | .id id =>
        let v1 ← @evalExp w v1
        let v2 ← @evalExp w v2
        let res := evalIntBinaryOp op v1 v2
        let st ← get
        let st' := {st with registers := (st.registers.insert (.local_id id) (.bv w res))}
        set st'
      | .void _ => throw s!"IntBinaryOp should be assigned with an instruction id"
    | _ => throw s!"Expected int type, but found [{t.print}]"
  | .conversionOp op fromTy v toTy => do
    match fromTy, toTy with
    | .int fromW, .int toW =>
      let fromW ← expectConcreteWidth fromW
      let toW ← expectConcreteWidth toW
      match id with
      | .id id =>
        let v ← @evalExp fromW v
        let res : IntW toW := evalConversionOp op v
        let st ← get
        let st' := { st with registers := (st.registers.insert (.local_id id) (.bv toW res)) }
        set st'
      | .void _ => throw s!"ConversionOp should be assigned with an instruction id"
    | _, _ => throw s!"Expected int type in conversion op, but found from=[{fromTy.print}], to=[{toTy.print}]"
  | .freeze ⟨ty, exp⟩ => do
    let id ← match id with
    | .id id => pure id
    | _ => throw s!"freeze should be assigned with an instruction id"

    match ty with
    | .int w =>
      let w ← expectConcreteWidth w
      let exp ← @evalExp w exp
      let res := freeze exp
      let st ← get
      let st' := { st with registers := (st.registers.insert (.local_id id) (.bv w res)) }
      set st'
    | _ => throw s!"Expected int type for freeze op, but found [{ty.print}]"

@[simp_llvm]
def evalNanoLlvmCode : (@AST.Code φ) → NanoLlvmStateM Unit
  | .nil => pure ()
  | ⟨instr_id, instr⟩ :: t => do
    evalInstruction instr_id instr
    evalNanoLlvmCode t

@[simp_llvm]
def bindDefinitionArgs :
    List (AST.LlvmType φ) → List AST.RawId → List RegisterValue → NanoLlvmStateM Unit
  | [], [], [] => pure ()
  | [], _, _ => throw s!"unmatched number of argument types, ids and values"
  | _, [], _ => throw s!"unmatched number of argument types, ids and values"
  | _, _, [] => throw s!"unmatched number of argument types, ids and values"
  | (argTy :: restTys), (argId :: restIds), (argVal :: restVals) => do
      match argTy, argVal with
      | .int wTy, .bv wVal _v =>
        let wTy ← expectConcreteWidth wTy
        if wTy = wVal then
          let st ← get
          let registers := st.registers.insert (.local_id argId) argVal
          set { st with registers := registers }
        else
          throw s!"unmatched argument integer width: [{argTy.print} {argId} = {argVal}]"
      | _, _ => throw s!"unsupported argument: [{argTy.print} {argId} = {argVal}]"
      bindDefinitionArgs restTys restIds restVals

@[simp_llvm]
def evalNanoLlvmDefinition : (@AST.Definition φ) → List RegisterValue → NanoLlvmStateM RegisterValue
  | ⟨proto, argIds, body⟩, argVals =>
    match proto.type with
    | .function retTy argTys => do
      bindDefinitionArgs argTys argIds argVals

      evalNanoLlvmCode body.code

      match body.terminator with
      | ⟨_termId, term⟩ => match term with
        | .retVoid =>
          match retTy with
          | .void => pure .void
          | _ => throw s!"Expected [{retTy.print}] as return type, but found void"
        | .ret ⟨.int w, exp⟩ =>
          let w ← expectConcreteWidth w
          match retTy with
          | .ret (.int retW) =>
            let retW ← expectConcreteWidth retW
            if h : retW = w then
              let exp ← @evalExp w exp
              pure (.bv w (h ▸ exp))
            else
              throw s!"Expected [{retTy.print}] as return type, but found [i{w}]"
          | _ => throw s!"Expected [{retTy.print}] as return type, but found [i{w}]"
        | _ => throw s!"unsupported return: [{term.print}]"
    | ty => throw s!"Expected function type for the prototype of definition, but found [{ty.print}]"

@[simp_llvm]
def evalInstantiatedDefinition (ws : List.Vector Nat φ) (defn : @AST.Definition φ)
    (argVals : List RegisterValue) : NanoLlvmStateM RegisterValue :=
  evalNanoLlvmDefinition (defn.instantiateWidths ws) argVals

@[simp_llvm]
def runInstantiatedDefinition (ws : List.Vector Nat φ) (defn : @AST.Definition φ)
    (args : List RegisterValue) (st : NanoLlvmState := default) : Except String RegisterValue := do
  runNanoLlvmStateM (evalInstantiatedDefinition ws defn args) st

@[simp_llvm]
def runInstantiatedDefinitionWithUndef (ws : List.Vector Nat φ) (defn : @AST.Definition φ)
    (args : List RegisterValue) (st : NanoLlvmState := default) (uState : UndefState := default)
    : Except String RegisterValue :=
  runNanoLlvmStateM (evalInstantiatedDefinition ws defn args) st uState

end LeanNanoLlvm.Semantics
