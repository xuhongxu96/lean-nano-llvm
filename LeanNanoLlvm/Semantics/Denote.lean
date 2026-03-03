import LeanNanoLlvm.Semantics.Semantics
import LeanNanoLlvm.Semantics.State
import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.Print

namespace LeanNanoLlvm.Semantics

open Std

variable {φ : Nat}

def denoteIntBinaryOp {w : Nat} (op : AST.IntBinaryOp) (x y : IntW w) : IntW w :=
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

def denoteExp : AST.Exp → NanoLlvmStateM (IntW w)
  | .identifier id => do
    let st ← get
    match st.registers.get? id with
    | some val => match val with
      | .bv w' val =>
        if h: w = w' then
          pure (h ▸ val)
        else
          throw s!"invalid width: expected [{w}], found [{w'}]"
    | none => throw s!"unknown id [{id.print}]"
  | .bool b =>
    if w = 1 then pure (pure b.toNat)
    else throw s!"invalid width: expected [{w}], found [1] (bool)"
  | .int x => pure (pure x)
  | .null => throw s!"`null` exp is not supported yet"
  | .undef => throw s!"`undef` exp is not supported yet"
  | .poison => pure .poison

def denoteInstruction (id : AST.InstructionId) : (@AST.Instruction φ) → NanoLlvmStateM Unit
  | .intBinaryOp op t v1 v2 => do
    match t with
    | .int w =>
      match id with
      | .id id =>
        let v1 ← @denoteExp w v1
        let v2 ← @denoteExp w v2
        let res := denoteIntBinaryOp op v1 v2
        let st ← get
        let st' := {st with registers := (st.registers.insert (.local_id id) (.bv w res))}
        set st'
      | .void _ => throw s!"IntBinaryOp should be assigned with an instruction id"
    | _ => throw s!"Expected int type, but found [{t.print}]"
  | .conversionOp op fromTy v toTy => throw s!"conversion op is not supported yet"
  | .freeze ⟨ty, exp⟩ => throw s!"`freeze` instruction is not supported yet"

def denoteNanoLlvmCode : (@AST.Code φ) → NanoLlvmStateM Unit
  | .nil => pure ()
  | ⟨instr_id, instr⟩ :: t => do
    denoteInstruction instr_id instr
    denoteNanoLlvmCode t

end LeanNanoLlvm.Semantics
