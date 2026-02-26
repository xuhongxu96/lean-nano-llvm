import LeanNanoLlvm.AST.AST

namespace LeanNanoLlvm.AST

def Identifier.print : Identifier → String
  | .global_id id => s!"@{id.ToString}"
  | .local_id id => s!"%{id.ToString}"

def LlvmType.print : LlvmType φ → String
  | .int w => s!"{w}"
  | .function .. => unreachable!

def LlvmRetType.print : LlvmRetType φ → String
  | .void => "void"
  | .ret t => t.print

def Exp.print : Exp → String
  | .identifier id => id.print
  | .bool b => s!"{b}"
  | .int i => s!"{i}"
  | .null => "null"
  | .undef => "undef"
  | .poison => "poison"

private def printBinOp (op : String) (flags : List String) (t : LlvmType φ) (v1 v2 : Exp) : String :=
  let flagStr := String.join (flags.map (" " ++ ·))
  s!"{op}{flagStr} {t.print} {v1.print}, {v2.print}"

private def printConversionOp (op : String) (flags : List String) (fromTy : LlvmType φ) (v : Exp) (toTy : LlvmType φ) : String :=
  let flagStr := String.join (flags.map (" " ++ ·))
  s!"{op}{flagStr} {fromTy.print} {v.print} to {toTy.print}"

-- Syntax: [?cond1 => val1, ?cond2 => val2]
syntax "[?" (ident),* "]" : term

macro_rules
  | `([?]) => `(([] : List String))
  | `([? $id:ident, $[$ids:ident],*]) => do
    let flagName := id.getId.toString
    `( (if $id then [" " ++ $(Lean.quote flagName)] else []) ++ [? $[$ids],* ] )
  | `([? $id:ident]) => do
    let flagName := id.getId.toString
    `( if $id then [" " ++ $(Lean.quote flagName)] else [] )

def Instruction.print : @Instruction φ → String
  | .intBinaryOp op t v1 v2 =>
    let (name, flags) := match op with
      | .add nuw nsw => ("add", [?nuw, nsw])
      | .sub nuw nsw => ("sub", [?nuw, nsw])
      | .mul nuw nsw => ("mul", [?nuw, nsw])
      | .shl nuw nsw => ("shl", [?nuw, nsw])
      | .udiv exact => ("udiv", [?exact])
      | .sdiv exact => ("sdiv", [?exact])
      | .lshr exact => ("lshr", [?exact])
      | .ashr exact => ("ashr", [?exact])
      | .urem => ("urem", [])
      | .srem => ("srem", [])
      | .and => ("and", [])
      | .or disjoint => ("or", [?disjoint])
      | .xor => ("xor", [])
    printBinOp name flags t v1 v2

  | .conversionOp op fromTy v toTy =>
    let (name, flags) := match op with
      | .trunc nuw nsw => ("trunc", [?nuw, nsw])
      | .zext nneg => ("zext", [?nneg])
      | .sext => ("sext", [])
    printConversionOp name flags fromTy v toTy

  | .freeze ⟨ty, v⟩ =>
    s!"freeze {ty.print} {v.print}"

def Terminator.print : @Terminator φ → String
  | .retVoid => "ret void"
  | .ret ⟨ty, v⟩ => s!"ret {ty.print} {v.print}"

def printInstructionWithId (id : InstructionId) (instruction : @Instruction φ ⊕ @Terminator φ) : String :=
  let instructionStr := match instruction with
    | .inl instruction => instruction.print
    | .inr terminator => terminator.print

  match id with
  | .id id =>
    let id := Identifier.local_id id
    s!"{id.print} = {instructionStr}"
  | .void _ =>
    s!"{instructionStr}"


private def indentString (indent : Nat) (s : String) : String :=
  match indent with
  | 0 => ""
  | n + 1 => s ++ indentString n s


def printCode (indent : Nat) : @Code φ → String
  | .nil => ""
  | .cons ⟨id, instruction⟩ tail =>
    indentString indent " " ++ printInstructionWithId id (.inl instruction) ++ "\n" ++ printCode indent tail


def Block.print (block : @Block φ) : String :=
  let indentSize := 2
  s!"{block.id.ToString}:\n"
  ++ printCode indentSize block.code
  ++ indentString indentSize " " ++ printInstructionWithId block.terminator.fst (.inr block.terminator.snd) ++ "\n"

def Declaration.printSignature (decl : @Declaration φ) : String :=
  let id := Identifier.global_id decl.name
  match decl.type with
  | .function ret args =>
    let argStr := String.join <| args.map (fun ty => s!" {ty.print}")
    s!"{ret.print} {id.print}({argStr})"
  | _ => unreachable!

def Definition.printSignature (definition : @Definition φ) : String :=
  let decl := definition.prototype
  let id := Identifier.global_id decl.name
  match decl.type with
  | .function ret args =>
    let args := args.zip (definition.args.map (Identifier.local_id ·))
    let argStr := String.join <| args.map (fun ⟨ty, arg⟩ => s!" {ty.print} {arg.print}")
    s!"{ret.print} {id.print}({argStr})"
  | _ => unreachable!

def Declaration.print (decl : @Declaration φ) : String :=
  let sig := printSignature decl
  s!"declare {sig}"

def Definition.print (definition : @Definition φ) : String :=
  let sig := definition.printSignature
  s!"define {sig} "
  ++ "{\n"
  ++ definition.body.print
  ++ "}"

def TopLevelEntity.print : @TopLevelEntity φ → String
  | .declaration decl => decl.print
  | .definition defn => defn.print

def TopLevel.print : TopLevel φ → String
  | .nil => ""
  | .cons entity tail => entity.print ++ "\n" ++ TopLevel.print tail


end LeanNanoLlvm.AST
