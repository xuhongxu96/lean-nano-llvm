import LeanNanoLlvm.AST.AST

namespace LeanNanoLlvm.AST.Syntax

open Lean Lean.Meta Lean.Elab Lean.Elab.Term
open LeanNanoLlvm.AST

declare_syntax_cat nanollvm_rawid
syntax ident : nanollvm_rawid
syntax num : nanollvm_rawid

def elabNanoLlvmRawId : Syntax → MetaM Expr
  | `(nanollvm_rawid| $s:ident) => mkAppM ``RawId.name #[mkStrLit s.getId.toString]
  | `(nanollvm_rawid| $n:num) => mkAppM ``RawId.anonymom #[mkNatLit n.getNat]
  | _ => throwUnsupportedSyntax

declare_syntax_cat nanollvm_identifier
syntax "@" nanollvm_rawid : nanollvm_identifier
syntax "%" nanollvm_rawid : nanollvm_identifier

def elabNanoLlvmIdentifier : Syntax → MetaM Expr
  | `(nanollvm_identifier| @ $id:nanollvm_rawid) => do
    let rawid ← elabNanoLlvmRawId id
    mkAppM ``Identifier.global_id #[rawid]
  | `(nanollvm_identifier| % $id:nanollvm_rawid) => do
    let rawid ← elabNanoLlvmRawId id
    mkAppM ``Identifier.local_id #[rawid]
  | _ => throwUnsupportedSyntax

declare_syntax_cat nanollvm_type
syntax "void" : nanollvm_type
syntax ident : nanollvm_type
syntax nanollvm_type "(" nanollvm_type,* ")" : nanollvm_type

mutual
partial def elabNanoLlvmType (φ : Nat) : Syntax → MetaM Expr
  | `(nanollvm_type| $id:ident) => do
    let s := id.getId.toString
    if s.startsWith "i" then
      let numStr := s.drop 1
      match numStr.toNat? with
      | some n =>
        let w ← mkAppOptM ``Width.concrete #[mkNatLit φ, mkNatLit n]
        mkAppM ``LlvmType.int #[w]
      | none   => throwError "Invalid LLVM integer type width: {s}"
    else
      throwUnsupportedSyntax

  | `(nanollvm_type| $ret:nanollvm_type ( $params:nanollvm_type,* )) => do
    let ty ← mkAppM ``LlvmType #[mkNatLit φ]
    let ret ← elabNanoLlvmRetType φ ret
    let argVals ← params.getElems.mapM (elabNanoLlvmType φ)
    let argList ← mkListLit (ty) argVals.toList
    mkAppM ``LlvmType.function #[ret, argList]

  | _ => throwUnsupportedSyntax

partial def elabNanoLlvmRetType (φ : Nat) : Syntax → MetaM Expr
  | `(nanollvm_type| void) => mkAppOptM ``LlvmRetType.void #[mkNatLit φ]
  | stx => do
    let ty ← elabNanoLlvmType φ stx
    mkAppM ``LlvmRetType.ret #[ty]
end

declare_syntax_cat nanollvm_exp
syntax nanollvm_identifier : nanollvm_exp
syntax "true" : nanollvm_exp
syntax "false" : nanollvm_exp
syntax num : nanollvm_exp -- TODO: negative ints
syntax "null" : nanollvm_exp
syntax "undef" : nanollvm_exp
syntax "poison" : nanollvm_exp

def elabNanoLlvmExp : Syntax → MetaM Expr
  | `(nanollvm_exp| $id:nanollvm_identifier) => do
    let id ← elabNanoLlvmIdentifier id
    mkAppM ``Exp.identifier #[id]
  | `(nanollvm_exp| true) => mkAppM ``Exp.bool #[(.const ``Bool.true [])]
  | `(nanollvm_exp| false) => mkAppM ``Exp.bool #[(.const ``Bool.false [])]
  | `(nanollvm_exp| $n:num) => do
    let int ← mkAppM ``Int.ofNat #[mkNatLit n.getNat]
    mkAppM ``Exp.int #[int]
  | `(nanollvm_exp| null) => mkAppM ``Exp.null #[]
  | `(nanollvm_exp| undef) => mkAppM ``Exp.undef #[]
  | `(nanollvm_exp| poison) => mkAppM ``Exp.poison #[]
  | _ => throwUnsupportedSyntax

declare_syntax_cat nanollvm_int_bin_op
syntax "add" " nuw "? " nsw"? : nanollvm_int_bin_op
syntax "sub" " nuw "? " nsw"? : nanollvm_int_bin_op
syntax "mul" " nuw "? " nsw"? : nanollvm_int_bin_op
syntax "shl" " nuw "? " nsw"? : nanollvm_int_bin_op
syntax "udiv" " exact "? : nanollvm_int_bin_op
syntax "sdiv" " exact "? : nanollvm_int_bin_op
syntax "lshr" " exact "? : nanollvm_int_bin_op
syntax "ashr" " exact "? : nanollvm_int_bin_op
syntax "urem" : nanollvm_int_bin_op
syntax "srem" : nanollvm_int_bin_op
syntax "and" : nanollvm_int_bin_op
syntax "or" " disjoint "? : nanollvm_int_bin_op
syntax "xor" : nanollvm_int_bin_op

def elabNanoLlvmIntBinOp (stx : Syntax) : MetaM Expr := do
  -- child i is "present" when it was actually written in source
  let flag (i : Nat) : Bool := !stx[i].isNone
  match stx[0].getAtomVal with
  | "add"  => return mkAppN (mkConst ``IntBinaryOp.add)  #[toExpr (flag 1), toExpr (flag 2)]
  | "sub"  => return mkAppN (mkConst ``IntBinaryOp.sub)  #[toExpr (flag 1), toExpr (flag 2)]
  | "mul"  => return mkAppN (mkConst ``IntBinaryOp.mul)  #[toExpr (flag 1), toExpr (flag 2)]
  | "shl"  => return mkAppN (mkConst ``IntBinaryOp.shl)  #[toExpr (flag 1), toExpr (flag 2)]
  | "udiv" => return mkApp  (mkConst ``IntBinaryOp.udiv) (toExpr (flag 1))
  | "sdiv" => return mkApp  (mkConst ``IntBinaryOp.sdiv) (toExpr (flag 1))
  | "lshr" => return mkApp  (mkConst ``IntBinaryOp.lshr) (toExpr (flag 1))
  | "ashr" => return mkApp  (mkConst ``IntBinaryOp.ashr) (toExpr (flag 1))
  | "urem" => return mkConst ``IntBinaryOp.urem
  | "srem" => return mkConst ``IntBinaryOp.srem
  | "and"  => return mkConst ``IntBinaryOp.and
  | "or"   => return mkApp  (mkConst ``IntBinaryOp.or)   (toExpr (flag 1))
  | "xor"  => return mkConst ``IntBinaryOp.xor
  | op     => throwErrorAt stx "unknown IntBinaryOp opcode: {op}"

declare_syntax_cat nanollvm_conversion_op
syntax "trunc" " nuw "? " nsw"? : nanollvm_conversion_op
syntax "zext" " nneg "? : nanollvm_conversion_op
syntax "sext" : nanollvm_conversion_op

def elabNanoLlvmConversionOp (stx : Syntax) : MetaM Expr := do
  let flag (i : Nat) : Bool := !stx[i].isNone
  match stx[0].getAtomVal with
  | "trunc"  => return mkAppN (mkConst ``ConversionOp.trunc)  #[toExpr (flag 1), toExpr (flag 2)]
  | "zext"  => return mkAppN (mkConst ``ConversionOp.zext)  #[toExpr (flag 1)]
  | "sext"  => return mkAppN (mkConst ``ConversionOp.sext)  #[]
  | op     => throwErrorAt stx "unknown ConversionOp opcode: {op}"

declare_syntax_cat nanollvm_instruction
syntax nanollvm_int_bin_op nanollvm_type nanollvm_exp ", " nanollvm_exp : nanollvm_instruction
syntax nanollvm_conversion_op nanollvm_type nanollvm_exp " to " nanollvm_type : nanollvm_instruction
syntax "freeze" nanollvm_type nanollvm_exp : nanollvm_instruction

def elabNanoLlvmInstruction (φ: Nat) : Syntax → MetaM Expr
  | `(nanollvm_instruction| $op:nanollvm_int_bin_op $ty:nanollvm_type $op1:nanollvm_exp, $op2:nanollvm_exp) => do
    let op ← elabNanoLlvmIntBinOp op
    let ty ← elabNanoLlvmType φ ty
    let op1 ← elabNanoLlvmExp op1
    let op2 ← elabNanoLlvmExp op2
    mkAppM ``Instruction.intBinaryOp #[op, ty, op1, op2]
  | `(nanollvm_instruction| $op:nanollvm_conversion_op $fromTy:nanollvm_type $v:nanollvm_exp to $toTy:nanollvm_type) => do
    let op ← elabNanoLlvmConversionOp op
    let fromTy ← elabNanoLlvmType φ fromTy
    let v ← elabNanoLlvmExp v
    let toTy ← elabNanoLlvmType φ toTy
    mkAppM ``Instruction.conversionOp #[op, fromTy, v, toTy]
  | `(nanollvm_instruction| freeze $ty:nanollvm_type $v:nanollvm_exp) => do
    let ty ← elabNanoLlvmType φ ty
    let v ← elabNanoLlvmExp v
    let tv ← mkAppM ``Prod.mk #[ty, v]
    mkAppM ``Instruction.freeze #[tv]
  | _ => throwUnsupportedSyntax

declare_syntax_cat nanollvm_terminator
syntax "ret " "void" : nanollvm_terminator
syntax "ret " nanollvm_type nanollvm_exp : nanollvm_terminator

def elabNanoLlvmTerminator (φ : Nat) : Syntax → MetaM Expr
  | `(nanollvm_terminator| ret void) => mkAppOptM ``Terminator.retVoid #[mkNatLit φ]
  | `(nanollvm_terminator| ret $ty:nanollvm_type $e:nanollvm_exp) => do
    let ty ← elabNanoLlvmType φ ty
    let e ← elabNanoLlvmExp e
    let te ← mkAppM ``Prod.mk #[ty, e]
    mkAppOptM ``Terminator.ret #[mkNatLit φ, te]
  | _ => throwUnsupportedSyntax

declare_syntax_cat nanollvm_declaration
syntax "declare " nanollvm_type "@" nanollvm_rawid "(" nanollvm_type,* ")" : nanollvm_declaration

def elabNanoLlvmDeclaration (φ : Nat) : Syntax → MetaM Expr
  | `(nanollvm_declaration| declare $retTy:nanollvm_type @$id:nanollvm_rawid($params:nanollvm_type,*)) => do
    let id ← elabNanoLlvmRawId id
    let ty ← mkAppM ``LlvmType #[mkNatLit φ]
    let retTy ← elabNanoLlvmRetType φ retTy
    let argVals ← params.getElems.mapM (elabNanoLlvmType φ)
    let argList ← mkListLit (ty) argVals.toList
    let fnTy ← mkAppM ``LlvmType.function #[retTy, argList]
    mkAppOptM ``Declaration.mk #[mkNatLit φ, id, fnTy]
  | _ => throwUnsupportedSyntax

declare_syntax_cat nanollvm_codeline
syntax "%" nanollvm_rawid " = " nanollvm_instruction linebreak : nanollvm_codeline
syntax nanollvm_instruction linebreak : nanollvm_codeline

def elabNanoLlvmCodeline (φ : Nat) (lineno: Nat) : Syntax → MetaM Expr
  | `(nanollvm_codeline| %$id:nanollvm_rawid = $instr:nanollvm_instruction
  ) => do
    let id ← elabNanoLlvmRawId id
    let id ← mkAppM ``InstructionId.id #[id]
    let instr ← elabNanoLlvmInstruction φ instr
    mkAppM ``Prod.mk #[id, instr]
  | `(nanollvm_codeline| $instr:nanollvm_instruction
  ) => do
    let id ← mkAppM ``InstructionId.void #[mkNatLit lineno]
    let instr ← elabNanoLlvmInstruction φ instr
    mkAppM ``Prod.mk #[id, instr]
  | _ => throwUnsupportedSyntax

declare_syntax_cat nanollvm_code
syntax nanollvm_codeline* : nanollvm_code

def elabNanoLlvmCode (φ : Nat) (lineno: Nat) : Syntax → MetaM (Expr × Nat)
  | `(nanollvm_code| $codelines:nanollvm_codeline*) => do
    let instrTy ← mkAppOptM ``Instruction #[mkNatLit φ]
    let ty ← mkAppM ``Prod #[mkConst ``InstructionId, instrTy]
    let codelines ← codelines.mapIdxM (fun offset => elabNanoLlvmCodeline φ (lineno + offset))
    pure (← mkListLit (ty) codelines.toList, codelines.size)
  | _ => throwUnsupportedSyntax

declare_syntax_cat nanollvm_block
syntax nanollvm_rawid ": " linebreak nanollvm_code nanollvm_terminator : nanollvm_block

def elabNanoLlvmBlock (φ : Nat) (lineno: Nat) : Syntax → MetaM Expr
  | `(nanollvm_block| $id:nanollvm_rawid:
  $code:nanollvm_code $term:nanollvm_terminator) => do
    let id ← elabNanoLlvmRawId id
    let ⟨code, nLines⟩ ← elabNanoLlvmCode φ lineno code
    let term ← elabNanoLlvmTerminator φ term
    let termId ← mkAppM ``InstructionId.void #[mkNatLit (lineno + nLines)]
    let term ← mkAppM ``Prod.mk #[termId, term]
    mkAppM ``Block.mk #[id, code, term]
  | _ => throwUnsupportedSyntax

declare_syntax_cat nanollvm_arg
syntax nanollvm_type " %" nanollvm_rawid : nanollvm_arg

def elabNanoLlvmArg (φ : Nat) : Syntax → MetaM (Expr × Expr)
  | `(nanollvm_arg| $ty:nanollvm_type %$id:nanollvm_rawid) => do
    let ty ← elabNanoLlvmType φ ty
    let id ← elabNanoLlvmRawId id
    pure (ty, id)
  | _ => throwUnsupportedSyntax

declare_syntax_cat nanollvm_definition
syntax "define " nanollvm_type "@" nanollvm_rawid "(" nanollvm_arg,* ")" " {" nanollvm_block "}" : nanollvm_definition

def elabNanoLlvmDefinition (φ : Nat) : Syntax → MetaM Expr
  | `(nanollvm_definition| define $retTy:nanollvm_type @$id:nanollvm_rawid($args:nanollvm_arg,*) { $block:nanollvm_block }) => do
    let id ← elabNanoLlvmRawId id
    let argTy ← mkAppM ``LlvmType #[mkNatLit φ]
    let retTy ← elabNanoLlvmRetType φ retTy
    let argTys ← args.getElems.mapM (fun a => do pure (← elabNanoLlvmArg φ a).fst)
    let argNames ← args.getElems.mapM (fun a => do pure (← elabNanoLlvmArg φ a).snd)
    let argList ← mkListLit (argTy) argTys.toList
    let argNameList ← mkListLit (mkConst ``RawId) argNames.toList
    let fnTy ← mkAppM ``LlvmType.function #[retTy, argList]
    let block ← elabNanoLlvmBlock φ 1 block
    let decl ← mkAppOptM ``Declaration.mk #[mkNatLit φ, id, fnTy]
    mkAppOptM ``Definition.mk #[mkNatLit φ, decl, argNameList, block]
  | _ => throwUnsupportedSyntax

declare_syntax_cat nanollvm_entity
syntax nanollvm_declaration : nanollvm_entity
syntax nanollvm_definition : nanollvm_entity

def elabNanoLlvmEntity (φ : Nat) : Syntax → MetaM Expr
  | `(nanollvm_entity| $decl:nanollvm_declaration) => do
    let decl ← elabNanoLlvmDeclaration φ decl
    mkAppOptM ``TopLevelEntity.declaration #[mkNatLit φ, decl]
  | `(nanollvm_entity| $defn:nanollvm_definition) => do
    let defn ← elabNanoLlvmDefinition φ defn
    mkAppOptM ``TopLevelEntity.definition #[mkNatLit φ, defn]
  | _ => throwUnsupportedSyntax

declare_syntax_cat nanollvm
syntax nanollvm_entity* : nanollvm

def elabNanoLlvm (φ : Nat) : Syntax → MetaM Expr
  | `(nanollvm| $entity:nanollvm_entity*) => do
    let entity ← entity.mapM (elabNanoLlvmEntity φ)
    let ty ← mkAppOptM ``TopLevelEntity #[mkNatLit φ]
    mkListLit ty entity.toList
  | _ => throwUnsupportedSyntax

elab ">>[" n:num "]" linebreak p:nanollvm "<<" : term => elabNanoLlvm n.getNat p


end LeanNanoLlvm.AST.Syntax
