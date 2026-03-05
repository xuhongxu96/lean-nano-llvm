import LeanNanoLlvm.AST.AST

namespace LeanNanoLlvm.AST.Syntax

open Lean Lean.Meta Lean.Elab Lean.Elab.Term
open LeanNanoLlvm.AST
open scoped LeanNanoLlvm.AST.Syntax

declare_syntax_cat nanollvm_rawid
scoped syntax ident : nanollvm_rawid
scoped syntax num : nanollvm_rawid

def elabNanoLlvmRawId : Syntax → MetaM Expr
  | `(nanollvm_rawid| $s:ident) => mkAppM ``RawId.name #[mkStrLit s.getId.toString]
  | `(nanollvm_rawid| $n:num) => mkAppM ``RawId.anonymous #[mkNatLit n.getNat]
  | _ => throwUnsupportedSyntax

elab "[llvm-rawid|" p:nanollvm_rawid "]" : term => elabNanoLlvmRawId p

declare_syntax_cat nanollvm_identifier
scoped syntax "@" nanollvm_rawid : nanollvm_identifier
scoped syntax "%" nanollvm_rawid : nanollvm_identifier

def elabNanoLlvmIdentifier : Syntax → MetaM Expr
  | `(nanollvm_identifier| @ $id:nanollvm_rawid) => do
    let rawid ← elabNanoLlvmRawId id
    mkAppM ``Identifier.global_id #[rawid]
  | `(nanollvm_identifier| % $id:nanollvm_rawid) => do
    let rawid ← elabNanoLlvmRawId id
    mkAppM ``Identifier.local_id #[rawid]
  | _ => throwUnsupportedSyntax

elab "[llvm-identifier|" p:nanollvm_identifier "]" : term => elabNanoLlvmIdentifier p

declare_syntax_cat nanollvm_instruction_id
scoped syntax "void " "(" num ")"  : nanollvm_instruction_id
scoped syntax "%" nanollvm_rawid : nanollvm_instruction_id

def elabNanoLlvmInstructionId : Syntax → MetaM Expr
  | `(nanollvm_instruction_id| void ($n:num)) =>
    mkAppM ``InstructionId.void #[mkNatLit n.getNat]
  | `(nanollvm_instruction_id | %$id:nanollvm_rawid) => do
    let rawid ← elabNanoLlvmRawId id
    mkAppM ``InstructionId.id #[rawid]
  | _ => throwUnsupportedSyntax

elab "[llvm-instruction-id|" p:nanollvm_instruction_id "]" : term => elabNanoLlvmInstructionId p

declare_syntax_cat nanollvm_type
scoped syntax "void" : nanollvm_type
scoped syntax ident : nanollvm_type
scoped syntax nanollvm_type "(" nanollvm_type,* ")" : nanollvm_type

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

elab "[llvm-" n:num "-type|" p:nanollvm_type "]" : term => elabNanoLlvmType n.getNat p
elab "[llvm-type|" p:nanollvm_type "]" : term => elabNanoLlvmType 512 p

declare_syntax_cat nanollvm_exp
scoped syntax nanollvm_identifier : nanollvm_exp
scoped syntax "<" ident ":int>" : nanollvm_exp
scoped syntax "true" : nanollvm_exp
scoped syntax "false" : nanollvm_exp
scoped syntax num : nanollvm_exp -- TODO: negative ints
scoped syntax "null" : nanollvm_exp
scoped syntax "undef" : nanollvm_exp
scoped syntax "undef!" nanollvm_rawid : nanollvm_exp
scoped syntax "poison" : nanollvm_exp

def elabNanoLlvmExp (undefStartIndex : Nat) : Syntax → MetaM (Expr × Nat)
  | `(nanollvm_exp| $id:nanollvm_identifier) => do
    let id ← elabNanoLlvmIdentifier id
    pure (← mkAppM ``Exp.identifier #[id], undefStartIndex)
  | `(nanollvm_exp| <$id:ident:int>) => do
    let lctx ← getLCtx
    match lctx.findFromUserName? id.getId with
    | some decl =>
      let e := decl.toExpr
      let t ← whnf (← inferType e)
      if ← isDefEq t (mkConst ``Int) then
        pure (← mkAppM ``Exp.int #[e], undefStartIndex)
      else if ← isDefEq t (mkConst ``Nat) then
        pure (← mkAppM ``Exp.int #[← mkAppM ``Int.ofNat #[e]], undefStartIndex)
      else
        throwErrorAt id "Expected local Int/Nat variable in LLVM expression, got type {t}"
    | none =>
      throwErrorAt id "Unknown local identifier '{id.getId}' in LLVM expression"
  | `(nanollvm_exp| true) => do
    pure (← mkAppM ``Exp.bool #[(.const ``Bool.true [])], undefStartIndex)
  | `(nanollvm_exp| false) => do
    pure (← mkAppM ``Exp.bool #[(.const ``Bool.false [])], undefStartIndex)
  | `(nanollvm_exp| $n:num) => do
    let int ← mkAppM ``Int.ofNat #[mkNatLit n.getNat]
    pure (← mkAppM ``Exp.int #[int], undefStartIndex)
  | `(nanollvm_exp| null) => do
    pure (← mkAppM ``Exp.null #[], undefStartIndex)
  | `(nanollvm_exp| undef) => do
    let rawid ← mkAppM ``RawId.anonymous #[mkNatLit undefStartIndex]
    pure (← mkAppM ``Exp.undef #[rawid], undefStartIndex + 1)
  | `(nanollvm_exp| undef!$rawid:nanollvm_rawid) => do
    let rawid ← elabNanoLlvmRawId rawid
    pure (← mkAppM ``Exp.undef #[rawid], undefStartIndex)
  | `(nanollvm_exp| poison) => do
    pure (← mkAppM ``Exp.poison #[], undefStartIndex)
  | _ => throwUnsupportedSyntax

elab "[llvm-" m:num "-exp|" p:nanollvm_exp "]" : term => do
  pure (← elabNanoLlvmExp m.getNat p).fst
elab "[llvm-exp|" p:nanollvm_exp "]" : term => do
  pure (← elabNanoLlvmExp 0 p).fst

declare_syntax_cat nanollvm_int_bin_op
scoped syntax "add" " nuw "? " nsw"? : nanollvm_int_bin_op
scoped syntax "sub" " nuw "? " nsw"? : nanollvm_int_bin_op
scoped syntax "mul" " nuw "? " nsw"? : nanollvm_int_bin_op
scoped syntax "shl" " nuw "? " nsw"? : nanollvm_int_bin_op
scoped syntax "udiv" " exact "? : nanollvm_int_bin_op
scoped syntax "sdiv" " exact "? : nanollvm_int_bin_op
scoped syntax "lshr" " exact "? : nanollvm_int_bin_op
scoped syntax "ashr" " exact "? : nanollvm_int_bin_op
scoped syntax "urem" : nanollvm_int_bin_op
scoped syntax "srem" : nanollvm_int_bin_op
scoped syntax "and" : nanollvm_int_bin_op
scoped syntax "or" " disjoint "? : nanollvm_int_bin_op
scoped syntax "xor" : nanollvm_int_bin_op

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

elab "[llvm-int-bin-op|" p:nanollvm_int_bin_op "]" : term => elabNanoLlvmIntBinOp p

declare_syntax_cat nanollvm_conversion_op
scoped syntax "trunc" " nuw "? " nsw"? : nanollvm_conversion_op
scoped syntax "zext" " nneg "? : nanollvm_conversion_op
scoped syntax "sext" : nanollvm_conversion_op

def elabNanoLlvmConversionOp (stx : Syntax) : MetaM Expr := do
  let flag (i : Nat) : Bool := !stx[i].isNone
  match stx[0].getAtomVal with
  | "trunc"  => return mkAppN (mkConst ``ConversionOp.trunc)  #[toExpr (flag 1), toExpr (flag 2)]
  | "zext"  => return mkAppN (mkConst ``ConversionOp.zext)  #[toExpr (flag 1)]
  | "sext"  => return mkAppN (mkConst ``ConversionOp.sext)  #[]
  | op     => throwErrorAt stx "unknown ConversionOp opcode: {op}"

elab "[llvm-conversion-op|" p:nanollvm_conversion_op "]" : term => elabNanoLlvmConversionOp p

declare_syntax_cat nanollvm_instruction
scoped syntax nanollvm_int_bin_op ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_exp : nanollvm_instruction
scoped syntax nanollvm_conversion_op ppHardSpace nanollvm_type ppHardSpace nanollvm_exp " to " nanollvm_type : nanollvm_instruction
scoped syntax "freeze" ppHardSpace nanollvm_type ppHardSpace nanollvm_exp : nanollvm_instruction

def elabNanoLlvmInstruction (φ: Nat) (_lineno : Nat) (undefStartIndex : Nat) : Syntax → MetaM (Expr × Nat)
  | `(nanollvm_instruction| $op:nanollvm_int_bin_op $ty:nanollvm_type $op1:nanollvm_exp, $op2:nanollvm_exp) => do
    let op ← elabNanoLlvmIntBinOp op
    let ty ← elabNanoLlvmType φ ty
    let (op1, undefNext) ← elabNanoLlvmExp undefStartIndex op1
    let (op2, undefNext) ← elabNanoLlvmExp undefNext op2
    pure (← mkAppM ``Instruction.intBinaryOp #[op, ty, op1, op2], undefNext)
  | `(nanollvm_instruction| $op:nanollvm_conversion_op $fromTy:nanollvm_type $v:nanollvm_exp to $toTy:nanollvm_type) => do
    let op ← elabNanoLlvmConversionOp op
    let fromTy ← elabNanoLlvmType φ fromTy
    let (v, undefNext) ← elabNanoLlvmExp undefStartIndex v
    let toTy ← elabNanoLlvmType φ toTy
    pure (← mkAppM ``Instruction.conversionOp #[op, fromTy, v, toTy], undefNext)
  | `(nanollvm_instruction| freeze $ty:nanollvm_type $v:nanollvm_exp) => do
    let ty ← elabNanoLlvmType φ ty
    let (v, undefNext) ← elabNanoLlvmExp undefStartIndex v
    let tv ← mkAppM ``Prod.mk #[ty, v]
    pure (← mkAppM ``Instruction.freeze #[tv], undefNext)
  | _ => throwUnsupportedSyntax

elab "[llvm-" n:num "-" m:num "-instruction|" p:nanollvm_instruction "]" : term => do
  pure (← elabNanoLlvmInstruction n.getNat m.getNat m.getNat p).fst
elab "[llvm-" n:num "-instruction|" p:nanollvm_instruction "]" : term => do
  pure (← elabNanoLlvmInstruction n.getNat 0 0 p).fst
elab "[llvm-instruction|" p:nanollvm_instruction "]" : term => do
  pure (← elabNanoLlvmInstruction 512 0 0 p).fst

declare_syntax_cat nanollvm_terminator
scoped syntax "ret " "void" : nanollvm_terminator
scoped syntax "ret " nanollvm_type ppHardSpace nanollvm_exp : nanollvm_terminator

def elabNanoLlvmTerminator (φ : Nat) (undefStartIndex : Nat) : Syntax → MetaM (Expr × Nat)
  | `(nanollvm_terminator| ret void) => do
    pure (← mkAppOptM ``Terminator.retVoid #[mkNatLit φ], undefStartIndex)
  | `(nanollvm_terminator| ret $ty:nanollvm_type $e:nanollvm_exp) => do
    let ty ← elabNanoLlvmType φ ty
    let (e, undefNext) ← elabNanoLlvmExp undefStartIndex e
    let te ← mkAppM ``Prod.mk #[ty, e]
    pure (← mkAppOptM ``Terminator.ret #[mkNatLit φ, te], undefNext)
  | _ => throwUnsupportedSyntax

elab "[llvm-" n:num "-" m:num "-terminator|" p:nanollvm_terminator "]" : term => do
  pure (← elabNanoLlvmTerminator n.getNat m.getNat p).fst
elab "[llvm-" n:num "-terminator|" p:nanollvm_terminator "]" : term => do
  pure (← elabNanoLlvmTerminator n.getNat 0 p).fst
elab "[llvm-terminator|" p:nanollvm_terminator "]" : term => do
  pure (← elabNanoLlvmTerminator 512 0 p).fst

declare_syntax_cat nanollvm_declaration
scoped syntax "declare " nanollvm_type ppHardSpace "@" nanollvm_rawid "(" nanollvm_type,* ")" : nanollvm_declaration

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

elab "[llvm-" n:num "-declaration|" p:nanollvm_declaration "]" : term => elabNanoLlvmDeclaration n.getNat p
elab "[llvm-declaration|" p:nanollvm_declaration "]" : term => elabNanoLlvmDeclaration 512 p

declare_syntax_cat nanollvm_codeline
scoped syntax "%" nanollvm_rawid " = " nanollvm_instruction : nanollvm_codeline
scoped syntax nanollvm_instruction : nanollvm_codeline

def elabNanoLlvmCodeline (φ : Nat) (lineno: Nat) (undefStartIndex : Nat) : Syntax → MetaM (Expr × Nat)
  | `(nanollvm_codeline| %$id:nanollvm_rawid = $instr:nanollvm_instruction
  ) => do
    let id ← elabNanoLlvmRawId id
    let id ← mkAppM ``InstructionId.id #[id]
    let (instr, undefNext) ← elabNanoLlvmInstruction φ lineno undefStartIndex instr
    pure (← mkAppM ``Prod.mk #[id, instr], undefNext)
  | `(nanollvm_codeline| $instr:nanollvm_instruction
  ) => do
    let id ← mkAppM ``InstructionId.void #[mkNatLit lineno]
    let (instr, undefNext) ← elabNanoLlvmInstruction φ lineno undefStartIndex instr
    pure (← mkAppM ``Prod.mk #[id, instr], undefNext)
  | _ => throwUnsupportedSyntax

elab "[llvm-" n:num "-" l:num "-codeline|" p:nanollvm_codeline "]" : term => do
  pure (← elabNanoLlvmCodeline n.getNat l.getNat 0 p).fst
elab "[llvm-codeline|" p:nanollvm_codeline "]" : term => do
  pure (← elabNanoLlvmCodeline 512 1 0 p).fst

declare_syntax_cat nanollvm_code
scoped syntax ppDedent(ppLine nanollvm_codeline)* : nanollvm_code

def elabNanoLlvmCode (φ : Nat) (lineno: Nat) (undefStartIndex : Nat) : Syntax → MetaM (Expr × Nat × Nat)
  | `(nanollvm_code| $lines:nanollvm_codeline*) => do
    let instrTy ← mkAppOptM ``Instruction #[mkNatLit φ]
    let ty ← mkAppM ``Prod #[mkConst ``InstructionId, instrTy]
    let codelines := lines
    let mut undefNext := undefStartIndex
    let mut elabedCodelines : Array Expr := #[]
    for offset in [:codelines.size] do
      let codeline := codelines[offset]!
      let (codeline, next) ← elabNanoLlvmCodeline φ (lineno + offset) undefNext codeline
      undefNext := next
      elabedCodelines := elabedCodelines.push codeline
    pure (← mkListLit (ty) elabedCodelines.toList, elabedCodelines.size, undefNext)
  | _ => throwUnsupportedSyntax

elab "[llvm-" n:num "-" l:num "-code|" p:nanollvm_code "]" : term => do
  pure (← elabNanoLlvmCode n.getNat l.getNat 0 p).1
elab "[llvm-code|" p:nanollvm_code "]" : term => do
  pure (← elabNanoLlvmCode 512 1 0 p).1

declare_syntax_cat nanollvm_block
scoped syntax nanollvm_rawid ": " ppIndent(nanollvm_code ppLine nanollvm_terminator) : nanollvm_block

def elabNanoLlvmBlock (φ : Nat) (lineno: Nat) (undefStartIndex : Nat) : Syntax → MetaM (Expr × Nat)
  | `(nanollvm_block| $id:nanollvm_rawid:
  $code:nanollvm_code $term:nanollvm_terminator) => do
    let id ← elabNanoLlvmRawId id
    let (code, nLines, undefNext) ← elabNanoLlvmCode φ lineno undefStartIndex code
    let (term, undefNext) ← elabNanoLlvmTerminator φ undefNext term
    let termId ← mkAppM ``InstructionId.void #[mkNatLit (lineno + nLines)]
    let term ← mkAppM ``Prod.mk #[termId, term]
    pure (← mkAppM ``Block.mk #[id, code, term], undefNext)
  | _ => throwUnsupportedSyntax

elab "[llvm-" n:num "-" l:num "-block|" p:nanollvm_block "]" : term => do
  pure (← elabNanoLlvmBlock n.getNat l.getNat 0 p).fst
elab "[llvm-block|" p:nanollvm_block "]" : term => do
  pure (← elabNanoLlvmBlock 512 1 0 p).fst

declare_syntax_cat nanollvm_arg
scoped syntax nanollvm_type " %" nanollvm_rawid : nanollvm_arg

def elabNanoLlvmArg (φ : Nat) : Syntax → MetaM (Expr × Expr)
  | `(nanollvm_arg| $ty:nanollvm_type %$id:nanollvm_rawid) => do
    let ty ← elabNanoLlvmType φ ty
    let id ← elabNanoLlvmRawId id
    pure (ty, id)
  | _ => throwUnsupportedSyntax

elab "[llvm-" n:num "-arg|" p:nanollvm_arg "]" : term => do
  let (ty, id) ← elabNanoLlvmArg n.getNat p
  mkAppM ``Prod.mk #[ty, id]
elab "[llvm-arg|" p:nanollvm_arg "]" : term => do
  let (ty, id) ← elabNanoLlvmArg 512 p
  mkAppM ``Prod.mk #[ty, id]

declare_syntax_cat nanollvm_definition
scoped syntax "define " nanollvm_type ppHardSpace "@" nanollvm_rawid "(" nanollvm_arg,* ") "
       ppDedent(ppDedent("{" ppLine nanollvm_block ppLine "}")) : nanollvm_definition

def elabNanoLlvmDefinition (φ : Nat) : Syntax → MetaM Expr
  | `(nanollvm_definition| define $retTy:nanollvm_type @$id:nanollvm_rawid($args:nanollvm_arg,*) {
    $block:nanollvm_block
    }) => do
    let id ← elabNanoLlvmRawId id
    let argTy ← mkAppM ``LlvmType #[mkNatLit φ]
    let retTy ← elabNanoLlvmRetType φ retTy
    let argTys ← args.getElems.mapM (fun a => do pure (← elabNanoLlvmArg φ a).fst)
    let argNames ← args.getElems.mapM (fun a => do pure (← elabNanoLlvmArg φ a).snd)
    let argList ← mkListLit (argTy) argTys.toList
    let argNameList ← mkListLit (mkConst ``RawId) argNames.toList
    let fnTy ← mkAppM ``LlvmType.function #[retTy, argList]
    let blockResult ← elabNanoLlvmBlock φ 1 0 block
    let block := blockResult.fst
    let decl ← mkAppOptM ``Declaration.mk #[mkNatLit φ, id, fnTy]
    mkAppOptM ``Definition.mk #[mkNatLit φ, decl, argNameList, block]
  | _ => throwUnsupportedSyntax

elab "[llvm-" n:num "-definition|" p:nanollvm_definition "]" : term => elabNanoLlvmDefinition n.getNat p
elab "[llvm-definition|" p:nanollvm_definition "]" : term => elabNanoLlvmDefinition 512 p

declare_syntax_cat nanollvm_entity
scoped syntax nanollvm_declaration : nanollvm_entity
scoped syntax nanollvm_definition : nanollvm_entity

def elabNanoLlvmEntity (φ : Nat) : Syntax → MetaM Expr
  | `(nanollvm_entity| $decl:nanollvm_declaration) => do
    let decl ← elabNanoLlvmDeclaration φ decl
    mkAppOptM ``TopLevelEntity.declaration #[mkNatLit φ, decl]
  | `(nanollvm_entity| $defn:nanollvm_definition) => do
    let defn ← elabNanoLlvmDefinition φ defn
    mkAppOptM ``TopLevelEntity.definition #[mkNatLit φ, defn]
  | _ => throwUnsupportedSyntax

elab "[llvm-" n:num "-entity|" p:nanollvm_entity "]" : term => elabNanoLlvmEntity n.getNat p
elab "[llvm-entity|" p:nanollvm_entity "]" : term => elabNanoLlvmEntity 512 p

declare_syntax_cat nanollvm
scoped syntax ppDedent(nanollvm_entity ppLine)* : nanollvm

def elabNanoLlvm (φ : Nat) : Syntax → MetaM Expr
  | `(nanollvm| $entity:nanollvm_entity*) => do
    let entity ← entity.mapM (elabNanoLlvmEntity φ)
    let ty ← mkAppOptM ``TopLevelEntity #[mkNatLit φ]
    let entities ← mkListLit ty entity.toList
    mkAppOptM ``TopLevel.mk #[mkNatLit φ, entities]
  | _ => throwUnsupportedSyntax

elab "[llvm-" n:num "|" ppLine p:nanollvm "]" : term => elabNanoLlvm n.getNat p
elab "[llvm|" ppLine p:nanollvm "]" : term => elabNanoLlvm 512 p

end LeanNanoLlvm.AST.Syntax
