import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.AST

open Lean PrettyPrinter PrettyPrinter.Delaborator SubExpr
open scoped LeanNanoLlvm.AST.Syntax

private def asRawId? (stx : Syntax) : Option (TSyntax `nanollvm_rawid) :=
  match stx with
  | `([llvm-rawid| $id:nanollvm_rawid]) => some id
  | _ => none

private def asIdentifier? (stx : Syntax) : Option (TSyntax `nanollvm_identifier) :=
  match stx with
  | `([llvm-identifier| $id:nanollvm_identifier]) => some id
  | _ => none

private def asInstructionId? (stx : Syntax) : Option (TSyntax `nanollvm_instruction_id) :=
  match stx with
  | `([llvm-instruction-id| $id:nanollvm_instruction_id]) => some id
  | _ => none

private def asType? (stx : Syntax) : Option (TSyntax `nanollvm_type) :=
  match stx with
  | `([llvm-type| $ty:nanollvm_type]) => some ty
  | _ => none

private def asExp? (stx : Syntax) : Option (TSyntax `nanollvm_exp) :=
  match stx with
  | `([llvm-exp| $e:nanollvm_exp]) => some e
  | _ => none

private def asIntBinOp? (stx : Syntax) : Option (TSyntax `nanollvm_int_bin_op) :=
  match stx with
  | `([llvm-int-bin-op| $op:nanollvm_int_bin_op]) => some op
  | _ => none

private def asConversionOp? (stx : Syntax) : Option (TSyntax `nanollvm_conversion_op) :=
  match stx with
  | `([llvm-conversion-op| $op:nanollvm_conversion_op]) => some op
  | _ => none

private def asInstruction? (stx : Syntax) : Option (TSyntax `nanollvm_instruction) :=
  match stx with
  | `([llvm-instruction| $instr:nanollvm_instruction]) => some instr
  | _ => none

private def asTerminator? (stx : Syntax) : Option (TSyntax `nanollvm_terminator) :=
  match stx with
  | `([llvm-terminator| $term:nanollvm_terminator]) => some term
  | _ => none

private def asDeclaration? (stx : Syntax) : Option (TSyntax `nanollvm_declaration) :=
  match stx with
  | `([llvm-declaration| $decl:nanollvm_declaration]) => some decl
  | _ => none

private def asDefinition? (stx : Syntax) : Option (TSyntax `nanollvm_definition) :=
  match stx with
  | `([llvm-definition| $defn:nanollvm_definition]) => some defn
  | _ => none

private def asBlock? (stx : Syntax) : Option (TSyntax `nanollvm_block) :=
  match stx with
  | `([llvm-block| $blk:nanollvm_block]) => some blk
  | _ => none

private def asEntity? (stx : Syntax) : Option (TSyntax `nanollvm_entity) :=
  match stx with
  | `([llvm-entity| $entity:nanollvm_entity]) => some entity
  | _ => none

private def asCodeline (stx : Syntax) : UnexpandM (TSyntax `nanollvm_codeline) := do
  match stx with
  | `(nanollvm_codeline| %$id:nanollvm_rawid = $instr:nanollvm_instruction) =>
    `(nanollvm_codeline| %$id:nanollvm_rawid = $instr:nanollvm_instruction)
  | `(nanollvm_codeline| $instr:nanollvm_instruction) =>
    `(nanollvm_codeline| $instr:nanollvm_instruction)
  | _ => throw ()

private def asCode?(stx : Syntax) : Option (TSyntax `nanollvm_code) :=
  match stx with
  | `([llvm-code| $code:nanollvm_code]) => some ⟨code⟩
  | _ => none

@[app_unexpander RawId.name]
def unexpandRawIdName : Unexpander
  | `($_ $s:str) =>
    let name := mkIdent $ Name.mkSimple s.getString
    `([llvm-rawid| $name:ident])
  | _ => throw ()

@[app_unexpander RawId.anonymous]
def unexpandRawIdAnonymous : Unexpander
  | `($_ $n:num) => `([llvm-rawid| $n:num])
  | _ => throw ()

@[app_unexpander Identifier.global_id]
def unexpandIdentifierGlobalId : Unexpander
  | `($_ $id) =>
    match asRawId? id with
    | some id => `([llvm-identifier| @ $id:nanollvm_rawid])
    | none => throw ()
  | _ => throw ()

@[app_unexpander Identifier.local_id]
def unexpandIdentifierLocalId : Unexpander
  | `($_ $id) =>
    match asRawId? id with
    | some id => `([llvm-identifier| % $id:nanollvm_rawid])
    | none => throw ()
  | _ => throw ()

@[app_unexpander InstructionId.id]
def unexpandLlvmInstructionIdId : Unexpander
  | `($_ $id) =>
    match asRawId? id with
    | some id => `([llvm-instruction-id| % $id:nanollvm_rawid])
    | none => throw ()
  | _ => throw ()

@[app_unexpander InstructionId.void]
def unexpandLlvmInstructionIdVoid : Unexpander
  | `($_ $n:num) =>
    `([llvm-instruction-id| void ($n:num)])
  | _ => throw ()

@[app_unexpander LlvmRetType.void]
def unexpandLlvmRetTypeVoid : Unexpander
  | `($_) => `([llvm-type| void])

@[app_unexpander LlvmRetType.ret]
def unexpandLlvmRetTypeRet : Unexpander
  | `($_ $ty) =>
    match asType? ty with
    | some ty => `([llvm-type| $ty:nanollvm_type])
    | none => throw ()
  | _ => throw ()

@[app_unexpander Width.concrete]
def unexpandWidthConcrete : Unexpander
  | `($_ $w:num) =>
    let w := mkIdent $ Name.mkSimple s!"i{w.getNat}"
    `([llvm-type| $w:ident])
  | _ => throw ()

@[app_unexpander LlvmType.int]
def unexpandLlvmTypeInt : Unexpander
  | `($_ $w) =>
    match asType? w with
    | some w => `([llvm-type| $w:nanollvm_type])
    | none => throw ()
  | _ => throw ()

@[app_unexpander LlvmType.function]
def unexpandLlvmTypeFunction : Unexpander
  | `($_ $retTy [$args,*]) =>
    match asType? retTy with
    | none => throw ()
    | some retTy =>
      let args : Option (Array (TSyntax `nanollvm_type)) :=
        args.getElems.mapM asType?
      match args with
      | none => throw ()
      | some args =>
        let args : Syntax.TSepArray `nanollvm_type "," := args
        `([llvm-type| $retTy:nanollvm_type($args,*)])
  | _ => throw ()

@[app_unexpander IntBinaryOp.add]
def unexpandIntBinaryOpAdd : Unexpander
  | `($_ $a:ident $b:ident) =>
    match a.getId, b.getId with
    | `true, `true => `([llvm-int-bin-op| add nuw nsw])
    | `true, `false => `([llvm-int-bin-op| add nuw])
    | `false, `true => `([llvm-int-bin-op| add nsw])
    | `false, `false => `([llvm-int-bin-op| add])
    | _, _ => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.sub]
def unexpandIntBinaryOpSub : Unexpander
  | `($_ $a:ident $b:ident) =>
    match a.getId, b.getId with
    | `true, `true => `([llvm-int-bin-op| sub nuw nsw])
    | `true, `false => `([llvm-int-bin-op| sub nuw])
    | `false, `true => `([llvm-int-bin-op| sub nsw])
    | `false, `false => `([llvm-int-bin-op| sub])
    | _, _ => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.mul]
def unexpandIntBinaryOpMul : Unexpander
  | `($_ $a:ident $b:ident) =>
    match a.getId, b.getId with
    | `true, `true => `([llvm-int-bin-op| mul nuw nsw])
    | `true, `false => `([llvm-int-bin-op| mul nuw])
    | `false, `true => `([llvm-int-bin-op| mul nsw])
    | `false, `false => `([llvm-int-bin-op| mul])
    | _, _ => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.shl]
def unexpandIntBinaryOpShl : Unexpander
  | `($_ $a:ident $b:ident) =>
    match a.getId, b.getId with
    | `true, `true => `([llvm-int-bin-op| shl nuw nsw])
    | `true, `false => `([llvm-int-bin-op| shl nuw])
    | `false, `true => `([llvm-int-bin-op| shl nsw])
    | `false, `false => `([llvm-int-bin-op| shl])
    | _, _ => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.udiv]
def unexpandIntBinaryOpUdiv : Unexpander
  | `($_ $a:ident) =>
    match a.getId with
    | `true => `([llvm-int-bin-op| udiv exact])
    | `false => `([llvm-int-bin-op| udiv])
    | _ => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.sdiv]
def unexpandIntBinaryOpSdiv : Unexpander
  | `($_ $a:ident) =>
    match a.getId with
    | `true => `([llvm-int-bin-op| sdiv exact])
    | `false => `([llvm-int-bin-op| sdiv])
    | _ => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.lshr]
def unexpandIntBinaryOpLshr : Unexpander
  | `($_ $a:ident) =>
    match a.getId with
    | `true => `([llvm-int-bin-op| lshr exact])
    | `false => `([llvm-int-bin-op| lshr])
    | _ => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.ashr]
def unexpandIntBinaryOpAshr : Unexpander
  | `($_ $a:ident) =>
    match a.getId with
    | `true => `([llvm-int-bin-op| ashr exact])
    | `false => `([llvm-int-bin-op| ashr])
    | _ => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.urem]
def unexpandIntBinaryOpUrem : Unexpander
  | `($_) => `([llvm-int-bin-op| urem])

@[app_unexpander IntBinaryOp.srem]
def unexpandIntBinaryOpSrem : Unexpander
  | `($_) => `([llvm-int-bin-op| srem])

@[app_unexpander IntBinaryOp.and]
def unexpandIntBinaryOpAnd : Unexpander
  | `($_) => `([llvm-int-bin-op| and])

@[app_unexpander IntBinaryOp.or]
def unexpandIntBinaryOpOr : Unexpander
  | `($_ $a:ident) =>
    match a.getId with
    | `true => `([llvm-int-bin-op| or disjoint])
    | `false => `([llvm-int-bin-op| or])
    | _ => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.xor]
def unexpandIntBinaryOpXor : Unexpander
  | `($_) => `([llvm-int-bin-op| xor])

@[app_unexpander ConversionOp.trunc]
def unexpandConversionOpTrunc : Unexpander
  | `($_ $a:ident $b:ident) =>
    match a.getId, b.getId with
    | `true, `true => `([llvm-conversion-op| trunc nuw nsw])
    | `true, `false => `([llvm-conversion-op| trunc nuw])
    | `false, `true => `([llvm-conversion-op| trunc nsw])
    | `false, `false => `([llvm-conversion-op| trunc])
    | _, _ => throw ()
  | _ => throw ()

@[app_unexpander ConversionOp.zext]
def unexpandConversionOpZext : Unexpander
  | `($_ $a:ident) =>
    match a.getId with
    | `true => `([llvm-conversion-op| zext nneg])
    | `false => `([llvm-conversion-op| zext])
    | _ => throw ()
  | _ => throw ()

@[app_unexpander ConversionOp.sext]
def unexpandConversionOpSext : Unexpander
  | `($_) => `([llvm-conversion-op| sext])

@[app_unexpander Exp.identifier]
def unexpandExpIdentifier : Unexpander
  | `($_ $id) =>
    match asIdentifier? id with
    | some id => `([llvm-exp| $id:nanollvm_identifier])
    | none => throw ()
  | _ => throw ()

@[app_unexpander Exp.bool]
def unexpandExpBool : Unexpander
  | `($_ $a:ident) =>
    match a.getId with
    | `true => `([llvm-exp| true])
    | `false => `([llvm-exp| false])
    | _ => throw ()
  | _ => throw ()

@[app_unexpander Exp.int]
def unexpandExpInt : Unexpander
  | `($_ (Int.ofNat $n:num)) => `([llvm-exp| $n:num])
  | `($_ (Int.ofNat $id:ident)) => `([llvm-exp| <$id:ident:int>])
  | `($_ $id:ident) => `([llvm-exp| <$id:ident:int>])
  | `($_ $n) =>
    match n with
    | `($_ $n:num) => `([llvm-exp| $n:num])
    | _ => throw ()
  | _ => throw ()

@[app_unexpander Exp.null]
def unexpandExpNull : Unexpander
  | `($_) => `([llvm-exp| null])

@[app_unexpander Exp.undef]
def unexpandExpUndef : Unexpander
  | `($_ $n) =>
    match asRawId? n with
    | some rawid => `([llvm-exp| undef!$rawid])
    | none => `([llvm-exp| undef])
  | _ => throw ()

@[app_unexpander Exp.poison]
def unexpandExpPoison : Unexpander
  | `($_) => `([llvm-exp| poison])

@[app_unexpander Instruction.intBinaryOp]
def unexpandInstructionIntBinaryOp : Unexpander
  | `($_ $op $ty $v1 $v2) =>
    match asIntBinOp? op, asType? ty, asExp? v1, asExp? v2 with
    | some op, some ty, some v1, some v2 =>
      `([llvm-instruction| $op:nanollvm_int_bin_op $ty:nanollvm_type $v1:nanollvm_exp, $v2:nanollvm_exp])
    | _, _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander Instruction.conversionOp]
def unexpandInstructionConversionOp : Unexpander
  | `($_ $op $fromTy $v $toTy) =>
    match asConversionOp? op, asType? fromTy, asExp? v, asType? toTy with
    | some op, some fromTy, some v, some toTy =>
      `([llvm-instruction| $op:nanollvm_conversion_op $fromTy:nanollvm_type $v:nanollvm_exp to $toTy:nanollvm_type])
    | _, _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander Instruction.freeze]
def unexpandInstructionFreeze : Unexpander
  | `($_ ⟨$ty, $v⟩) | `($_ (($ty, $v))) =>
    match asType? ty, asExp? v with
    | some ty, some v => `([llvm-instruction| freeze $ty:nanollvm_type $v:nanollvm_exp])
    | _, _ => throw ()
  | `($_ $tv) =>
    match tv with
    | `(⟨$ty, $v⟩) | `(($ty, $v)) =>
      match asType? ty, asExp? v with
      | some ty, some v => `([llvm-instruction| freeze $ty:nanollvm_type $v:nanollvm_exp])
      | _, _ => throw ()
    | _ => throw ()
  | _ => throw ()

@[app_unexpander Terminator.retVoid]
def unexpandTerminatorRetVoid : Unexpander
  | `($_) => `([llvm-terminator| ret void])

@[app_unexpander Terminator.ret]
def unexpandTerminatorRet : Unexpander
  | `($_ $tv) =>
    match tv with
    | `(($ty, $v)) =>
      match asType? ty, asExp? v with
      | some ty, some v => `([llvm-terminator| ret $ty:nanollvm_type $v:nanollvm_exp])
      | _, _ => throw ()
    | _ => throw ()
  | _ => throw ()

@[app_unexpander Declaration.mk]
def unexpandDeclarationMk : Unexpander
  | `($_ $name $ty) =>
    match asRawId? name, asType? ty with
    | some name, some ty =>
      match ty with
      | `(nanollvm_type| $retTy($args,*)) =>
        let retTy : TSyntax `nanollvm_type := ⟨retTy⟩
        let args : Array (TSyntax `nanollvm_type) := args.getElems.map (fun x => ⟨x⟩)
        let args : Syntax.TSepArray `nanollvm_type "," := args
        `([llvm-declaration| declare $retTy:nanollvm_type @$name:nanollvm_rawid($args,*)])
      | _ => throw ()
    | _, _ => throw ()
  | _ => throw ()

-- Unexpander for nanollvm_codeline
@[app_unexpander Prod.mk]
def unexpandProdMk : Unexpander
  | `($_ $id $instr) =>
    match asInstructionId? id, asInstruction? instr with
    | some id, some instr =>
      match id with
      | `(nanollvm_instruction_id| %$id:nanollvm_rawid) =>
        `(nanollvm_codeline| %$id:nanollvm_rawid = $instr:nanollvm_instruction)
      | `(nanollvm_instruction_id| void ($_:num)) =>
        `(nanollvm_codeline| $instr:nanollvm_instruction)
      | _ => throw ()
    | _, _ => throw ()
  | _ => throw ()

-- Unexpander for nanollvm_code
@[app_unexpander List.cons]
def unexpandCodeListCons : Unexpander
  | `($(_) $x $tail) => do
    let x : TSyntax `nanollvm_codeline ← asCodeline x
    let xs : Array (TSyntax `nanollvm_codeline) ←
      match tail with
      | `([llvm-code| $xs:nanollvm_codeline*]) =>
        xs.mapM asCodeline
      | `([]) =>
        pure #[]
      | `([$xs,*]) =>
        xs.getElems.mapM asCodeline
      | _ => throw ()
    let code : Syntax.TSepArray `nanollvm_codeline "\n" := #[x] ++ xs
    `([llvm-code| $code:nanollvm_codeline*])
  | _ => throw ()

@[app_unexpander Block.mk]
def unexpandBlockMk : Unexpander
  | `($_ $id $code $term) => do
    let id ←
      match asRawId? id with
      | some id => pure id
      | none => throw ()
    let code : TSyntax `nanollvm_code ←
      match asCode? code with
      | some code => pure code
      | none => throw ()
    let term : TSyntax `nanollvm_terminator ←
      match term with
      | `(($_, $term)) =>
        match asTerminator? term with
        | some term => pure term
        | none => throw ()
      | _ => throw ()
    `([llvm-block| $id:nanollvm_rawid:
$code:nanollvm_code
$term:nanollvm_terminator])
  | _ => throw ()

@[app_unexpander Definition.mk]
def unexpandDefinitionMk : Unexpander
  | `($_ $proto [$argVals,*] $body) => do
    match asDeclaration? proto, asBlock? body with
    | some proto, some body =>
      match proto with
      | `(nanollvm_declaration| declare $retTy:nanollvm_type @$name:nanollvm_rawid($args,*)) =>
        let argVals : Option (Array (TSyntax `nanollvm_rawid)) := argVals.getElems.mapM asRawId?
        let argVals ←
          match argVals with
          | some argVals => pure argVals
          | none => throw ()
        let args : Array (TSyntax `nanollvm_type) := args.getElems.map (fun x => ⟨x⟩)
        let args : Array (TSyntax `nanollvm_arg) ← args.zip argVals |>.mapM (fun ⟨t, v⟩ => `(nanollvm_arg| $t:nanollvm_type %$v:nanollvm_rawid))
        let args : Syntax.TSepArray `nanollvm_arg "," := args
        `([llvm-definition| define $retTy:nanollvm_type @$name:nanollvm_rawid($args,*) {
          $body:nanollvm_block
        }])
      | _ => throw ()
    | _, _ => throw ()
  | _ => throw ()

@[app_unexpander TopLevelEntity.declaration]
def unexpandTopLevelEntityDeclaration : Unexpander
  | `($_ $decl) =>
    match asDeclaration? decl with
    | some decl => `([llvm-entity| $decl:nanollvm_declaration])
    | none => throw ()
  | _ => throw ()

@[app_unexpander TopLevelEntity.definition]
def unexpandTopLevelEntityDefinition : Unexpander
  | `($_ $defn) =>
    match asDefinition? defn with
    | some defn => `([llvm-entity| $defn:nanollvm_definition])
    | none => throw ()
  | _ => throw ()

@[app_unexpander TopLevel.mk]
def unexpandTopLevelMk : Unexpander
  | `($_ [$h]) =>
    match asEntity? h with
    | some h =>
      match h with
      | `(nanollvm_entity| $entity:nanollvm_declaration) =>
        `([llvm| $entity:nanollvm_declaration])
      | `(nanollvm_entity| $entity:nanollvm_definition) =>
        `([llvm| $entity:nanollvm_definition])
      | _ => throw ()
    | _ => throw ()
  | `($_ [$els,*]) => do
    let els : Array (TSyntax `nanollvm_entity) ← els.getElems.mapM (fun h => do
      match asEntity? h with
      | some h =>
        match h with
        | `(nanollvm_entity| $entity:nanollvm_declaration) =>
          `(nanollvm_entity| $entity:nanollvm_declaration)
        | `(nanollvm_entity| $entity:nanollvm_definition) =>
          `(nanollvm_entity| $entity:nanollvm_definition)
        | _ => throw ()
      | _ => throw ()
    )
    let els : Syntax.TSepArray `nanollvm_entity "\n" := els
    `([llvm|
$[$els]*])
  | _ => throw ()

end LeanNanoLlvm.AST
