import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.AST

open Lean PrettyPrinter PrettyPrinter.Delaborator SubExpr

@[app_unexpander RawId.name]
def unexpandRawIdName : Unexpander
  | `($_ $s:str) =>
    let name := mkIdent $ Name.mkSimple s.getString
    `(nanollvm_rawid| $name:ident)
  | _ => throw ()

@[app_unexpander RawId.anonymous]
def unexpandRawIdAnonymous : Unexpander
  | `($_ $n:num) => `(nanollvm_rawid| $n:num)
  | _ => throw ()

@[app_unexpander Identifier.global_id]
def unexpandIdentifierGlobalId : Unexpander
  | `($_ $id) =>
    let id : TSyntax `nanollvm_rawid := ⟨id⟩
    `(nanollvm_identifier| @ $id:nanollvm_rawid)
  | _ => throw ()

@[app_unexpander Identifier.local_id]
def unexpandIdentifierLocalId : Unexpander
  | `($_ $id) =>
    let id : TSyntax `nanollvm_rawid := ⟨id⟩
    `(nanollvm_identifier| % $id:nanollvm_rawid)
  | _ => throw ()

@[app_unexpander LlvmRetType.void]
def unexpandLlvmRetTypeVoid : Unexpander
  | `($_) => `(nanollvm_type| void)

@[app_unexpander LlvmRetType.ret]
def unexpandLlvmRetTypeRet : Unexpander
  | `($_ $ty) =>
    let ty : TSyntax `nanollvm_type := ⟨ty⟩
    `(nanollvm_type| $ty)
  | _ => throw ()

@[app_unexpander Width.concrete]
def unexpandWidthConcrete : Unexpander
  | `($_ $w:num) =>
    let w := mkIdent $ Name.mkSimple s!"i{w.getNat}"
    `(nanollvm_type| $w:ident)
  | _ => throw ()

@[app_unexpander LlvmType.int]
def unexpandLlvmTypeInt : Unexpander
  | `($_ $w) =>
    let w : TSyntax `nanollvm_type := ⟨w⟩
    `(nanollvm_type| $w)
  | _ => throw ()

@[app_unexpander LlvmType.function]
def unexpandLlvmTypeFunction : Unexpander
  | `($_ $retTy [$args,*]) =>
    let retTy : TSyntax `nanollvm_type := ⟨retTy⟩
    let args : Array (TSyntax `nanollvm_type) := args.getElems.map (fun x => ⟨x⟩)
    let args : Syntax.TSepArray `nanollvm_type "," := args
    `(nanollvm_type| $retTy($args,*))
  | _ => throw ()

@[app_unexpander IntBinaryOp.add]
def unexpandIntBinaryOpAdd : Unexpander
  | `($_ $a:ident $b:ident) =>
    match a.getId, b.getId with
    | `true, `true => `(nanollvm_int_bin_op| add nuw nsw)
    | `true, `false => `(nanollvm_int_bin_op| add nuw)
    | `false, `true => `(nanollvm_int_bin_op| add nsw)
    | `false, `false => `(nanollvm_int_bin_op| add)
    | _, _ => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.sub]
def unexpandIntBinaryOpSub : Unexpander
  | `($_ $a:ident $b:ident) =>
    match a.getId, b.getId with
    | `true, `true => `(nanollvm_int_bin_op| sub nuw nsw)
    | `true, `false => `(nanollvm_int_bin_op| sub nuw)
    | `false, `true => `(nanollvm_int_bin_op| sub nsw)
    | `false, `false => `(nanollvm_int_bin_op| sub)
    | _, _ => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.mul]
def unexpandIntBinaryOpMul : Unexpander
  | `($_ $a:ident $b:ident) =>
    match a.getId, b.getId with
    | `true, `true => `(nanollvm_int_bin_op| mul nuw nsw)
    | `true, `false => `(nanollvm_int_bin_op| mul nuw)
    | `false, `true => `(nanollvm_int_bin_op| mul nsw)
    | `false, `false => `(nanollvm_int_bin_op| mul)
    | _, _ => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.shl]
def unexpandIntBinaryOpShl : Unexpander
  | `($_ $a:ident $b:ident) =>
    match a.getId, b.getId with
    | `true, `true => `(nanollvm_int_bin_op| shl nuw nsw)
    | `true, `false => `(nanollvm_int_bin_op| shl nuw)
    | `false, `true => `(nanollvm_int_bin_op| shl nsw)
    | `false, `false => `(nanollvm_int_bin_op| shl)
    | _, _ => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.udiv]
def unexpandIntBinaryOpUdiv : Unexpander
  | `($_ $a:ident) =>
    match a.getId with
    | `true => `(nanollvm_int_bin_op| udiv exact)
    | `false => `(nanollvm_int_bin_op| udiv)
    | _ => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.sdiv]
def unexpandIntBinaryOpSdiv : Unexpander
  | `($_ $a:ident) =>
    match a.getId with
    | `true => `(nanollvm_int_bin_op| sdiv exact)
    | `false => `(nanollvm_int_bin_op| sdiv)
    | _ => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.lshr]
def unexpandIntBinaryOpLshr : Unexpander
  | `($_ $a:ident) =>
    match a.getId with
    | `true => `(nanollvm_int_bin_op| lshr exact)
    | `false => `(nanollvm_int_bin_op| lshr)
    | _ => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.ashr]
def unexpandIntBinaryOpAshr : Unexpander
  | `($_ $a:ident) =>
    match a.getId with
    | `true => `(nanollvm_int_bin_op| ashr exact)
    | `false => `(nanollvm_int_bin_op| ashr)
    | _ => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.urem]
def unexpandIntBinaryOpUrem : Unexpander
  | `($_) => `(nanollvm_int_bin_op| urem)

@[app_unexpander IntBinaryOp.srem]
def unexpandIntBinaryOpSrem : Unexpander
  | `($_) => `(nanollvm_int_bin_op| srem)

@[app_unexpander IntBinaryOp.and]
def unexpandIntBinaryOpAnd : Unexpander
  | `($_) => `(nanollvm_int_bin_op| and)

@[app_unexpander IntBinaryOp.or]
def unexpandIntBinaryOpOr : Unexpander
  | `($_ $a:ident) =>
    match a.getId with
    | `true => `(nanollvm_int_bin_op| or disjoint)
    | `false => `(nanollvm_int_bin_op| or)
    | _ => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.xor]
def unexpandIntBinaryOpXor : Unexpander
  | `($_) => `(nanollvm_int_bin_op| xor)

@[app_unexpander ConversionOp.trunc]
def unexpandConversionOpTrunc : Unexpander
  | `($_ $a:ident $b:ident) =>
    match a.getId, b.getId with
    | `true, `true => `(nanollvm_conversion_op| trunc nuw nsw)
    | `true, `false => `(nanollvm_conversion_op| trunc nuw)
    | `false, `true => `(nanollvm_conversion_op| trunc nsw)
    | `false, `false => `(nanollvm_conversion_op| trunc)
    | _, _ => throw ()
  | _ => throw ()

@[app_unexpander ConversionOp.zext]
def unexpandConversionOpZext : Unexpander
  | `($_ $a:ident) =>
    match a.getId with
    | `true => `(nanollvm_conversion_op| zext nneg)
    | `false => `(nanollvm_conversion_op| zext)
    | _ => throw ()
  | _ => throw ()

@[app_unexpander ConversionOp.sext]
def unexpandConversionOpSext : Unexpander
  | `($_) => `(nanollvm_conversion_op| sext)

@[app_unexpander Exp.identifier]
def unexpandExpIdentifier : Unexpander
  | `($_ $id) =>
    let id : TSyntax `nanollvm_identifier := ⟨id⟩
    `(nanollvm_exp| $id:nanollvm_identifier)
  | _ => throw ()

@[app_unexpander Exp.bool]
def unexpandExpBool : Unexpander
  | `($_ $a:ident) =>
    match a.getId with
    | `true => `(nanollvm_exp| true)
    | `false => `(nanollvm_exp| false)
    | _ => throw ()
  | _ => throw ()

@[app_unexpander Exp.int]
def unexpandExpInt : Unexpander
  | `($_ (Int.ofNat $n:num)) => `(nanollvm_exp| $n:num)
  | `($_ $n) =>
    match n with
    | `($_ $n:num) => `(nanollvm_exp| $n:num)
    | _ => throw ()
  | _ => throw ()

@[app_unexpander Exp.null]
def unexpandExpNull : Unexpander
  | `($_) => `(nanollvm_exp| null)

@[app_unexpander Exp.undef]
def unexpandExpUndef : Unexpander
  | `($_) => `(nanollvm_exp| undef)

@[app_unexpander Exp.poison]
def unexpandExpPoison : Unexpander
  | `($_) => `(nanollvm_exp| poison)

@[app_unexpander Instruction.intBinaryOp]
def unexpandInstructionIntBinaryOp : Unexpander
  | `($_ $op $ty $v1 $v2) => do
    let op : TSyntax `nanollvm_int_bin_op := ⟨op⟩
    let ty : TSyntax `nanollvm_type := ⟨ty⟩
    let v1 : TSyntax `nanollvm_exp := ⟨v1⟩
    let v2 : TSyntax `nanollvm_exp := ⟨v2⟩
    `(nanollvm_instruction| $op:nanollvm_int_bin_op $ty:nanollvm_type $v1:nanollvm_exp, $v2:nanollvm_exp)
  | _ => throw ()

@[app_unexpander Instruction.conversionOp]
def unexpandInstructionConversionOp : Unexpander
  | `($_ $op $fromTy $v $toTy) =>
    let op : TSyntax `nanollvm_conversion_op := ⟨op⟩
    let fromTy : TSyntax `nanollvm_type := ⟨fromTy⟩
    let v : TSyntax `nanollvm_exp := ⟨v⟩
    let toTy : TSyntax `nanollvm_type := ⟨toTy⟩
    `(nanollvm_instruction| $op:nanollvm_conversion_op $fromTy:nanollvm_type $v:nanollvm_exp to $toTy:nanollvm_type)
  | _ => throw ()

@[app_unexpander Instruction.freeze]
def unexpandInstructionFreeze : Unexpander
  | `($_ ⟨$ty, $v⟩) | `($_ (($ty, $v)))   =>
    let ty : TSyntax `nanollvm_type := ⟨ty⟩
    let v : TSyntax `nanollvm_exp := ⟨v⟩
    `(nanollvm_instruction| freeze $ty:nanollvm_type $v:nanollvm_exp)
  | `($_ $tv) =>
    match tv with
    | `(⟨$ty, $v⟩) | `(($ty, $v)) =>
      let ty : TSyntax `nanollvm_type := ⟨ty⟩
      let v : TSyntax `nanollvm_exp := ⟨v⟩
      `(nanollvm_instruction| freeze $ty:nanollvm_type $v:nanollvm_exp)
    | _ => throw ()
  | _ => throw ()

@[app_unexpander Terminator.retVoid]
def unexpandTerminatorRetVoid : Unexpander
  | `($_) => `(nanollvm_terminator| ret void)

@[app_unexpander Terminator.ret]
def unexpandTerminatorRet : Unexpander
  | `($_ $tv) =>
    match tv with
    | `(($ty, $v)) =>
      let ty : TSyntax `nanollvm_type := ⟨ty⟩
      let v : TSyntax `nanollvm_exp := ⟨v⟩
      `(nanollvm_terminator| ret $ty:nanollvm_type $v:nanollvm_exp)
    | _ => throw ()
  | _ => throw ()

@[app_unexpander Prod.mk]
def unexpandProdMk : Unexpander
  | `($_ $id $val) =>
    match id with
    | `(InstructionId.id $rid) =>
      let rid : TSyntax `nanollvm_rawid := ⟨rid⟩
      let instr : TSyntax `nanollvm_instruction := ⟨val⟩
      `(nanollvm_codeline| %$rid:nanollvm_rawid = $instr:nanollvm_instruction)
    | `(InstructionId.void $_) =>
      let term : TSyntax `nanollvm_terminator := ⟨val⟩
      `(nanollvm_terminator| $term:nanollvm_terminator)
    | _ => throw ()
  | _ => throw ()

@[app_unexpander Declaration.mk]
def unexpandDeclarationMk : Unexpander
  | `($_ $name $ty) =>
      let name : TSyntax `nanollvm_rawid := ⟨name⟩
      match ty with
      | `(nanollvm_type| $retTy($args,*)) =>
        let retTy : TSyntax `nanollvm_type := ⟨retTy⟩
        let args : Array (TSyntax `nanollvm_type) := args.getElems.map (fun x => ⟨x⟩)
        let args : Syntax.TSepArray `nanollvm_type "," := args
        `(nanollvm_declaration| declare $retTy:nanollvm_type @$name:nanollvm_rawid($args,*))
      | _ => throw ()
  | _ => throw ()

@[app_unexpander Block.mk]
def unexpandBlockMk : Unexpander
  | `($_ $id [$code,*] $term) =>
    let id : TSyntax `nanollvm_rawid := ⟨id⟩
    let code : Array (TSyntax `nanollvm_codeline) := code.getElems.map (fun x => ⟨x⟩)
    let code : Syntax.TSepArray `nanollvm_codeline "\n" := code
    let term : TSyntax `nanollvm_terminator := ⟨term⟩
    `(nanollvm_block| $id:nanollvm_rawid:
$code:nanollvm_codeline*
$term:nanollvm_terminator)
  | _ => throw ()

@[app_unexpander Definition.mk]
def unexpandDefinitionMk : Unexpander
  | `($_ $proto [$argVals,*] $body) =>
    let body : TSyntax `term := ⟨body⟩
    match proto with
    | `(nanollvm_declaration| declare $retTy:nanollvm_type @$name:nanollvm_rawid($args,*)) => do
      let body : TSyntax `nanollvm_block := ⟨body⟩
      let argVals : Array (TSyntax `nanollvm_rawid) := argVals.getElems.map (fun x => ⟨x⟩)
      let args : Array (TSyntax `nanollvm_type) := args.getElems.map (fun x => ⟨x⟩)
      let args : Array (TSyntax `nanollvm_arg) ← args.zip argVals |>.mapM (fun ⟨t, v⟩ => `(nanollvm_arg| $t:nanollvm_type %$v:nanollvm_rawid))
      let args : Syntax.TSepArray `nanollvm_arg "," := args
      `(nanollvm_definition| define $retTy:nanollvm_type @$name:nanollvm_rawid($args,*) {
        $body:nanollvm_block
      })
    | _ => throw ()
  | _ => throw ()

@[app_unexpander TopLevelEntity.declaration]
def unexpandTopLevelEntityDeclaration : Unexpander
  | `($_ $decl) =>
    let decl : TSyntax `nanollvm_declaration := ⟨decl⟩
    `(nanollvm_entity| $decl:nanollvm_declaration)
  | _ => throw ()

@[app_unexpander TopLevelEntity.definition]
def unexpandTopLevelEntityDefinition : Unexpander
  | `($_ $defn) =>
    let defn : TSyntax `nanollvm_definition := ⟨defn⟩
    `(nanollvm_entity| $defn:nanollvm_definition)
  | _ => throw ()

private partial def unexpandListTail : Syntax → UnexpandM (TSyntaxArray `nanollvm_entity)
  | `(nanollvm_entity| $decl:nanollvm_declaration) => do
    let e ← `(nanollvm_entity|$decl:nanollvm_declaration)
    pure (#[e])
  | `(nanollvm_entity| $decl:nanollvm_definition) => do
    let e ← `(nanollvm_entity|$decl:nanollvm_definition)
    pure (#[e])
  | `($_ $h $t) => do
    match h with
    | `(nanollvm_entity| $decl:nanollvm_declaration) => do
      let e ← `(nanollvm_entity|$decl:nanollvm_declaration)
      let t ← unexpandListTail t
      pure (#[e].append t)
    | `(nanollvm_entity| $decl:nanollvm_definition) => do
      let e ← `(nanollvm_entity|$decl:nanollvm_definition)
      let t ← unexpandListTail t
      pure (#[e].append t)
    | _ => throw ()
  | _ => throw ()


@[app_unexpander List.cons]
def unexpandListCons : Unexpander
  | `($_ $h []) =>
    match h with
    | `(nanollvm_entity| $decl:nanollvm_declaration) =>
      `(nanollvm|$decl:nanollvm_declaration)
    | `(nanollvm_entity| $decl:nanollvm_definition) =>
      `(nanollvm|$decl:nanollvm_definition)
    | _ => throw ()
  | `($_ $h $t) => do
    let t ← unexpandListTail t
    match h with
    | `(nanollvm_entity| $decl:nanollvm_declaration) =>
      `(nanollvm|$decl:nanollvm_declaration $t*)
    | `(nanollvm_entity| $decl:nanollvm_definition) =>
      `(nanollvm|$decl:nanollvm_definition $t*)
    | _ => throw ()
  | _ => throw ()

set_option pp.rawOnError true
#check [llvm|
declare i32 @g(i32, i8)
]

#check [llvm|
declare i32 @g(i32, i8)
-- declare i32 @g(i32, i8)
-- declare i32 @g2(i32, i8)
define i32 @f(i8 %a) {
B:
  %i0 = add i32 0, 1
  freeze i32 %i0
  %x = add nsw i32 %i0, %i0
  ret i32 %x
}
]

end LeanNanoLlvm.AST
