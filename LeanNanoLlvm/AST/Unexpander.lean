import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.AST

open Lean PrettyPrinter PrettyPrinter.Delaborator SubExpr
open scoped LeanNanoLlvm.AST.Syntax

/-! ### Unexpander Extraction Helpers -/

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

private def asGlobal? (stx : Syntax) : Option (TSyntax `nanollvm_global) :=
  match stx with
  | `([llvm-global| $gv:nanollvm_global]) => some gv
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

private def asCode? (stx : Syntax) : Option (TSyntax `nanollvm_code) :=
  match stx with
  | `([llvm-code| $code:nanollvm_code]) => some ⟨code⟩
  | _ => none

private def asBool? (stx : Syntax) : Option Bool :=
  match stx with
  | `($id:ident) =>
    match id.getId with
    | `true | ``Bool.true => some true
    | `false | ``Bool.false => some false
    | _ => none
  | _ => none

private def asTypedExp? (stx : Syntax) : UnexpandM (TSyntax `nanollvm_typed_exp) := do
  match stx with
  | `(($ty, $e)) | `(⟨$ty, $e⟩) =>
    match asType? ty, asExp? e with
    | some ty, some e => `(nanollvm_typed_exp| $ty:nanollvm_type $e:nanollvm_exp)
    | _, _ => throw ()
  | _ => throw ()

private def asSignedInt? (stx : Syntax) : UnexpandM (TSyntax `nanollvm_signed_int) := do
  let stx := match stx with | `(($x)) => x.raw | _ => stx
  match stx with
  | `(Int.ofNat $n:num) | `($n:num) => `(nanollvm_signed_int| $n:num)
  | `(-$n:num) => `(nanollvm_signed_int| -$n:num)
  | `(Int.negSucc $n:num) =>
    let k := Syntax.mkNumLit (toString (n.getNat + 1))
    `(nanollvm_signed_int| -$k:num)
  | _ => throw ()

private def unexpandFMFFlags (stx : Syntax) : UnexpandM (Array (TSyntax `nanollvm_fmf_flag)) := do
  match stx with
  | `({ }) | `(FastMathFlags.none) => pure #[]
  | `(FastMathFlags.fast) => pure #[← `(nanollvm_fmf_flag| fast)]
  | `({ $fields,* }) =>
    let mut out : Array (TSyntax `nanollvm_fmf_flag) := #[]
    for f in fields.getElems do
      match f with
      | `(Parser.Term.structInstField| $nm:ident := $val) =>
        if asBool? val == some true then
          let flag ← match nm.getId.eraseMacroScopes with
            | `nnan => `(nanollvm_fmf_flag| nnan)
            | `ninf => `(nanollvm_fmf_flag| ninf)
            | `nsz => `(nanollvm_fmf_flag| nsz)
            | `arcp => `(nanollvm_fmf_flag| arcp)
            | `contract => `(nanollvm_fmf_flag| contract)
            | `afn => `(nanollvm_fmf_flag| afn)
            | `reassoc => `(nanollvm_fmf_flag| reassoc)
            | _ => throw ()
          out := out.push flag
      | _ => throw ()
    pure out
  | _ => throw ()

private def unexpandGEPFlags (stx : Syntax) : UnexpandM (Array (TSyntax `nanollvm_gep_flag)) := do
  match stx with
  | `({ }) | `(GEPFlags.none) => pure #[]
  | `(GEPFlags.mkInbounds) => pure #[← `(nanollvm_gep_flag| inbounds)]
  | `({ $fields,* }) =>
    let mut hasInbounds := false
    let mut hasNusw := false
    let mut hasNuw := false
    for f in fields.getElems do
      match f with
      | `(Parser.Term.structInstField| $nm:ident := $val) =>
        if asBool? val == some true then
          match nm.getId.eraseMacroScopes with
          | `inbounds => hasInbounds := true
          | `nusw => hasNusw := true
          | `nuw => hasNuw := true
          | _ => throw ()
      | _ => throw ()
    let mut out : Array (TSyntax `nanollvm_gep_flag) := #[]
    if hasInbounds then out := out.push (← `(nanollvm_gep_flag| inbounds))
    else if hasNusw then out := out.push (← `(nanollvm_gep_flag| nusw))
    if hasNuw then out := out.push (← `(nanollvm_gep_flag| nuw))
    pure out
  | _ => throw ()

private def unexpandValueAttr (stx : Syntax) : UnexpandM (TSyntax `nanollvm_value_attr) := do
  match stx with
  | `($id:ident) =>
    match id.getId with
    | ``ValueAttr.noundef | `ValueAttr.noundef | `noundef => `(nanollvm_value_attr| noundef)
    | ``ValueAttr.nonnull | `ValueAttr.nonnull | `nonnull => `(nanollvm_value_attr| nonnull)
    | _ => throw ()
  | `($f:ident $n:num) =>
    match f.getId with
    | ``ValueAttr.align | `ValueAttr.align | `align => `(nanollvm_value_attr| align $n:num)
    | ``ValueAttr.dereferenceable | `ValueAttr.dereferenceable | `dereferenceable =>
      `(nanollvm_value_attr| dereferenceable($n:num))
    | ``ValueAttr.dereferenceableOrNull | `ValueAttr.dereferenceableOrNull | `dereferenceableOrNull =>
      `(nanollvm_value_attr| dereferenceable_or_null($n:num))
    | ``ValueAttr.nofpclass | `ValueAttr.nofpclass | `nofpclass =>
      `(nanollvm_value_attr| nofpclass($n:num))
    | _ => throw ()
  | `($f:ident $lo $hi) =>
    match f.getId with
    | ``ValueAttr.range | `ValueAttr.range | `range =>
      let loS ← asSignedInt? lo
      let hiS ← asSignedInt? hi
      `(nanollvm_value_attr| range($loS:nanollvm_signed_int, $hiS:nanollvm_signed_int))
    | _ => throw ()
  | `($f:ident $ty) =>
    match f.getId, asType? ty with
    | ``ValueAttr.byval, some ty | `ValueAttr.byval, some ty | `byval, some ty =>
      `(nanollvm_value_attr| byval($ty:nanollvm_type))
    | _, _ => throw ()
  | _ => throw ()

private def unexpandValueAttrList (stx : Syntax) : UnexpandM (Array (TSyntax `nanollvm_value_attr)) := do
  match stx with
  | `([]) => pure #[]
  | `([$attrs,*]) => attrs.getElems.mapM unexpandValueAttr
  | _ => throw ()

private def unexpandICmpPred (stx : Syntax) : UnexpandM (TSyntax `ident) := do
  match stx with
  | `($id:ident) =>
    let nm? := match id.getId with
      | ``ICmpPred.eq  | `eq  => some `eq
      | ``ICmpPred.ne  | `ne  => some `ne
      | ``ICmpPred.ugt | `ugt => some `ugt
      | ``ICmpPred.uge | `uge => some `uge
      | ``ICmpPred.ult | `ult => some `ult
      | ``ICmpPred.ule | `ule => some `ule
      | ``ICmpPred.sgt | `sgt => some `sgt
      | ``ICmpPred.sge | `sge => some `sge
      | ``ICmpPred.slt | `slt => some `slt
      | ``ICmpPred.sle | `sle => some `sle
      | _ => none
    match nm? with
    | some nm => pure (mkIdent nm)
    | none => throw ()
  | _ => throw ()

private def unexpandFCmpPred (stx : Syntax) : UnexpandM (TSyntax `ident) := do
  match stx with
  | `($id:ident) =>
    let nm? := match id.getId with
      | ``FCmpPred.ffalse | `ffalse => some `false
      | ``FCmpPred.oeq    | `oeq    => some `oeq
      | ``FCmpPred.ogt    | `ogt    => some `ogt
      | ``FCmpPred.oge    | `oge    => some `oge
      | ``FCmpPred.olt    | `olt    => some `olt
      | ``FCmpPred.ole    | `ole    => some `ole
      | ``FCmpPred.one    | `one    => some `one
      | ``FCmpPred.ord    | `ord    => some `ord
      | ``FCmpPred.ueq    | `ueq    => some `ueq
      | ``FCmpPred.ugt    | `ugt    => some `ugt
      | ``FCmpPred.uge    | `uge    => some `uge
      | ``FCmpPred.ult    | `ult    => some `ult
      | ``FCmpPred.ule    | `ule    => some `ule
      | ``FCmpPred.une    | `une    => some `une
      | ``FCmpPred.uno    | `uno    => some `uno
      | ``FCmpPred.ftrue  | `ftrue  => some `true
      | _ => none
    match nm? with
    | some nm => pure (mkIdent nm)
    | none => throw ()
  | _ => throw ()

/-! ### Identifiers -/

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
  | `($_ $n:num) => `([llvm-instruction-id| void ($n:num)])
  | _ => throw ()

/-! ### Types -/

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

@[app_unexpander LlvmType.int]
def unexpandLlvmTypeInt : Unexpander
  | `($_ $w:num) =>
    let id := mkIdent $ Name.mkSimple s!"i{w.getNat}"
    `([llvm-type| $id:ident])
  | `($_ $w:term) =>
    `([llvm-type| i$($w:term)])
  | _ => throw ()

@[app_unexpander LlvmType.float]
def unexpandLlvmTypeFloat : Unexpander
  | `($_ $ft:ident) =>
    let name? := match ft.getId with
      | ``FloatType.half   | `half   => some `half
      | ``FloatType.bfloat | `bfloat => some `bfloat
      | ``FloatType.float  | `float  => some `float
      | ``FloatType.double | `double => some `double
      | ``FloatType.fp128  | `fp128  => some `fp128
      | _ => none
    match name? with
    | some nm =>
      let id := mkIdent nm
      `([llvm-type| $id:ident])
    | none => throw ()
  | _ => throw ()

@[app_unexpander LlvmType.ptr]
def unexpandLlvmTypePtr : Unexpander
  | `($_ 0) =>
    let id := mkIdent `ptr
    `([llvm-type| $id:ident])
  | `($_ $n:num) => `([llvm-type| ptr addrspace($n:num)])
  | `($_) =>
    let id := mkIdent `ptr
    `([llvm-type| $id:ident])

@[app_unexpander LlvmType.vector]
def unexpandLlvmTypeVector : Unexpander
  | `($_ $n:num $elem) =>
    match asType? elem with
    | some elem => `([llvm-type| <$n:num x $elem:nanollvm_type>])
    | none => throw ()
  | _ => throw ()

@[app_unexpander LlvmType.array]
def unexpandLlvmTypeArray : Unexpander
  | `($_ $n:num $elem) =>
    match asType? elem with
    | some elem => `([llvm-type| [$n:num x $elem:nanollvm_type]])
    | none => throw ()
  | _ => throw ()

@[app_unexpander LlvmType.struct]
def unexpandLlvmTypeStruct : Unexpander
  | `($_ $packed [$fields,*]) =>
    match asBool? packed, fields.getElems.mapM asType? with
    | some false, some fs =>
      let fs : Syntax.TSepArray `nanollvm_type "," := fs
      `([llvm-type| { $fs,* }])
    | some true, some fs =>
      let fs : Syntax.TSepArray `nanollvm_type "," := fs
      `([llvm-type| <{ $fs,* }>])
    | _, _ => throw ()
  | _ => throw ()

@[app_unexpander LlvmType.function]
def unexpandLlvmTypeFunction : Unexpander
  | `($_ $retTy [$args,*] $isVarArg) => do
    match asType? retTy, args.getElems.mapM asType?, asBool? isVarArg with
    | some retTy, some args, some isVarArg =>
      let mut ps : Array (TSyntax `nanollvm_fn_param) ← args.mapM fun t =>
        `(nanollvm_fn_param| $t:nanollvm_type)
      if isVarArg then
        ps := ps.push (← `(nanollvm_fn_param| ...))
      let psSep : Syntax.TSepArray `nanollvm_fn_param "," := ps
      `([llvm-type| $retTy:nanollvm_type($psSep,*)])
    | _, _, _ => throw ()
  | `($_ $retTy [$args,*]) => do
    match asType? retTy, args.getElems.mapM asType? with
    | some retTy, some args =>
      let ps : Array (TSyntax `nanollvm_fn_param) ← args.mapM fun t =>
        `(nanollvm_fn_param| $t:nanollvm_type)
      let psSep : Syntax.TSepArray `nanollvm_fn_param "," := ps
      `([llvm-type| $retTy:nanollvm_type($psSep,*)])
    | _, _ => throw ()
  | _ => throw ()

/-! ### Operators -/

@[app_unexpander IntBinaryOp.add]
def unexpandIntBinaryOpAdd : Unexpander
  | `($_ $a $b) =>
    match asBool? a, asBool? b with
    | some true, some true   => `([llvm-int-bin-op| add nuw nsw])
    | some true, some false  => `([llvm-int-bin-op| add nuw])
    | some false, some true  => `([llvm-int-bin-op| add nsw])
    | some false, some false => `([llvm-int-bin-op| add])
    | _, _ => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.sub]
def unexpandIntBinaryOpSub : Unexpander
  | `($_ $a $b) =>
    match asBool? a, asBool? b with
    | some true, some true   => `([llvm-int-bin-op| sub nuw nsw])
    | some true, some false  => `([llvm-int-bin-op| sub nuw])
    | some false, some true  => `([llvm-int-bin-op| sub nsw])
    | some false, some false => `([llvm-int-bin-op| sub])
    | _, _ => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.mul]
def unexpandIntBinaryOpMul : Unexpander
  | `($_ $a $b) =>
    match asBool? a, asBool? b with
    | some true, some true   => `([llvm-int-bin-op| mul nuw nsw])
    | some true, some false  => `([llvm-int-bin-op| mul nuw])
    | some false, some true  => `([llvm-int-bin-op| mul nsw])
    | some false, some false => `([llvm-int-bin-op| mul])
    | _, _ => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.shl]
def unexpandIntBinaryOpShl : Unexpander
  | `($_ $a $b) =>
    match asBool? a, asBool? b with
    | some true, some true   => `([llvm-int-bin-op| shl nuw nsw])
    | some true, some false  => `([llvm-int-bin-op| shl nuw])
    | some false, some true  => `([llvm-int-bin-op| shl nsw])
    | some false, some false => `([llvm-int-bin-op| shl])
    | _, _ => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.udiv]
def unexpandIntBinaryOpUdiv : Unexpander
  | `($_ $a) =>
    match asBool? a with
    | some true  => `([llvm-int-bin-op| udiv exact])
    | some false => `([llvm-int-bin-op| udiv])
    | none => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.sdiv]
def unexpandIntBinaryOpSdiv : Unexpander
  | `($_ $a) =>
    match asBool? a with
    | some true  => `([llvm-int-bin-op| sdiv exact])
    | some false => `([llvm-int-bin-op| sdiv])
    | none => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.lshr]
def unexpandIntBinaryOpLshr : Unexpander
  | `($_ $a) =>
    match asBool? a with
    | some true  => `([llvm-int-bin-op| lshr exact])
    | some false => `([llvm-int-bin-op| lshr])
    | none => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.ashr]
def unexpandIntBinaryOpAshr : Unexpander
  | `($_ $a) =>
    match asBool? a with
    | some true  => `([llvm-int-bin-op| ashr exact])
    | some false => `([llvm-int-bin-op| ashr])
    | none => throw ()
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
  | `($_ $a) =>
    match asBool? a with
    | some true  => `([llvm-int-bin-op| or disjoint])
    | some false => `([llvm-int-bin-op| or])
    | none => throw ()
  | _ => throw ()

@[app_unexpander IntBinaryOp.xor]
def unexpandIntBinaryOpXor : Unexpander
  | `($_) => `([llvm-int-bin-op| xor])

@[app_unexpander ConversionOp.trunc]
def unexpandConversionOpTrunc : Unexpander
  | `($_ $a $b) =>
    match asBool? a, asBool? b with
    | some true, some true   => `([llvm-conversion-op| trunc nuw nsw])
    | some true, some false  => `([llvm-conversion-op| trunc nuw])
    | some false, some true  => `([llvm-conversion-op| trunc nsw])
    | some false, some false => `([llvm-conversion-op| trunc])
    | _, _ => throw ()
  | _ => throw ()

@[app_unexpander ConversionOp.zext]
def unexpandConversionOpZext : Unexpander
  | `($_ $a) =>
    match asBool? a with
    | some true  => `([llvm-conversion-op| zext nneg])
    | some false => `([llvm-conversion-op| zext])
    | none => throw ()
  | _ => throw ()

@[app_unexpander ConversionOp.sext]
def unexpandConversionOpSext : Unexpander
  | `($_) => `([llvm-conversion-op| sext])

@[app_unexpander ConversionOp.fptrunc]
def unexpandConversionOpFptrunc : Unexpander
  | `($_ $fmf) => do
    let flags ← unexpandFMFFlags fmf
    `([llvm-conversion-op| fptrunc $flags:nanollvm_fmf_flag*])
  | `($_) => `([llvm-conversion-op| fptrunc])

@[app_unexpander ConversionOp.fpext]
def unexpandConversionOpFpext : Unexpander
  | `($_ $fmf) => do
    let flags ← unexpandFMFFlags fmf
    `([llvm-conversion-op| fpext $flags:nanollvm_fmf_flag*])
  | `($_) => `([llvm-conversion-op| fpext])

@[app_unexpander ConversionOp.fptoui]
def unexpandConversionOpFptoui : Unexpander
  | `($_) => `([llvm-conversion-op| fptoui])

@[app_unexpander ConversionOp.fptosi]
def unexpandConversionOpFptosi : Unexpander
  | `($_) => `([llvm-conversion-op| fptosi])

@[app_unexpander ConversionOp.uitofp]
def unexpandConversionOpUitofp : Unexpander
  | `($_ $nnegV $fmf) => do
    let flags ← unexpandFMFFlags fmf
    match asBool? nnegV with
    | some true  => `([llvm-conversion-op| uitofp nneg $flags:nanollvm_fmf_flag*])
    | some false => `([llvm-conversion-op| uitofp $flags:nanollvm_fmf_flag*])
    | none => throw ()
  | `($_) => `([llvm-conversion-op| uitofp])

@[app_unexpander ConversionOp.sitofp]
def unexpandConversionOpSitofp : Unexpander
  | `($_ $fmf) => do
    let flags ← unexpandFMFFlags fmf
    `([llvm-conversion-op| sitofp $flags:nanollvm_fmf_flag*])
  | `($_) => `([llvm-conversion-op| sitofp])

@[app_unexpander ConversionOp.ptrtoint]
def unexpandConversionOpPtrtoint : Unexpander
  | `($_) => `([llvm-conversion-op| ptrtoint])

@[app_unexpander ConversionOp.ptrtoaddr]
def unexpandConversionOpPtrtoaddr : Unexpander
  | `($_) => `([llvm-conversion-op| ptrtoaddr])

@[app_unexpander ConversionOp.inttoptr]
def unexpandConversionOpInttoptr : Unexpander
  | `($_) => `([llvm-conversion-op| inttoptr])

@[app_unexpander ConversionOp.bitcast]
def unexpandConversionOpBitcast : Unexpander
  | `($_) => `([llvm-conversion-op| bitcast])

@[app_unexpander ConversionOp.addrspacecast]
def unexpandConversionOpAddrspacecast : Unexpander
  | `($_) => `([llvm-conversion-op| addrspacecast])

/-! ### Expressions -/

@[app_unexpander Exp.identifier]
def unexpandExpIdentifier : Unexpander
  | `($_ $id) =>
    match asIdentifier? id with
    | some id => `([llvm-exp| $id:nanollvm_identifier])
    | none => throw ()
  | _ => throw ()

@[app_unexpander Exp.bool]
def unexpandExpBool : Unexpander
  | `($_ $a) =>
    match asBool? a with
    | some true  => `([llvm-exp| true])
    | some false => `([llvm-exp| false])
    | none => throw ()
  | _ => throw ()

@[app_unexpander Exp.int]
def unexpandExpInt : Unexpander
  | `($_ $arg) =>
    match arg with
    | `(Int.ofNat $n:num) | `($n:num) => `([llvm-exp| $n:num])
    | `(Int.negSucc $n:num) =>
      let k := Syntax.mkNumLit (toString (n.getNat + 1))
      `([llvm-exp| -$k:num])
    | `(-$n:num) => `([llvm-exp| -$n:num])
    | `(Int.ofNat $id:ident) | `($id:ident) => `([llvm-exp| <$id:ident:int>])
    | _ => throw ()
  | _ => throw ()

@[app_unexpander Exp.floatBits]
def unexpandExpFloatBits : Unexpander
  | `($_ $n:num) => `([llvm-exp| fbits($n:num)])
  | _ => throw ()

@[app_unexpander Exp.null]
def unexpandExpNull : Unexpander
  | `($_) => `([llvm-exp| null])

@[app_unexpander Exp.zeroinitializer]
def unexpandExpZeroInit : Unexpander
  | `($_) => `([llvm-exp| zeroinitializer])

@[app_unexpander Exp.undef]
def unexpandExpUndef : Unexpander
  | `($_) => `([llvm-exp| undef])

@[app_unexpander Exp.poison]
def unexpandExpPoison : Unexpander
  | `($_) => `([llvm-exp| poison])

@[app_unexpander Exp.array]
def unexpandExpArray : Unexpander
  | `($_ [$elems,*]) => do
    let es ← elems.getElems.mapM asTypedExp?
    let es : Syntax.TSepArray `nanollvm_typed_exp "," := es
    `([llvm-exp| [$es,*]])
  | _ => throw ()

@[app_unexpander Exp.struct]
def unexpandExpStruct : Unexpander
  | `($_ $packed [$elems,*]) => do
    let es ← elems.getElems.mapM asTypedExp?
    let es : Syntax.TSepArray `nanollvm_typed_exp "," := es
    match asBool? packed with
    | some false => `([llvm-exp| { $es,* }])
    | some true  => `([llvm-exp| <{ $es,* }>])
    | none => throw ()
  | _ => throw ()

@[app_unexpander Exp.vector]
def unexpandExpVector : Unexpander
  | `($_ [$elems,*]) => do
    if elems.getElems.isEmpty then throw ()
    let es ← elems.getElems.mapM asTypedExp?
    let es : Syntax.TSepArray `nanollvm_typed_exp "," := es
    `([llvm-exp| <$es,*>])
  | _ => throw ()

@[app_unexpander Exp.splat]
def unexpandExpSplat : Unexpander
  | `($_ $te) => do
    let te ← asTypedExp? te
    `([llvm-exp| splat ($te:nanollvm_typed_exp)])
  | _ => throw ()

/-! ### Instructions -/

@[app_unexpander Instruction.intBinaryOp]
def unexpandInstructionIntBinaryOp : Unexpander
  | `($_ $op $ty $v1 $v2) =>
    match asIntBinOp? op, asType? ty, asExp? v1, asExp? v2 with
    | some op, some ty, some v1, some v2 =>
      `([llvm-instruction| $op:nanollvm_int_bin_op $ty:nanollvm_type $v1:nanollvm_exp, $v2:nanollvm_exp])
    | _, _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander Instruction.floatUnaryOp]
def unexpandInstructionFloatUnaryOp : Unexpander
  | `($_ (FloatUnaryOp.fneg $fmf) $ty $v) => do
    let flags ← unexpandFMFFlags fmf
    match asType? ty, asExp? v with
    | some ty, some v => `([llvm-instruction| fneg $flags:nanollvm_fmf_flag* $ty:nanollvm_type $v:nanollvm_exp])
    | _, _ => throw ()
  | `($_ FloatUnaryOp.fneg $ty $v) =>
    match asType? ty, asExp? v with
    | some ty, some v => `([llvm-instruction| fneg $ty:nanollvm_type $v:nanollvm_exp])
    | _, _ => throw ()
  | _ => throw ()

@[app_unexpander Instruction.floatBinaryOp]
def unexpandInstructionFloatBinaryOp : Unexpander
  | `($_ ($op $fmf) $ty $v1 $v2) => do
    let flags ← unexpandFMFFlags fmf
    match asType? ty, asExp? v1, asExp? v2 with
    | some ty, some v1, some v2 =>
      let fpOp : TSyntax `nanollvm_fp_bin_op ← match op with
        | `(FloatBinaryOp.fadd) => `(nanollvm_fp_bin_op| fadd $flags:nanollvm_fmf_flag*)
        | `(FloatBinaryOp.fsub) => `(nanollvm_fp_bin_op| fsub $flags:nanollvm_fmf_flag*)
        | `(FloatBinaryOp.fmul) => `(nanollvm_fp_bin_op| fmul $flags:nanollvm_fmf_flag*)
        | `(FloatBinaryOp.fdiv) => `(nanollvm_fp_bin_op| fdiv $flags:nanollvm_fmf_flag*)
        | `(FloatBinaryOp.frem) => `(nanollvm_fp_bin_op| frem $flags:nanollvm_fmf_flag*)
        | _ => throw ()
      `([llvm-instruction| $fpOp:nanollvm_fp_bin_op $ty:nanollvm_type $v1:nanollvm_exp, $v2:nanollvm_exp])
    | _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander Instruction.icmp]
def unexpandInstructionICmp : Unexpander
  | `($_ $ss $pred $ty $v1 $v2) => do
    let predId ← unexpandICmpPred pred
    match asBool? ss, asType? ty, asExp? v1, asExp? v2 with
    | some true, some ty, some v1, some v2 =>
      `([llvm-instruction| icmp samesign $predId:ident $ty:nanollvm_type $v1:nanollvm_exp, $v2:nanollvm_exp])
    | some false, some ty, some v1, some v2 =>
      `([llvm-instruction| icmp $predId:ident $ty:nanollvm_type $v1:nanollvm_exp, $v2:nanollvm_exp])
    | _, _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander Instruction.fcmp]
def unexpandInstructionFCmp : Unexpander
  | `($_ $fmf $pred $ty $v1 $v2) => do
    let flags ← unexpandFMFFlags fmf
    let predId ← unexpandFCmpPred pred
    match asType? ty, asExp? v1, asExp? v2 with
    | some ty, some v1, some v2 =>
      `([llvm-instruction| fcmp $flags:nanollvm_fmf_flag* $predId:ident $ty:nanollvm_type $v1:nanollvm_exp, $v2:nanollvm_exp])
    | _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander Instruction.conversionOp]
def unexpandInstructionConversionOp : Unexpander
  | `($_ $op $fromTy $v $toTy) =>
    match asConversionOp? op, asType? fromTy, asExp? v, asType? toTy with
    | some op, some fromTy, some v, some toTy =>
      `([llvm-instruction| $op:nanollvm_conversion_op $fromTy:nanollvm_type $v:nanollvm_exp to $toTy:nanollvm_type])
    | _, _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander Instruction.select]
def unexpandInstructionSelect : Unexpander
  | `($_ $fmf $cTy $c $vTy $tv $fv) => do
    let flags ← unexpandFMFFlags fmf
    match asType? cTy, asExp? c, asType? vTy, asExp? tv, asExp? fv with
    | some cTy, some c, some vTy, some tv, some fv =>
      `([llvm-instruction| select $flags:nanollvm_fmf_flag* $cTy:nanollvm_type $c:nanollvm_exp, $vTy:nanollvm_type $tv:nanollvm_exp, $vTy:nanollvm_type $fv:nanollvm_exp])
    | _, _, _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander Instruction.phi]
def unexpandInstructionPhi : Unexpander
  | `($_ $ty $fmf [$incs,*]) => do
    if incs.getElems.isEmpty then throw ()
    let flags ← unexpandFMFFlags fmf
    match asType? ty with
    | none => throw ()
    | some ty =>
      let incArr ← incs.getElems.mapM fun inc =>
        match inc with
        | `(($e, $lbl)) =>
          match asExp? e, asRawId? lbl with
          | some e, some lbl => `(nanollvm_phi_incoming| [$e:nanollvm_exp, %$lbl:nanollvm_rawid])
          | _, _ => throw ()
        | _ => throw ()
      let incSep : Syntax.TSepArray `nanollvm_phi_incoming "," := incArr
      `([llvm-instruction| phi $flags:nanollvm_fmf_flag* $ty:nanollvm_type $incSep,*])
  | _ => throw ()

@[app_unexpander Instruction.alloca]
def unexpandInstructionAlloca : Unexpander
  | `($_ $ty $numEl $al $as) => do
    match asType? ty with
    | none => throw ()
    | some ty =>
      let mut opts : Array (TSyntax `nanollvm_alloca_opt) := #[]
      match numEl with
      | `(none) | `(Option.none) => pure ()
      | `(some $te) | `(Option.some $te) =>
        let te ← asTypedExp? te
        opts := opts.push (← `(nanollvm_alloca_opt| $te:nanollvm_typed_exp))
      | _ => throw ()
      match al with
      | `(none) | `(Option.none) => pure ()
      | `(some $n:num) | `(Option.some $n:num) =>
        opts := opts.push (← `(nanollvm_alloca_opt| align $n:num))
      | _ => throw ()
      match as with
      | `(0) => pure ()
      | `($n:num) => opts := opts.push (← `(nanollvm_alloca_opt| addrspace($n:num)))
      | _ => throw ()
      `([llvm-instruction| alloca $ty:nanollvm_type $[, $opts:nanollvm_alloca_opt]*])
  | `($_ $ty $numEl $al) => do
    match asType? ty with
    | none => throw ()
    | some ty =>
      let mut opts : Array (TSyntax `nanollvm_alloca_opt) := #[]
      match numEl with
      | `(none) | `(Option.none) => pure ()
      | `(some $te) | `(Option.some $te) =>
        let te ← asTypedExp? te
        opts := opts.push (← `(nanollvm_alloca_opt| $te:nanollvm_typed_exp))
      | _ => throw ()
      match al with
      | `(none) | `(Option.none) => pure ()
      | `(some $n:num) | `(Option.some $n:num) =>
        opts := opts.push (← `(nanollvm_alloca_opt| align $n:num))
      | _ => throw ()
      `([llvm-instruction| alloca $ty:nanollvm_type $[, $opts:nanollvm_alloca_opt]*])
  | _ => throw ()

@[app_unexpander Instruction.load]
def unexpandInstructionLoad : Unexpander
  | `($_ $ty $pTy $ptr $al $isVol $nu) => do
    match asType? ty, asType? pTy, asExp? ptr, asBool? isVol, asBool? nu with
    | some ty, some pTy, some ptr, some isVol, some nu =>
      let mut opts : Array (TSyntax `nanollvm_load_opt) := #[]
      match al with
      | `(none) | `(Option.none) => pure ()
      | `(some $n:num) | `(Option.some $n:num) =>
        opts := opts.push (← `(nanollvm_load_opt| align $n:num))
      | _ => throw ()
      if nu then opts := opts.push (← `(nanollvm_load_opt| !noundef))
      if isVol then
        `([llvm-instruction| load volatile $ty:nanollvm_type, $pTy:nanollvm_type $ptr:nanollvm_exp $[, $opts:nanollvm_load_opt]*])
      else
        `([llvm-instruction| load $ty:nanollvm_type, $pTy:nanollvm_type $ptr:nanollvm_exp $[, $opts:nanollvm_load_opt]*])
    | _, _, _, _, _ => throw ()
  | `($_ $ty $pTy $ptr $al) => do
    match asType? ty, asType? pTy, asExp? ptr with
    | some ty, some pTy, some ptr =>
      let mut opts : Array (TSyntax `nanollvm_load_opt) := #[]
      match al with
      | `(none) | `(Option.none) => pure ()
      | `(some $n:num) | `(Option.some $n:num) =>
        opts := opts.push (← `(nanollvm_load_opt| align $n:num))
      | _ => throw ()
      `([llvm-instruction| load $ty:nanollvm_type, $pTy:nanollvm_type $ptr:nanollvm_exp $[, $opts:nanollvm_load_opt]*])
    | _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander Instruction.store]
def unexpandInstructionStore : Unexpander
  | `($_ $vTy $v $pTy $ptr $al $isVol) => do
    match asType? vTy, asExp? v, asType? pTy, asExp? ptr, asBool? isVol with
    | some vTy, some v, some pTy, some ptr, some isVol =>
      match al with
      | `(none) | `(Option.none) =>
        if isVol then `([llvm-instruction| store volatile $vTy:nanollvm_type $v:nanollvm_exp, $pTy:nanollvm_type $ptr:nanollvm_exp])
        else `([llvm-instruction| store $vTy:nanollvm_type $v:nanollvm_exp, $pTy:nanollvm_type $ptr:nanollvm_exp])
      | `(some $n:num) | `(Option.some $n:num) =>
        if isVol then `([llvm-instruction| store volatile $vTy:nanollvm_type $v:nanollvm_exp, $pTy:nanollvm_type $ptr:nanollvm_exp, align $n:num])
        else `([llvm-instruction| store $vTy:nanollvm_type $v:nanollvm_exp, $pTy:nanollvm_type $ptr:nanollvm_exp, align $n:num])
      | _ => throw ()
    | _, _, _, _, _ => throw ()
  | `($_ $vTy $v $pTy $ptr $al) => do
    match asType? vTy, asExp? v, asType? pTy, asExp? ptr with
    | some vTy, some v, some pTy, some ptr =>
      match al with
      | `(none) | `(Option.none) =>
        `([llvm-instruction| store $vTy:nanollvm_type $v:nanollvm_exp, $pTy:nanollvm_type $ptr:nanollvm_exp])
      | `(some $n:num) | `(Option.some $n:num) =>
        `([llvm-instruction| store $vTy:nanollvm_type $v:nanollvm_exp, $pTy:nanollvm_type $ptr:nanollvm_exp, align $n:num])
      | _ => throw ()
    | _, _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander Instruction.getelementptr]
def unexpandInstructionGEP : Unexpander
  | `($_ $flags $baseTy $pTy $ptr [$idxs,*]) => do
    let gFlags ← unexpandGEPFlags flags
    match asType? baseTy, asType? pTy, asExp? ptr with
    | some baseTy, some pTy, some ptr =>
      let idxArr ← idxs.getElems.mapM asTypedExp?
      `([llvm-instruction| getelementptr $gFlags:nanollvm_gep_flag* $baseTy:nanollvm_type, $pTy:nanollvm_type $ptr:nanollvm_exp $[, $idxArr:nanollvm_typed_exp]*])
    | _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander Instruction.extractvalue]
def unexpandInstructionExtractValue : Unexpander
  | `($_ $aggTy $agg [$idxs,*]) => do
    if idxs.getElems.isEmpty then throw ()
    match asType? aggTy, asExp? agg with
    | some aggTy, some agg =>
      let ns ← idxs.getElems.mapM fun x =>
        match x with
        | `($n:num) => pure n
        | _ => throw ()
      let ns : Syntax.TSepArray `num "," := ns
      `([llvm-instruction| extractvalue $aggTy:nanollvm_type $agg:nanollvm_exp, $ns,*])
    | _, _ => throw ()
  | _ => throw ()

@[app_unexpander Instruction.insertvalue]
def unexpandInstructionInsertValue : Unexpander
  | `($_ $aggTy $agg $valTy $val [$idxs,*]) => do
    if idxs.getElems.isEmpty then throw ()
    match asType? aggTy, asExp? agg, asType? valTy, asExp? val with
    | some aggTy, some agg, some valTy, some val =>
      let ns ← idxs.getElems.mapM fun x =>
        match x with
        | `($n:num) => pure n
        | _ => throw ()
      let ns : Syntax.TSepArray `num "," := ns
      `([llvm-instruction| insertvalue $aggTy:nanollvm_type $agg:nanollvm_exp, $valTy:nanollvm_type $val:nanollvm_exp, $ns,*])
    | _, _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander Instruction.extractelement]
def unexpandInstructionExtractElement : Unexpander
  | `($_ $vecTy $vec $idxTy $idx) =>
    match asType? vecTy, asExp? vec, asType? idxTy, asExp? idx with
    | some vecTy, some vec, some idxTy, some idx =>
      `([llvm-instruction| extractelement $vecTy:nanollvm_type $vec:nanollvm_exp, $idxTy:nanollvm_type $idx:nanollvm_exp])
    | _, _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander Instruction.insertelement]
def unexpandInstructionInsertElement : Unexpander
  | `($_ $vecTy $vec $valTy $val $idxTy $idx) =>
    match asType? vecTy, asExp? vec, asType? valTy, asExp? val, asType? idxTy, asExp? idx with
    | some vecTy, some vec, some valTy, some val, some idxTy, some idx =>
      `([llvm-instruction| insertelement $vecTy:nanollvm_type $vec:nanollvm_exp, $valTy:nanollvm_type $val:nanollvm_exp, $idxTy:nanollvm_type $idx:nanollvm_exp])
    | _, _, _, _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander Instruction.shufflevector]
def unexpandInstructionShuffleVector : Unexpander
  | `($_ $vecTy $v1 $v2 [$mask,*]) => do
    if mask.getElems.isEmpty then throw ()
    match asType? vecTy, asExp? v1, asExp? v2 with
    | some vecTy, some v1, some v2 =>
      let i32Id := mkIdent `i32
      let elems ← mask.getElems.mapM fun el =>
        match el with
        | `(some $n:num) | `(Option.some $n:num) => `(nanollvm_shuffle_elem| $i32Id:ident $n:num)
        | `(none) | `(Option.none) => `(nanollvm_shuffle_elem| $i32Id:ident poison)
        | _ => throw ()
      let elemsSep : Syntax.TSepArray `nanollvm_shuffle_elem "," := elems
      let lenLit := Syntax.mkNumLit (toString mask.getElems.size)
      `([llvm-instruction| shufflevector $vecTy:nanollvm_type $v1:nanollvm_exp, $vecTy:nanollvm_type $v2:nanollvm_exp, < $lenLit:num x i32 > < $elemsSep,* >])
    | _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander Instruction.call]
def unexpandInstructionCall : Unexpander
  | `($_ $retTy $fmf $callee [$args,*] $retAttrs) => do
    let flags ← unexpandFMFFlags fmf
    let rAttrs ← unexpandValueAttrList retAttrs
    match asType? retTy, asExp? callee with
    | some retTy, some callee =>
      let callArgs ← args.getElems.mapM fun a =>
        match a with
        | `(($t, $e, $attrs)) => do
          let as ← unexpandValueAttrList attrs
          match asType? t, asExp? e with
          | some t, some e => `(nanollvm_call_arg| $t:nanollvm_type $as:nanollvm_value_attr* $e:nanollvm_exp)
          | _, _ => throw ()
        | _ => throw ()
      let callArgsSep : Syntax.TSepArray `nanollvm_call_arg "," := callArgs
      `([llvm-instruction| call $flags:nanollvm_fmf_flag* $rAttrs:nanollvm_value_attr* $retTy:nanollvm_type $callee:nanollvm_exp($callArgsSep,*)])
    | _, _ => throw ()
  | `($_ $retTy $fmf $callee [$args,*]) => do
    let flags ← unexpandFMFFlags fmf
    match asType? retTy, asExp? callee with
    | some retTy, some callee =>
      let callArgs ← args.getElems.mapM fun a =>
        match a with
        | `(($t, $e, $attrs)) => do
          let as ← unexpandValueAttrList attrs
          match asType? t, asExp? e with
          | some t, some e => `(nanollvm_call_arg| $t:nanollvm_type $as:nanollvm_value_attr* $e:nanollvm_exp)
          | _, _ => throw ()
        | _ => throw ()
      let callArgsSep : Syntax.TSepArray `nanollvm_call_arg "," := callArgs
      `([llvm-instruction| call $flags:nanollvm_fmf_flag* $retTy:nanollvm_type $callee:nanollvm_exp($callArgsSep,*)])
    | _, _ => throw ()
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

/-! ### Terminators -/

@[app_unexpander Terminator.retVoid]
def unexpandTerminatorRetVoid : Unexpander
  | `($_) => `([llvm-terminator| ret void])

@[app_unexpander Terminator.ret]
def unexpandTerminatorRet : Unexpander
  | `($_ $tv) =>
    match tv with
    | `(($ty, $v)) | `(⟨$ty, $v⟩) =>
      match asType? ty, asExp? v with
      | some ty, some v => `([llvm-terminator| ret $ty:nanollvm_type $v:nanollvm_exp])
      | _, _ => throw ()
    | _ => throw ()
  | _ => throw ()

@[app_unexpander Terminator.br]
def unexpandTerminatorBr : Unexpander
  | `($_ $dest) =>
    match asRawId? dest with
    | some dest => `([llvm-terminator| br label %$dest:nanollvm_rawid])
    | none => throw ()
  | _ => throw ()

@[app_unexpander Terminator.condBr]
def unexpandTerminatorCondBr : Unexpander
  | `($_ $cond $tDest $fDest) =>
    match asExp? cond, asRawId? tDest, asRawId? fDest with
    | some cond, some tDest, some fDest =>
      `([llvm-terminator| br i1 $cond:nanollvm_exp, label %$tDest:nanollvm_rawid, label %$fDest:nanollvm_rawid])
    | _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander Terminator.switch]
def unexpandTerminatorSwitch : Unexpander
  | `($_ $ty $cond $defDest [$cases,*]) => do
    match asType? ty, asExp? cond, asRawId? defDest with
    | some ty, some cond, some defDest =>
      let caseArr ← cases.getElems.mapM fun c =>
        match c with
        | `(($v, $lbl)) => do
          let vS ← asSignedInt? v
          match asRawId? lbl with
          | some lbl => `(nanollvm_switch_case| $ty:nanollvm_type $vS:nanollvm_signed_int, label %$lbl:nanollvm_rawid)
          | none => throw ()
        | _ => throw ()
      `([llvm-terminator| switch $ty:nanollvm_type $cond:nanollvm_exp, label %$defDest:nanollvm_rawid [ $caseArr:nanollvm_switch_case* ]])
    | _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander Terminator.unreachable]
def unexpandTerminatorUnreachable : Unexpander
  | `($_) => `([llvm-terminator| unreachable])

/-! ### Declarations, Blocks, Definitions, Globals, Modules -/

@[app_unexpander Declaration.mk]
def unexpandDeclarationMk : Unexpander
  | `($_ $name $ty $argAttrs $retAttrs) => do
    let rAttrs ← unexpandValueAttrList retAttrs
    let aAttrsList : Array (Array (TSyntax `nanollvm_value_attr)) ←
      match argAttrs with
      | `([]) => pure #[]
      | `([$xs,*]) => xs.getElems.mapM unexpandValueAttrList
      | _ => throw ()
    match asRawId? name, asType? ty with
    | some name, some ty =>
      match ty with
      | `(nanollvm_type| $retTy($params,*)) =>
        let retTy : TSyntax `nanollvm_type := ⟨retTy⟩
        let mut dArgs : Array (TSyntax `nanollvm_decl_arg) := #[]
        for i in [:params.getElems.size] do
          match params.getElems[i]!.raw with
          | `(nanollvm_fn_param| ...) =>
            dArgs := dArgs.push (← `(nanollvm_decl_arg| ...))
          | `(nanollvm_fn_param| $t:nanollvm_type) =>
            let as := aAttrsList.getD i #[]
            dArgs := dArgs.push (← `(nanollvm_decl_arg| $t:nanollvm_type $as:nanollvm_value_attr*))
          | _ => throw ()
        let dArgsSep : Syntax.TSepArray `nanollvm_decl_arg "," := dArgs
        `([llvm-declaration| declare $rAttrs:nanollvm_value_attr* $retTy:nanollvm_type @$name:nanollvm_rawid($dArgsSep,*)])
      | _ => throw ()
    | _, _ => throw ()
  | `($_ $name $ty) => do
    match asRawId? name, asType? ty with
    | some name, some ty =>
      match ty with
      | `(nanollvm_type| $retTy($params,*)) =>
        let retTy : TSyntax `nanollvm_type := ⟨retTy⟩
        let dArgs ← params.getElems.mapM fun p =>
          match p.raw with
          | `(nanollvm_fn_param| ...) => `(nanollvm_decl_arg| ...)
          | `(nanollvm_fn_param| $t:nanollvm_type) => `(nanollvm_decl_arg| $t:nanollvm_type)
          | _ => throw ()
        let dArgsSep : Syntax.TSepArray `nanollvm_decl_arg "," := dArgs
        `([llvm-declaration| declare $retTy:nanollvm_type @$name:nanollvm_rawid($dArgsSep,*)])
      | _ => throw ()
    | _, _ => throw ()
  | _ => throw ()

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

@[app_unexpander List.cons]
def unexpandCodeListCons : Unexpander
  | `($(_) $x $tail) => do
    let x : TSyntax `nanollvm_codeline ← asCodeline x
    let xs : Array (TSyntax `nanollvm_codeline) ←
      match tail with
      | `([llvm-code| $xs:nanollvm_codeline*]) => xs.mapM asCodeline
      | `([]) => pure #[]
      | `([$xs,*]) => xs.getElems.mapM asCodeline
      | _ => throw ()
    let code : Syntax.TSepArray `nanollvm_codeline "\n" := #[x] ++ xs
    `([llvm-code| $code:nanollvm_codeline*])
  | _ => throw ()

@[app_unexpander Block.mk]
def unexpandBlockMk : Unexpander
  | `($_ $id $code $term) => do
    let id ← match asRawId? id with
      | some id => pure id
      | none => throw ()
    let code : TSyntax `nanollvm_code ← match asCode? code with
      | some code => pure code
      | none =>
        match code with
        | `([]) => `(nanollvm_code| )
        | _ => throw ()
    let term : TSyntax `nanollvm_terminator ← match term with
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
  | `($_ $proto [$argVals,*] [$blks,*]) => do
    match asDeclaration? proto with
    | some proto =>
      match proto with
      | `(nanollvm_declaration| declare $rAttrs:nanollvm_value_attr* $retTy:nanollvm_type @$name:nanollvm_rawid($dArgs,*)) =>
        let argVals : Option (Array (TSyntax `nanollvm_rawid)) := argVals.getElems.mapM asRawId?
        let blksOpt : Option (Array (TSyntax `nanollvm_block)) := blks.getElems.mapM asBlock?
        match argVals, blksOpt with
        | some argVals, some blksArr =>
          if blksArr.isEmpty then throw ()
          let mut args : Array (TSyntax `nanollvm_arg) := #[]
          let mut idx := 0
          for da in dArgs.getElems do
            match da.raw with
            | `(nanollvm_decl_arg| ...) =>
              args := args.push (← `(nanollvm_arg| ...))
            | `(nanollvm_decl_arg| $t:nanollvm_type $as:nanollvm_value_attr*) =>
              match argVals[idx]? with
              | some v =>
                idx := idx + 1
                args := args.push (← `(nanollvm_arg| $t:nanollvm_type $as:nanollvm_value_attr* %$v:nanollvm_rawid))
              | none => throw ()
            | _ => throw ()
          if idx != argVals.size then throw ()
          let argsSep : Syntax.TSepArray `nanollvm_arg "," := args
          `([llvm-definition| define $rAttrs:nanollvm_value_attr* $retTy:nanollvm_type @$name:nanollvm_rawid($argsSep,*) {
            $[$blksArr]*
          }])
        | _, _ => throw ()
      | _ => throw ()
    | _ => throw ()
  | _ => throw ()

@[app_unexpander GlobalVariable.mk]
def unexpandGlobalVariableMk : Unexpander
  | `($_ $name $ty $isConst $init $al $as) => do
    match asRawId? name, asType? ty, asBool? isConst with
    | some name, some ty, some isConst =>
      let initOpt : Option (TSyntax `nanollvm_exp) ← match init with
        | `(none) | `(Option.none) => pure none
        | `(some $e) | `(Option.some $e) =>
          match asExp? e with
          | some e => pure (some e)
          | none => throw ()
        | _ => throw ()
      let alignOpt : Option (TSyntax `num) ← match al with
        | `(none) | `(Option.none) => pure none
        | `(some $n:num) | `(Option.some $n:num) => pure (some n)
        | _ => throw ()
      let asOpt : Option (TSyntax `num) ← match as with
        | `(0) => pure none
        | `($n:num) => pure (some n)
        | _ => throw ()
      if isConst then
        `([llvm-global| @$name:nanollvm_rawid = $[addrspace($asOpt:num)]? constant $ty:nanollvm_type $[$initOpt:nanollvm_exp]? $[, align $alignOpt:num]?])
      else
        `([llvm-global| @$name:nanollvm_rawid = $[addrspace($asOpt:num)]? global $ty:nanollvm_type $[$initOpt:nanollvm_exp]? $[, align $alignOpt:num]?])
    | _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander TopLevelEntity.global]
def unexpandTopLevelEntityGlobal : Unexpander
  | `($_ $gv) =>
    match asGlobal? gv with
    | some gv => `([llvm-entity| $gv:nanollvm_global])
    | none => throw ()
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
  | `($_ [$els,*]) => do
    let els : Array (TSyntax `nanollvm_entity) ← els.getElems.mapM fun h =>
      match asEntity? h with
      | some e => pure e
      | none => throw ()
    `([llvm|
$[$els]*])
  | _ => throw ()

end LeanNanoLlvm.AST
