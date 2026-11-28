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

private def stripParens (stx : Syntax) : Syntax :=
  match stx with
  | `(($x)) => x.raw
  | _ => stx

private def asBool? (stx : Syntax) : Option Bool :=
  match stripParens stx with
  | `($id:ident) =>
    match id.getId.eraseMacroScopes with
    | `true | ``Bool.true => some true
    | `false | ``Bool.false => some false
    | _ => none
  | _ => none

private def asStr? (stx : Syntax) : Option String :=
  match stripParens stx with
  | `($s:str) => some s.getString
  | _ => none

private def asTypedExp? (stx : Syntax) : UnexpandM (TSyntax `nanollvm_typed_exp) := do
  match stripParens stx with
  | `(($ty, $e)) | `(⟨$ty, $e⟩) =>
    match asType? ty, asExp? e with
    | some ty, some e => `(nanollvm_typed_exp| $ty:nanollvm_type $e:nanollvm_exp)
    | _, _ => throw ()
  | _ => throw ()

private def asSignedIntVal? (stx : Syntax) : Option Int :=
  match stripParens stx with
  | `(Int.ofNat $n:num) | `($n:num) => some (n.getNat : Int)
  | `(-$n:num) => some (-(n.getNat : Int))
  | `(Int.negSucc $n:num) => some (-(n.getNat + 1 : Int))
  | _ => none

private def asSignedInt? (stx : Syntax) : UnexpandM (TSyntax `nanollvm_signed_int) := do
  match asSignedIntVal? stx with
  | some v =>
    if v ≥ 0 then
      let k := Syntax.mkNumLit (toString v.toNat)
      `(nanollvm_signed_int| $k:num)
    else
      let k := Syntax.mkNumLit (toString (-v).toNat)
      `(nanollvm_signed_int| -$k:num)
  | none => throw ()

/-- Extract `(fieldName, fieldValue)` pairs from a Lean `Term.structInst` (`{ a := v, ... }` or `{ }`). -/
private def extractStructFields? (stx : Syntax) : Option (Array (Name × Syntax)) := do
  let s := stripParens stx
  if s.getKind != ``Lean.Parser.Term.structInst then
    none
  let fieldsNode := s[2]
  if fieldsNode.getKind != ``Lean.Parser.Term.structInstFields then
    none
  let mut out : Array (Name × Syntax) := #[]
  for f in fieldsNode[0].getSepArgs do
    if f.getKind != ``Lean.Parser.Term.structInstField then
      none
    let lval := f[0]
    if lval.getKind != ``Lean.Parser.Term.structInstLVal then
      none
    let nm := lval[0].getId.eraseMacroScopes
    let defNode := f[1][2]
    if defNode.getKind != ``Lean.Parser.Term.structInstFieldDef then
      none
    let val := defNode[2]
    out := out.push (nm, val)
  some out

private def fmfArrayFromBools (bNnan bNinf bNsz bArcp bContract bAfn bReassoc : Bool) :
    UnexpandM (Array (TSyntax `nanollvm_fmf_flag)) := do
  if bNnan && bNinf && bNsz && bArcp && bContract && bAfn && bReassoc then
    return #[← `(nanollvm_fmf_flag| fast)]
  let mut out : Array (TSyntax `nanollvm_fmf_flag) := #[]
  if bNnan     then out := out.push (← `(nanollvm_fmf_flag| nnan))
  if bNinf     then out := out.push (← `(nanollvm_fmf_flag| ninf))
  if bNsz      then out := out.push (← `(nanollvm_fmf_flag| nsz))
  if bArcp     then out := out.push (← `(nanollvm_fmf_flag| arcp))
  if bContract then out := out.push (← `(nanollvm_fmf_flag| contract))
  if bAfn      then out := out.push (← `(nanollvm_fmf_flag| afn))
  if bReassoc  then out := out.push (← `(nanollvm_fmf_flag| reassoc))
  pure out

private def unexpandFMFFlags (stx : Syntax) : UnexpandM (Array (TSyntax `nanollvm_fmf_flag)) := do
  let s := stripParens stx
  match s with
  | `($id:ident) =>
    match id.getId.eraseMacroScopes with
    | ``FastMathFlags.none | `FastMathFlags.none => return #[]
    | ``FastMathFlags.fast | `FastMathFlags.fast => return #[← `(nanollvm_fmf_flag| fast)]
    | _ => throw ()
  | `($f:ident $b1 $b2 $b3 $b4 $b5 $b6 $b7) =>
    match f.getId.eraseMacroScopes, asBool? b1, asBool? b2, asBool? b3, asBool? b4, asBool? b5, asBool? b6, asBool? b7 with
    | ``FastMathFlags.mk, some b1, some b2, some b3, some b4, some b5, some b6, some b7
    | `FastMathFlags.mk, some b1, some b2, some b3, some b4, some b5, some b6, some b7 =>
      fmfArrayFromBools b1 b2 b3 b4 b5 b6 b7
    | _, _, _, _, _, _, _, _ => throw ()
  | _ =>
    match extractStructFields? s with
    | some fields =>
      let mut bNnan := false
      let mut bNinf := false
      let mut bNsz := false
      let mut bArcp := false
      let mut bContract := false
      let mut bAfn := false
      let mut bReassoc := false
      for (nm, val) in fields do
        match asBool? val with
        | none => throw ()
        | some b =>
          match nm with
          | `nnan => bNnan := b
          | `ninf => bNinf := b
          | `nsz => bNsz := b
          | `arcp => bArcp := b
          | `contract => bContract := b
          | `afn => bAfn := b
          | `reassoc => bReassoc := b
          | _ => throw ()
      fmfArrayFromBools bNnan bNinf bNsz bArcp bContract bAfn bReassoc
    | none => throw ()

private def gepArrayFromBools (hasInbounds hasNusw hasNuw : Bool) :
    UnexpandM (Array (TSyntax `nanollvm_gep_flag)) := do
  let mut out : Array (TSyntax `nanollvm_gep_flag) := #[]
  if hasInbounds then out := out.push (← `(nanollvm_gep_flag| inbounds))
  else if hasNusw then out := out.push (← `(nanollvm_gep_flag| nusw))
  if hasNuw then out := out.push (← `(nanollvm_gep_flag| nuw))
  pure out

private def unexpandGEPFlags (stx : Syntax) : UnexpandM (Array (TSyntax `nanollvm_gep_flag)) := do
  let s := stripParens stx
  match s with
  | `($id:ident) =>
    match id.getId.eraseMacroScopes with
    | ``GEPFlags.none | `GEPFlags.none => return #[]
    | ``GEPFlags.mkInbounds | `GEPFlags.mkInbounds => return #[← `(nanollvm_gep_flag| inbounds)]
    | _ => throw ()
  | `($f:ident $b1 $b2 $b3) =>
    match f.getId.eraseMacroScopes, asBool? b1, asBool? b2, asBool? b3 with
    | ``GEPFlags.mk, some b1, some b2, some b3
    | `GEPFlags.mk, some b1, some b2, some b3 => gepArrayFromBools b1 b2 b3
    | _, _, _, _ => throw ()
  | _ =>
    match extractStructFields? s with
    | some fields =>
      let mut hasInbounds := false
      let mut hasNusw := false
      let mut hasNuw := false
      for (nm, val) in fields do
        match asBool? val with
        | none => throw ()
        | some b =>
          match nm with
          | `inbounds => hasInbounds := b
          | `nusw => hasNusw := b
          | `nuw => hasNuw := b
          | _ => throw ()
      gepArrayFromBools hasInbounds hasNusw hasNuw
    | none => throw ()

private def unexpandCallSiteInfo (stx : Syntax) : UnexpandM (Bool × String) := do
  let s := stripParens stx
  match s with
  | `($id:ident) =>
    match id.getId.eraseMacroScopes with
    | ``CallSiteInfo.default | `CallSiteInfo.default => return (false, "")
    | _ => throw ()
  | `($f:ident $tl $ccVal $va) =>
    match f.getId.eraseMacroScopes, asBool? tl, asStr? ccVal, (some va : Option _) with
    | ``CallSiteInfo.mk, some tl, some ccStr, _
    | `CallSiteInfo.mk, some tl, some ccStr, _ => return (tl, ccStr)  -- `fnTy?` is not shown
    | _, _, _, _ => throw ()
  | `($f:ident $tl $ccVal) =>
    match f.getId.eraseMacroScopes, asBool? tl, asStr? ccVal with
    | ``CallSiteInfo.mk, some tl, some ccStr
    | `CallSiteInfo.mk, some tl, some ccStr => return (tl, ccStr)
    | _, _, _ => throw ()
  | _ =>
    match extractStructFields? s with
    | some fields =>
      let mut isTail := false
      let mut ccStr := ""
      for (nm, val) in fields do
        match nm with
        | `isTail =>
          match asBool? val with
          | some b => isTail := b
          | none => throw ()
        | `callingConv =>
          match asStr? val with
          | some str => ccStr := str
          | none => throw ()
        | `fnTy? => pure ()  -- the call's function type is not shown (see `CallSiteInfo.fnTy?`)
        | _ => throw ()
      pure (isTail, ccStr)
    | none => throw ()

private def unexpandDenormalModeKind (stx : Syntax) : UnexpandM (TSyntax `ident) := do
  match stripParens stx with
  | `($id:ident) =>
    match id.getId.eraseMacroScopes with
    | ``DenormalModeKind.ieee | `DenormalModeKind.ieee | `ieee => pure (mkIdent `ieee)
    | ``DenormalModeKind.preserveSign | `DenormalModeKind.preserveSign | `preserveSign => pure (mkIdent `preservesign)
    | ``DenormalModeKind.positiveZero | `DenormalModeKind.positiveZero | `positiveZero => pure (mkIdent `positivezero)
    | _ => throw ()
  | _ => throw ()

private def unexpandDenormalMode (stx : Syntax) : UnexpandM (TSyntax `nanollvm_fn_attr) := do
  let s := stripParens stx
  match s with
  | `($f:ident $inK $outK) =>
    match f.getId.eraseMacroScopes with
    | ``DenormalMode.mk | `DenormalMode.mk =>
      let inId ← unexpandDenormalModeKind inK
      let outId ← unexpandDenormalModeKind outK
      `(nanollvm_fn_attr| denormal_fpenv($outId:ident | $inId:ident))
    | _ => throw ()
  | _ =>
    match extractStructFields? s with
    | some fields =>
      let mut inId := mkIdent `ieee
      let mut outId := mkIdent `ieee
      for (nm, val) in fields do
        match nm with
        | `input => inId ← unexpandDenormalModeKind val
        | `output => outId ← unexpandDenormalModeKind val
        | _ => throw ()
      `(nanollvm_fn_attr| denormal_fpenv($outId:ident | $inId:ident))
    | none => throw ()

private def unexpandValueAttr (stx : Syntax) : UnexpandM (TSyntax `nanollvm_value_attr) := do
  match stripParens stx with
  | `($id:ident) =>
    match id.getId.eraseMacroScopes with
    | ``ValueAttr.noundef | `ValueAttr.noundef | `noundef => `(nanollvm_value_attr| noundef)
    | ``ValueAttr.nonnull | `ValueAttr.nonnull | `nonnull => `(nanollvm_value_attr| nonnull)
    | ``ValueAttr.noalias | `ValueAttr.noalias | `noalias => `(nanollvm_value_attr| noalias)
    | ``ValueAttr.readonly | `ValueAttr.readonly | `readonly => `(nanollvm_value_attr| readonly)
    | _ => throw ()
  | `($f:ident $n:num) =>
    match f.getId.eraseMacroScopes with
    | ``ValueAttr.align | `ValueAttr.align | `align => `(nanollvm_value_attr| align $n:num)
    | ``ValueAttr.dereferenceable | `ValueAttr.dereferenceable | `dereferenceable =>
      `(nanollvm_value_attr| dereferenceable($n:num))
    | ``ValueAttr.dereferenceableOrNull | `ValueAttr.dereferenceableOrNull | `dereferenceableOrNull =>
      `(nanollvm_value_attr| dereferenceable_or_null($n:num))
    | ``ValueAttr.nofpclass | `ValueAttr.nofpclass | `nofpclass =>
      `(nanollvm_value_attr| nofpclass($n:num))
    | _ => throw ()
  | `($f:ident $lo $hi) =>
    match f.getId.eraseMacroScopes with
    | ``ValueAttr.range | `ValueAttr.range | `range =>
      let loS ← asSignedInt? lo
      let hiS ← asSignedInt? hi
      `(nanollvm_value_attr| range($loS:nanollvm_signed_int, $hiS:nanollvm_signed_int))
    | _ => throw ()
  | `($f:ident [$pairs,*]) =>
    match f.getId.eraseMacroScopes with
    | ``ValueAttr.rangeList | `ValueAttr.rangeList | `rangeList =>
      let pairArr ← pairs.getElems.mapM fun p =>
        match stripParens p with
        | `(($lo, $hi)) | `(⟨$lo, $hi⟩) => do
          let loS ← asSignedInt? lo
          let hiS ← asSignedInt? hi
          `(nanollvm_range_pair| $loS:nanollvm_signed_int, $hiS:nanollvm_signed_int)
        | _ => throw ()
      let pairSep : Syntax.TSepArray `nanollvm_range_pair "," := pairArr
      `(nanollvm_value_attr| range_list($pairSep,*))
    | _ => throw ()
  | `($f:ident $ty) =>
    match f.getId.eraseMacroScopes, asType? (stripParens ty) with
    | ``ValueAttr.byval, some ty | `ValueAttr.byval, some ty | `byval, some ty =>
      `(nanollvm_value_attr| byval($ty:nanollvm_type))
    | ``ValueAttr.sret, some ty | `ValueAttr.sret, some ty | `sret, some ty =>
      `(nanollvm_value_attr| sret($ty:nanollvm_type))
    | _, _ => throw ()
  | _ => throw ()

private def unexpandValueAttrList (stx : Syntax) : UnexpandM (Array (TSyntax `nanollvm_value_attr)) := do
  match stripParens stx with
  | `([]) => pure #[]
  | `([$attrs,*]) => attrs.getElems.mapM unexpandValueAttr
  | _ => throw ()

private def unexpandICmpPred (stx : Syntax) : UnexpandM (TSyntax `ident) := do
  match stripParens stx with
  | `($id:ident) =>
    let nm? := match id.getId.eraseMacroScopes with
      | ``ICmpPred.eq  | `ICmpPred.eq  | `eq  => some `eq
      | ``ICmpPred.ne  | `ICmpPred.ne  | `ne  => some `ne
      | ``ICmpPred.ugt | `ICmpPred.ugt | `ugt => some `ugt
      | ``ICmpPred.uge | `ICmpPred.uge | `uge => some `uge
      | ``ICmpPred.ult | `ICmpPred.ult | `ult => some `ult
      | ``ICmpPred.ule | `ICmpPred.ule | `ule => some `ule
      | ``ICmpPred.sgt | `ICmpPred.sgt | `sgt => some `sgt
      | ``ICmpPred.sge | `ICmpPred.sge | `sge => some `sge
      | ``ICmpPred.slt | `ICmpPred.slt | `slt => some `slt
      | ``ICmpPred.sle | `ICmpPred.sle | `sle => some `sle
      | _ => none
    match nm? with
    | some nm => pure (mkIdent nm)
    | none => throw ()
  | _ => throw ()

private def unexpandFCmpPred (stx : Syntax) : UnexpandM (TSyntax `ident) := do
  match stripParens stx with
  | `($id:ident) =>
    let nm? := match id.getId.eraseMacroScopes with
      | ``FCmpPred.ffalse | `FCmpPred.ffalse | `ffalse => some `false
      | ``FCmpPred.oeq    | `FCmpPred.oeq    | `oeq    => some `oeq
      | ``FCmpPred.ogt    | `FCmpPred.ogt    | `ogt    => some `ogt
      | ``FCmpPred.oge    | `FCmpPred.oge    | `oge    => some `oge
      | ``FCmpPred.olt    | `FCmpPred.olt    | `olt    => some `olt
      | ``FCmpPred.ole    | `FCmpPred.ole    | `ole    => some `ole
      | ``FCmpPred.one    | `FCmpPred.one    | `one    => some `one
      | ``FCmpPred.ord    | `FCmpPred.ord    | `ord    => some `ord
      | ``FCmpPred.ueq    | `FCmpPred.ueq    | `ueq    => some `ueq
      | ``FCmpPred.ugt    | `FCmpPred.ugt    | `ugt    => some `ugt
      | ``FCmpPred.uge    | `FCmpPred.uge    | `uge    => some `uge
      | ``FCmpPred.ult    | `FCmpPred.ult    | `ult    => some `ult
      | ``FCmpPred.ule    | `FCmpPred.ule    | `ule    => some `ule
      | ``FCmpPred.une    | `FCmpPred.une    | `une    => some `une
      | ``FCmpPred.uno    | `FCmpPred.uno    | `uno    => some `uno
      | ``FCmpPred.ftrue  | `FCmpPred.ftrue  | `ftrue  => some `true
      | _ => none
    match nm? with
    | some nm => pure (mkIdent nm)
    | none => throw ()
  | _ => throw ()

private def isReservedRawIdKeyword (s : String) : Bool :=
  s ∈ [
    "type", "void", "true", "false", "null", "undef", "poison", "zeroinitializer",
    "def", "let", "in", "where", "match", "with", "do", "fun", "if", "then", "else",
    "for", "return", "import", "open", "end", "section", "namespace", "by", "have",
    "show", "from", "at", "as", "struct", "structure", "inductive", "theorem", "lemma",
    "global", "constant", "declare", "define", "align", "addrspace", "label", "to",
    "cc", "tail", "noreturn", "nobuiltin", "fast", "nnan", "ninf", "nsz", "arcp",
    "contract", "afn", "reassoc", "inbounds", "nusw", "nuw", "noundef", "nonnull",
    "noalias", "readonly", "volatile", "samesign", "exact", "disjoint", "nneg",
    "splat", "fbits", "fspecial", "blockaddress", "denormal_fpenv", "range", "range_list",
    "dereferenceable", "dereferenceable_or_null", "nofpclass", "byval", "sret"
  ]

private def isSimpleRawIdIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs =>
    (c.isAlpha || c == '_') &&
    cs.all (fun ch => ch.isAlphanum || ch == '_') &&
    !isReservedRawIdKeyword s

/-! ### Identifiers -/

@[app_unexpander RawId.name]
def unexpandRawIdName : Unexpander
  | `($_ $s:str) =>
    let str := s.getString
    if isSimpleRawIdIdent str then
      let name := mkIdent (Name.mkSimple str)
      `([llvm-rawid| $name:ident])
    else
      `([llvm-rawid| $s:str])
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
    let id := mkIdent (Name.mkSimple s!"i{w.getNat}")
    `([llvm-type| $id:ident])
  | `($_ $w:term) =>
    `([llvm-type| i$($w:term)])
  | _ => throw ()

@[app_unexpander LlvmType.byte]
def unexpandLlvmTypeByte : Unexpander
  | `($_ $w:num) =>
    let id := mkIdent (Name.mkSimple s!"b{w.getNat}")
    `([llvm-type| $id:ident])
  | `($_ $w:term) =>
    `([llvm-type| b$($w:term)])
  | _ => throw ()

@[app_unexpander LlvmType.i1]
def unexpandLlvmTypeI1 : Unexpander | `($_) => let id := mkIdent `i1; `([llvm-type| $id:ident])
@[app_unexpander LlvmType.i8]
def unexpandLlvmTypeI8 : Unexpander | `($_) => let id := mkIdent `i8; `([llvm-type| $id:ident])
@[app_unexpander LlvmType.i16]
def unexpandLlvmTypeI16 : Unexpander | `($_) => let id := mkIdent `i16; `([llvm-type| $id:ident])
@[app_unexpander LlvmType.i32]
def unexpandLlvmTypeI32 : Unexpander | `($_) => let id := mkIdent `i32; `([llvm-type| $id:ident])
@[app_unexpander LlvmType.i64]
def unexpandLlvmTypeI64 : Unexpander | `($_) => let id := mkIdent `i64; `([llvm-type| $id:ident])
@[app_unexpander LlvmType.f16]
def unexpandLlvmTypeF16 : Unexpander | `($_) => let id := mkIdent `half; `([llvm-type| $id:ident])
@[app_unexpander LlvmType.bf16]
def unexpandLlvmTypeBF16 : Unexpander | `($_) => let id := mkIdent `bfloat; `([llvm-type| $id:ident])
@[app_unexpander LlvmType.f32]
def unexpandLlvmTypeF32 : Unexpander | `($_) => let id := mkIdent `float; `([llvm-type| $id:ident])
@[app_unexpander LlvmType.f64]
def unexpandLlvmTypeF64 : Unexpander | `($_) => let id := mkIdent `double; `([llvm-type| $id:ident])
@[app_unexpander LlvmType.f128]
def unexpandLlvmTypeF128 : Unexpander | `($_) => let id := mkIdent `fp128; `([llvm-type| $id:ident])

@[app_unexpander LlvmType.float]
def unexpandLlvmTypeFloat : Unexpander
  | `($_ $ft:ident) =>
    let name? := match ft.getId.eraseMacroScopes with
      | ``FloatType.half      | `FloatType.half      | `half      => some `half
      | ``FloatType.bfloat    | `FloatType.bfloat    | `bfloat    => some `bfloat
      | ``FloatType.float     | `FloatType.float     | `float     => some `float
      | ``FloatType.double    | `FloatType.double    | `double    => some `double
      | ``FloatType.x86_fp80  | `FloatType.x86_fp80  | `x86_fp80  => some `x86_fp80
      | ``FloatType.fp128     | `FloatType.fp128     | `fp128     => some `fp128
      | ``FloatType.ppc_fp128 | `FloatType.ppc_fp128 | `ppc_fp128 => some `ppc_fp128
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
  | `($_ $n:num) =>
    let id := mkIdent `ptr
    `([llvm-type| $id:ident addrspace($n:num)])
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

@[app_unexpander LlvmType.named]
def unexpandLlvmTypeNamed : Unexpander
  | `($_ $nm) =>
    match asRawId? nm with
    | some nm => `([llvm-type| %$nm:nanollvm_rawid])
    | none => throw ()
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
    | some true  => let id := mkIdent `true; `([llvm-exp| $id:ident])
    | some false => let id := mkIdent `false; `([llvm-exp| $id:ident])
    | none => throw ()
  | _ => throw ()

@[app_unexpander Exp.int]
def unexpandExpInt : Unexpander
  | `($_ $arg) =>
    match stripParens arg with
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

private def mkFloatDecSciLit (m : Nat) (exp10 : Int) : TSyntax `scientific :=
  let s :=
    if exp10 == -1 && m == 0 then
      "0.0"
    else if exp10 < 0 then
      let digits := toString m
      let e := (-exp10).toNat
      if digits.length > e then
        let intPart := digits.take (digits.length - e)
        let fracPart := digits.drop (digits.length - e)
        s!"{intPart}.{fracPart}"
      else
        s!"{m}e{exp10}"
    else
      s!"{m}e{exp10}"
  Syntax.mkScientificLit s

@[app_unexpander Exp.floatDec]
def unexpandExpFloatDec : Unexpander
  | `($_ $neg $m:num $exp10) =>
    match asBool? neg, asSignedIntVal? exp10 with
    | some false, some e =>
      let sci := mkFloatDecSciLit m.getNat e
      `([llvm-exp| $sci:scientific])
    | some true, some e =>
      let sci := mkFloatDecSciLit m.getNat e
      `([llvm-exp| -$sci:scientific])
    | _, _ => throw ()
  | _ => throw ()

private def unexpandFloatSpecialCore (neg isInf quiet : Syntax) (pOpt : Option (TSyntax `num)) :
    UnexpandM (TSyntax `term) :=
  match asBool? neg, asBool? isInf, asBool? quiet with
  | some neg, some isInf, some quiet =>
    let kind :=
      if isInf then mkIdent `inf
      else if quiet then mkIdent `qnan
      else mkIdent `snan
    if neg then
      `([llvm-exp| fspecial(- $kind:ident $[($pOpt:num)]?)])
    else
      `([llvm-exp| fspecial(+ $kind:ident $[($pOpt:num)]?)])
  | _, _, _ => throw ()

@[app_unexpander Exp.floatSpecial]
def unexpandExpFloatSpecial : Unexpander
  | `($_ $neg $isInf $quiet $payload:num) =>
    let pOpt : Option (TSyntax `num) :=
      if payload.getNat == 0 then none else some payload
    unexpandFloatSpecialCore neg isInf quiet pOpt
  | `($_ $neg $isInf $quiet) =>
    unexpandFloatSpecialCore neg isInf quiet none
  | _ => throw ()

@[app_unexpander Exp.blockAddress]
def unexpandExpBlockAddress : Unexpander
  | `($_ $fn $blk) =>
    match asRawId? fn, asRawId? blk with
    | some fn, some blk => `([llvm-exp| blockaddress(@$fn:nanollvm_rawid, %$blk:nanollvm_rawid)])
    | _, _ => throw ()
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

@[app_unexpander Exp.gepConst]
def unexpandExpGepConst : Unexpander
  | `($_ $flags $baseTy $ptr [$idxs,*]) => do
    let gFlags ← unexpandGEPFlags flags
    match asType? baseTy with
    | some baseTy =>
      let ptrTe ← asTypedExp? ptr
      let idxArr ← idxs.getElems.mapM asTypedExp?
      `([llvm-exp| getelementptr $gFlags:nanollvm_gep_flag* ($baseTy:nanollvm_type, $ptrTe:nanollvm_typed_exp $[, $idxArr:nanollvm_typed_exp]*)])
    | none => throw ()
  | _ => throw ()

@[app_unexpander Exp.convConst]
def unexpandExpConvConst : Unexpander
  | `($_ $op $fromTy $v $toTy) =>
    match asConversionOp? op, asType? fromTy, asExp? v, asType? toTy with
    | some op, some fromTy, some v, some toTy =>
      `([llvm-exp| $op:nanollvm_conversion_op ($fromTy:nanollvm_type $v:nanollvm_exp to $toTy:nanollvm_type)])
    | _, _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander Exp.binConst]
def unexpandExpBinConst : Unexpander
  | `($_ $op $ty $v1 $v2) =>
    match asIntBinOp? op, asType? ty, asExp? v1, asExp? v2 with
    | some op, some ty, some v1, some v2 =>
      `([llvm-exp| $op:nanollvm_int_bin_op ($ty:nanollvm_type $v1:nanollvm_exp, $ty:nanollvm_type $v2:nanollvm_exp)])
    | _, _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander Exp.insertElemConst]
def unexpandExpInsertElemConst : Unexpander
  | `($_ $vecTy $vec $valTy $val $idxTy $idx) => do
    match asType? vecTy, asExp? vec, asType? valTy, asExp? val, asType? idxTy, asExp? idx with
    | some vecTy, some vec, some valTy, some val, some idxTy, some idx =>
      let vTe ← `(nanollvm_typed_exp| $vecTy:nanollvm_type $vec:nanollvm_exp)
      let eTe ← `(nanollvm_typed_exp| $valTy:nanollvm_type $val:nanollvm_exp)
      let iTe ← `(nanollvm_typed_exp| $idxTy:nanollvm_type $idx:nanollvm_exp)
      `([llvm-exp| insertelement ($vTe:nanollvm_typed_exp, $eTe:nanollvm_typed_exp, $iTe:nanollvm_typed_exp)])
    | _, _, _, _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander Exp.extractElemConst]
def unexpandExpExtractElemConst : Unexpander
  | `($_ $vecTy $vec $idxTy $idx) => do
    match asType? vecTy, asExp? vec, asType? idxTy, asExp? idx with
    | some vecTy, some vec, some idxTy, some idx =>
      let vTe ← `(nanollvm_typed_exp| $vecTy:nanollvm_type $vec:nanollvm_exp)
      let iTe ← `(nanollvm_typed_exp| $idxTy:nanollvm_type $idx:nanollvm_exp)
      `([llvm-exp| extractelement ($vTe:nanollvm_typed_exp, $iTe:nanollvm_typed_exp)])
    | _, _, _, _ => throw ()
  | _ => throw ()

private def unexpandShuffleMaskElems (mask : Syntax.TSepArray `term ",") :
    UnexpandM (Syntax.TSepArray `nanollvm_shuffle_elem ",") := do
  if mask.getElems.isEmpty then throw ()
  let i32Id := mkIdent `i32
  let elems ← mask.getElems.mapM fun el =>
    match stripParens el with
    | `(some $n:num) | `(Option.some $n:num) => `(nanollvm_shuffle_elem| $i32Id:ident $n:num)
    | `(none) | `(Option.none) => `(nanollvm_shuffle_elem| $i32Id:ident poison)
    | _ => throw ()
  pure elems

@[app_unexpander Exp.shuffleVecConst]
def unexpandExpShuffleVecConst : Unexpander
  | `($_ $vecTy $v1 $v2 [$mask,*]) => do
    let elemsSep ← unexpandShuffleMaskElems mask
    let lenLit := Syntax.mkNumLit (toString mask.getElems.size)
    match asType? vecTy, asExp? v1, asExp? v2 with
    | some vecTy, some v1, some v2 =>
      let v1Te ← `(nanollvm_typed_exp| $vecTy:nanollvm_type $v1:nanollvm_exp)
      let v2Te ← `(nanollvm_typed_exp| $vecTy:nanollvm_type $v2:nanollvm_exp)
      `([llvm-exp| shufflevector ($v1Te:nanollvm_typed_exp, $v2Te:nanollvm_typed_exp, <$lenLit:num x i32> <$elemsSep,*>)])
    | _, _, _ => throw ()
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
  | `($_ $op $ty $v) => do
    let flags ← match stripParens op with
      | `($f:ident $fmf) =>
        match f.getId.eraseMacroScopes with
        | ``FloatUnaryOp.fneg | `FloatUnaryOp.fneg | `fneg => unexpandFMFFlags fmf
        | _ => throw ()
      | `($f:ident) =>
        match f.getId.eraseMacroScopes with
        | ``FloatUnaryOp.fneg | `FloatUnaryOp.fneg | `fneg => pure #[]
        | _ => throw ()
      | _ => throw ()
    match asType? ty, asExp? v with
    | some ty, some v => `([llvm-instruction| fneg $flags:nanollvm_fmf_flag* $ty:nanollvm_type $v:nanollvm_exp])
    | _, _ => throw ()
  | _ => throw ()

@[app_unexpander Instruction.floatBinaryOp]
def unexpandInstructionFloatBinaryOp : Unexpander
  | `($_ $opStx $ty $v1 $v2) => do
    let (opNm, flags) ← match stripParens opStx with
      | `($op:ident $fmf) => pure (op.getId.eraseMacroScopes, ← unexpandFMFFlags fmf)
      | `($op:ident) => pure (op.getId.eraseMacroScopes, #[])
      | _ => throw ()
    match asType? ty, asExp? v1, asExp? v2 with
    | some ty, some v1, some v2 =>
      let fpOp : TSyntax `nanollvm_fp_bin_op ← match opNm with
        | ``FloatBinaryOp.fadd | `FloatBinaryOp.fadd | `fadd => `(nanollvm_fp_bin_op| fadd $flags:nanollvm_fmf_flag*)
        | ``FloatBinaryOp.fsub | `FloatBinaryOp.fsub | `fsub => `(nanollvm_fp_bin_op| fsub $flags:nanollvm_fmf_flag*)
        | ``FloatBinaryOp.fmul | `FloatBinaryOp.fmul | `fmul => `(nanollvm_fp_bin_op| fmul $flags:nanollvm_fmf_flag*)
        | ``FloatBinaryOp.fdiv | `FloatBinaryOp.fdiv | `fdiv => `(nanollvm_fp_bin_op| fdiv $flags:nanollvm_fmf_flag*)
        | ``FloatBinaryOp.frem | `FloatBinaryOp.frem | `frem => `(nanollvm_fp_bin_op| frem $flags:nanollvm_fmf_flag*)
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

private def unexpandPhiCore (ty fmf : Syntax) (incs : Syntax.TSepArray `term ",") (mds : Array (TSyntax `nanollvm_value_attr)) :
    UnexpandM (TSyntax `term) := do
  if incs.getElems.isEmpty then throw ()
  let flags ← unexpandFMFFlags fmf
  match asType? ty with
  | none => throw ()
  | some ty =>
    let incArr ← incs.getElems.mapM fun inc =>
      match stripParens inc with
      | `(($e, $lbl)) | `(⟨$e, $lbl⟩) =>
        match asExp? e, asRawId? lbl with
        | some e, some lbl => `(nanollvm_phi_incoming| [$e:nanollvm_exp, %$lbl:nanollvm_rawid])
        | _, _ => throw ()
      | _ => throw ()
    let inc0 := incArr[0]!
    let incRest := incArr.extract 1 incArr.size
    `([llvm-instruction| phi $flags:nanollvm_fmf_flag* $ty:nanollvm_type $inc0:nanollvm_phi_incoming $[, $incRest:nanollvm_phi_incoming]* $[, !$mds:nanollvm_value_attr]*])

@[app_unexpander Instruction.phi]
def unexpandInstructionPhi : Unexpander
  | `($_ $ty $fmf [$incs,*] $md) => do
    let mds ← unexpandValueAttrList md
    unexpandPhiCore ty fmf incs mds
  | `($_ $ty $fmf [$incs,*]) =>
    unexpandPhiCore ty fmf incs #[]
  | _ => throw ()

@[app_unexpander Instruction.alloca]
def unexpandInstructionAlloca : Unexpander
  | `($_ $ty $numEl $al $as) => do
    match asType? ty with
    | none => throw ()
    | some ty =>
      let mut opts : Array (TSyntax `nanollvm_alloca_opt) := #[]
      match stripParens numEl with
      | `(none) | `(Option.none) => pure ()
      | `(some $te) | `(Option.some $te) =>
        let te ← asTypedExp? te
        opts := opts.push (← `(nanollvm_alloca_opt| $te:nanollvm_typed_exp))
      | _ => throw ()
      match stripParens al with
      | `(none) | `(Option.none) => pure ()
      | `(some $n:num) | `(Option.some $n:num) =>
        opts := opts.push (← `(nanollvm_alloca_opt| align $n:num))
      | _ => throw ()
      match stripParens as with
      | `(0) => pure ()
      | `($n:num) => opts := opts.push (← `(nanollvm_alloca_opt| addrspace($n:num)))
      | _ => throw ()
      `([llvm-instruction| alloca $ty:nanollvm_type $[, $opts:nanollvm_alloca_opt]*])
  | `($_ $ty $numEl $al) => do
    match asType? ty with
    | none => throw ()
    | some ty =>
      let mut opts : Array (TSyntax `nanollvm_alloca_opt) := #[]
      match stripParens numEl with
      | `(none) | `(Option.none) => pure ()
      | `(some $te) | `(Option.some $te) =>
        let te ← asTypedExp? te
        opts := opts.push (← `(nanollvm_alloca_opt| $te:nanollvm_typed_exp))
      | _ => throw ()
      match stripParens al with
      | `(none) | `(Option.none) => pure ()
      | `(some $n:num) | `(Option.some $n:num) =>
        opts := opts.push (← `(nanollvm_alloca_opt| align $n:num))
      | _ => throw ()
      `([llvm-instruction| alloca $ty:nanollvm_type $[, $opts:nanollvm_alloca_opt]*])
  | _ => throw ()

private def unexpandLoadCore (ty pTy ptr al : Syntax) (isVol nu : Bool) (mds : Array (TSyntax `nanollvm_value_attr)) :
    UnexpandM (TSyntax `term) := do
  match asType? ty, asType? pTy, asExp? ptr with
  | some ty, some pTy, some ptr =>
    let mut opts : Array (TSyntax `nanollvm_load_opt) := #[]
    match stripParens al with
    | `(none) | `(Option.none) => pure ()
    | `(some $n:num) | `(Option.some $n:num) =>
      opts := opts.push (← `(nanollvm_load_opt| align $n:num))
    | _ => throw ()
    if nu then opts := opts.push (← `(nanollvm_load_opt| !noundef))
    for md in mds do
      opts := opts.push (← `(nanollvm_load_opt| !$md:nanollvm_value_attr))
    if isVol then
      `([llvm-instruction| load volatile $ty:nanollvm_type, $pTy:nanollvm_type $ptr:nanollvm_exp $[, $opts:nanollvm_load_opt]*])
    else
      `([llvm-instruction| load $ty:nanollvm_type, $pTy:nanollvm_type $ptr:nanollvm_exp $[, $opts:nanollvm_load_opt]*])
  | _, _, _ => throw ()

@[app_unexpander Instruction.load]
def unexpandInstructionLoad : Unexpander
  | `($_ $ty $pTy $ptr $al $isVol $nu $md) => do
    match asBool? isVol, asBool? nu with
    | some isVol, some nu =>
      let mds ← unexpandValueAttrList md
      unexpandLoadCore ty pTy ptr al isVol nu mds
    | _, _ => throw ()
  | `($_ $ty $pTy $ptr $al $isVol $nu) => do
    match asBool? isVol, asBool? nu with
    | some isVol, some nu => unexpandLoadCore ty pTy ptr al isVol nu #[]
    | _, _ => throw ()
  | `($_ $ty $pTy $ptr $al $isVol) => do
    match asBool? isVol with
    | some isVol => unexpandLoadCore ty pTy ptr al isVol false #[]
    | none => throw ()
  | `($_ $ty $pTy $ptr $al) =>
    unexpandLoadCore ty pTy ptr al false false #[]
  | _ => throw ()

@[app_unexpander Instruction.store]
def unexpandInstructionStore : Unexpander
  | `($_ $vTy $v $pTy $ptr $al $isVol) => do
    match asType? vTy, asExp? v, asType? pTy, asExp? ptr, asBool? isVol with
    | some vTy, some v, some pTy, some ptr, some isVol =>
      match stripParens al with
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
      match stripParens al with
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
    let elemsSep ← unexpandShuffleMaskElems mask
    let lenLit := Syntax.mkNumLit (toString mask.getElems.size)
    match asType? vecTy, asExp? v1, asExp? v2 with
    | some vecTy, some v1, some v2 =>
      `([llvm-instruction| shufflevector $vecTy:nanollvm_type $v1:nanollvm_exp, $vecTy:nanollvm_type $v2:nanollvm_exp, <$lenLit:num x i32> <$elemsSep,*>])
    | _, _, _ => throw ()
  | _ => throw ()

private def unexpandCallArgs (args : Syntax.TSepArray `term ",") :
    UnexpandM (Syntax.TSepArray `nanollvm_call_arg ",") := do
  let callArgs ← args.getElems.mapM fun a =>
    match stripParens a with
    | `(($t, $e, $attrs)) | `(⟨$t, $e, $attrs⟩) => do
      let as ← unexpandValueAttrList attrs
      match asType? t, asExp? e with
      | some t, some e => `(nanollvm_call_arg| $t:nanollvm_type $as:nanollvm_value_attr* $e:nanollvm_exp)
      | _, _ => throw ()
    | _ => throw ()
  pure callArgs

private def unexpandOpBundles (stx : Syntax) : UnexpandM (Option (Syntax.TSepArray `nanollvm_op_bundle ",")) := do
  match stripParens stx with
  | `([]) => pure none
  | `([$bs,*]) =>
    if bs.getElems.isEmpty then return none
    let arr ← bs.getElems.mapM fun b =>
      match stripParens b with
      | `(($tag:str, [$tes,*])) | `(⟨$tag:str, [$tes,*]⟩) => do
        let teArr ← tes.getElems.mapM asTypedExp?
        let teSep : Syntax.TSepArray `nanollvm_typed_exp "," := teArr
        `(nanollvm_op_bundle| $tag:str ($teSep,*))
      | _ => throw ()
    let sep : Syntax.TSepArray `nanollvm_op_bundle "," := arr
    pure (some sep)
  | _ => throw ()

private def unexpandCallCore (retTy fmf callee : Syntax) (args : Syntax.TSepArray `term ",")
    (rAttrs : Array (TSyntax `nanollvm_value_attr))
    (bundlesOpt : Option (Syntax.TSepArray `nanollvm_op_bundle ","))
    (isNoReturn isTail : Bool) (ccStr : String) : UnexpandM (TSyntax `term) := do
  let flags ← unexpandFMFFlags fmf
  let callArgsSep ← unexpandCallArgs args
  match asType? retTy, asExp? callee with
  | some retTy, some callee =>
    let ccOpt : Option (TSyntax `str) := if ccStr.isEmpty then none else some (Syntax.mkStrLit ccStr)
    match isTail, isNoReturn, bundlesOpt with
    | false, false, none =>
      `([llvm-instruction| call $flags:nanollvm_fmf_flag* $[cc $ccOpt:str]? $rAttrs:nanollvm_value_attr* $retTy:nanollvm_type $callee:nanollvm_exp($callArgsSep,*)])
    | true, false, none =>
      `([llvm-instruction| tail call $flags:nanollvm_fmf_flag* $[cc $ccOpt:str]? $rAttrs:nanollvm_value_attr* $retTy:nanollvm_type $callee:nanollvm_exp($callArgsSep,*)])
    | false, true, none =>
      `([llvm-instruction| call $flags:nanollvm_fmf_flag* $[cc $ccOpt:str]? $rAttrs:nanollvm_value_attr* $retTy:nanollvm_type $callee:nanollvm_exp($callArgsSep,*) noreturn])
    | true, true, none =>
      `([llvm-instruction| tail call $flags:nanollvm_fmf_flag* $[cc $ccOpt:str]? $rAttrs:nanollvm_value_attr* $retTy:nanollvm_type $callee:nanollvm_exp($callArgsSep,*) noreturn])
    | false, false, some bs =>
      `([llvm-instruction| call $flags:nanollvm_fmf_flag* $[cc $ccOpt:str]? $rAttrs:nanollvm_value_attr* $retTy:nanollvm_type $callee:nanollvm_exp($callArgsSep,*) [$bs,*]])
    | true, false, some bs =>
      `([llvm-instruction| tail call $flags:nanollvm_fmf_flag* $[cc $ccOpt:str]? $rAttrs:nanollvm_value_attr* $retTy:nanollvm_type $callee:nanollvm_exp($callArgsSep,*) [$bs,*]])
    | false, true, some bs =>
      `([llvm-instruction| call $flags:nanollvm_fmf_flag* $[cc $ccOpt:str]? $rAttrs:nanollvm_value_attr* $retTy:nanollvm_type $callee:nanollvm_exp($callArgsSep,*) [$bs,*] noreturn])
    | true, true, some bs =>
      `([llvm-instruction| tail call $flags:nanollvm_fmf_flag* $[cc $ccOpt:str]? $rAttrs:nanollvm_value_attr* $retTy:nanollvm_type $callee:nanollvm_exp($callArgsSep,*) [$bs,*] noreturn])
  | _, _ => throw ()

@[app_unexpander Instruction.call]
def unexpandInstructionCall : Unexpander
  | `($_ $retTy $fmf $callee [$args,*] $retAttrs $bundles $isNoRet $site) => do
    let rAttrs ← unexpandValueAttrList retAttrs
    let bundlesOpt ← unexpandOpBundles bundles
    match asBool? isNoRet with
    | some isNoRet =>
      let (isTail, ccStr) ← unexpandCallSiteInfo site
      unexpandCallCore retTy fmf callee args rAttrs bundlesOpt isNoRet isTail ccStr
    | none => throw ()
  | `($_ $retTy $fmf $callee [$args,*] $retAttrs $bundles $isNoRet) => do
    let rAttrs ← unexpandValueAttrList retAttrs
    let bundlesOpt ← unexpandOpBundles bundles
    match asBool? isNoRet with
    | some isNoRet =>
      unexpandCallCore retTy fmf callee args rAttrs bundlesOpt isNoRet false ""
    | none => throw ()
  | `($_ $retTy $fmf $callee [$args,*] $retAttrs $bundles) => do
    let rAttrs ← unexpandValueAttrList retAttrs
    let bundlesOpt ← unexpandOpBundles bundles
    unexpandCallCore retTy fmf callee args rAttrs bundlesOpt false false ""
  | `($_ $retTy $fmf $callee [$args,*] $retAttrs) => do
    let rAttrs ← unexpandValueAttrList retAttrs
    unexpandCallCore retTy fmf callee args rAttrs none false false ""
  | `($_ $retTy $fmf $callee [$args,*]) =>
    unexpandCallCore retTy fmf callee args #[] none false false ""
  | _ => throw ()

@[app_unexpander Instruction.freeze]
def unexpandInstructionFreeze : Unexpander
  | `($_ $tv) =>
    match stripParens tv with
    | `(⟨$ty, $v⟩) | `(($ty, $v)) =>
      match asType? ty, asExp? v with
      | some ty, some v => `([llvm-instruction| freeze $ty:nanollvm_type $v:nanollvm_exp])
      | _, _ => throw ()
    | _ => throw ()
  | _ => throw ()

@[app_unexpander Instruction.bitinsert]
def unexpandInstructionBitinsert : Unexpander
  | `($_ $bTy $b $vTy $v $oTy $o) =>
    match asType? bTy, asExp? b, asType? vTy, asExp? v, asType? oTy, asExp? o with
    | some bTy, some b, some vTy, some v, some oTy, some o =>
      `([llvm-instruction| bitinsert $bTy:nanollvm_type $b:nanollvm_exp, $vTy:nanollvm_type $v:nanollvm_exp, $oTy:nanollvm_type $o:nanollvm_exp])
    | _, _, _, _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander Instruction.bitextract]
def unexpandInstructionBitextract : Unexpander
  | `($_ $rTy $sTy $s $oTy $o) =>
    match asType? rTy, asType? sTy, asExp? s, asType? oTy, asExp? o with
    | some rTy, some sTy, some s, some oTy, some o =>
      `([llvm-instruction| bitextract $rTy:nanollvm_type, $sTy:nanollvm_type $s:nanollvm_exp, $oTy:nanollvm_type $o:nanollvm_exp])
    | _, _, _, _, _ => throw ()
  | _ => throw ()

/-! ### Terminators -/

@[app_unexpander Terminator.retVoid]
def unexpandTerminatorRetVoid : Unexpander
  | `($_) => `([llvm-terminator| ret void])

@[app_unexpander Terminator.ret]
def unexpandTerminatorRet : Unexpander
  | `($_ $tv) =>
    match stripParens tv with
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
        match stripParens c with
        | `(($v, $lbl)) | `(⟨$v, $lbl⟩) => do
          let vS ← asSignedInt? v
          match asRawId? lbl with
          | some lbl => `(nanollvm_switch_case| $ty:nanollvm_type $vS:nanollvm_signed_int, label %$lbl:nanollvm_rawid)
          | none => throw ()
        | _ => throw ()
      `([llvm-terminator| switch $ty:nanollvm_type $cond:nanollvm_exp, label %$defDest:nanollvm_rawid [ $caseArr:nanollvm_switch_case* ]])
    | _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander Terminator.indirectBr]
def unexpandTerminatorIndirectBr : Unexpander
  | `($_ $addr [$dests,*]) => do
    match asExp? addr with
    | some addr =>
      let destArr ← dests.getElems.mapM fun d =>
        match asRawId? d with
        | some lbl => `(nanollvm_indirectbr_dest| label %$lbl:nanollvm_rawid)
        | none => throw ()
      let destSep : Syntax.TSepArray `nanollvm_indirectbr_dest "," := destArr
      `([llvm-terminator| indirectbr ptr $addr:nanollvm_exp, [$destSep,*]])
    | none => throw ()
  | _ => throw ()

@[app_unexpander Terminator.unreachable]
def unexpandTerminatorUnreachable : Unexpander
  | `($_) => `([llvm-terminator| unreachable])

/-! ### Declarations, Blocks, Definitions, Globals, Modules -/

private def unexpandDeclarationCore (name ty : Syntax)
    (aAttrsList : Array (Array (TSyntax `nanollvm_value_attr)))
    (rAttrs : Array (TSyntax `nanollvm_value_attr))
    (isNoRet isNoBuiltin : Bool)
    (denormOpt : Option (TSyntax `nanollvm_fn_attr))
    (ccStr : String) : UnexpandM (TSyntax `term) := do
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
      let mut fnAttrs : Array (TSyntax `nanollvm_fn_attr) := #[]
      if isNoRet then fnAttrs := fnAttrs.push (← `(nanollvm_fn_attr| noreturn))
      if isNoBuiltin then fnAttrs := fnAttrs.push (← `(nanollvm_fn_attr| nobuiltin))
      if let some d := denormOpt then fnAttrs := fnAttrs.push d
      let ccOpt : Option (TSyntax `str) := if ccStr.isEmpty then none else some (Syntax.mkStrLit ccStr)
      `([llvm-declaration| declare $[cc $ccOpt:str]? $rAttrs:nanollvm_value_attr* $retTy:nanollvm_type @$name:nanollvm_rawid($dArgsSep,*) $fnAttrs:nanollvm_fn_attr*])
    | _ => throw ()
  | _, _ => throw ()

private def unexpandArgAttrLists (argAttrs : Syntax) :
    UnexpandM (Array (Array (TSyntax `nanollvm_value_attr))) :=
  match stripParens argAttrs with
  | `([]) => pure #[]
  | `([$xs,*]) => xs.getElems.mapM unexpandValueAttrList
  | _ => throw ()

private def unexpandDenormOpt (denorm : Syntax) : UnexpandM (Option (TSyntax `nanollvm_fn_attr)) := do
  match stripParens denorm with
  | `(none) | `(Option.none) => pure none
  | `(some $d) | `(Option.some $d) => pure (some (← unexpandDenormalMode d))
  | _ => throw ()

@[app_unexpander Declaration.mk]
def unexpandDeclarationMk : Unexpander
  | `($_ $name $ty $argAttrs $retAttrs $isNoRet $isNoBuiltin $denorm $ccVal $denormF32 $pers) => do
    -- the `float:` override and the personality have no surface syntax in `[llvm-definition| ...]`
    match stripParens denormF32, stripParens pers with
    | `(none), `(none) | `(Option.none), `(none) | `(none), `(Option.none) | `(Option.none), `(Option.none) => pure ()
    | _, _ => throw ()
    let rAttrs ← unexpandValueAttrList retAttrs
    let aAttrsList ← unexpandArgAttrLists argAttrs
    let denormOpt ← unexpandDenormOpt denorm
    match asBool? isNoRet, asBool? isNoBuiltin, asStr? ccVal with
    | some isNoRet, some isNoBuiltin, some ccStr =>
      unexpandDeclarationCore name ty aAttrsList rAttrs isNoRet isNoBuiltin denormOpt ccStr
    | _, _, _ => throw ()
  | `($_ $name $ty $argAttrs $retAttrs $isNoRet $isNoBuiltin $denorm $ccVal) => do
    let rAttrs ← unexpandValueAttrList retAttrs
    let aAttrsList ← unexpandArgAttrLists argAttrs
    let denormOpt ← unexpandDenormOpt denorm
    match asBool? isNoRet, asBool? isNoBuiltin, asStr? ccVal with
    | some isNoRet, some isNoBuiltin, some ccStr =>
      unexpandDeclarationCore name ty aAttrsList rAttrs isNoRet isNoBuiltin denormOpt ccStr
    | _, _, _ => throw ()
  | `($_ $name $ty $argAttrs $retAttrs $isNoRet $isNoBuiltin $denorm) => do
    let rAttrs ← unexpandValueAttrList retAttrs
    let aAttrsList ← unexpandArgAttrLists argAttrs
    let denormOpt ← unexpandDenormOpt denorm
    match asBool? isNoRet, asBool? isNoBuiltin with
    | some isNoRet, some isNoBuiltin =>
      unexpandDeclarationCore name ty aAttrsList rAttrs isNoRet isNoBuiltin denormOpt ""
    | _, _ => throw ()
  | `($_ $name $ty $argAttrs $retAttrs $isNoRet $isNoBuiltin) => do
    let rAttrs ← unexpandValueAttrList retAttrs
    let aAttrsList ← unexpandArgAttrLists argAttrs
    match asBool? isNoRet, asBool? isNoBuiltin with
    | some isNoRet, some isNoBuiltin =>
      unexpandDeclarationCore name ty aAttrsList rAttrs isNoRet isNoBuiltin none ""
    | _, _ => throw ()
  | `($_ $name $ty $argAttrs $retAttrs $isNoRet) => do
    let rAttrs ← unexpandValueAttrList retAttrs
    let aAttrsList ← unexpandArgAttrLists argAttrs
    match asBool? isNoRet with
    | some isNoRet =>
      unexpandDeclarationCore name ty aAttrsList rAttrs isNoRet false none ""
    | none => throw ()
  | `($_ $name $ty $argAttrs $retAttrs) => do
    let rAttrs ← unexpandValueAttrList retAttrs
    let aAttrsList ← unexpandArgAttrLists argAttrs
    unexpandDeclarationCore name ty aAttrsList rAttrs false false none ""
  | `($_ $name $ty $argAttrs) => do
    let aAttrsList ← unexpandArgAttrLists argAttrs
    unexpandDeclarationCore name ty aAttrsList #[] false false none ""
  | `($_ $name $ty) =>
    unexpandDeclarationCore name ty #[] #[] false false none ""
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
  | `($(_) $x $rest) => do
    let x : TSyntax `nanollvm_codeline ← asCodeline x
    let xs : Array (TSyntax `nanollvm_codeline) ←
      match rest with
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
    let term : TSyntax `nanollvm_terminator ← match stripParens term with
      | `(($_, $term)) | `(⟨$_, $term⟩) =>
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
      | `(nanollvm_declaration| declare $[cc $ccName:str]? $rAttrs:nanollvm_value_attr* $retTy:nanollvm_type @$name:nanollvm_rawid($dArgs,*) $fnAttrs:nanollvm_fn_attr*) =>
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
          `([llvm-definition| define $[cc $ccName:str]? $rAttrs:nanollvm_value_attr* $retTy:nanollvm_type @$name:nanollvm_rawid($argsSep,*) $fnAttrs:nanollvm_fn_attr* {
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
      let initOpt : Option (TSyntax `nanollvm_exp) ← match stripParens init with
        | `(none) | `(Option.none) => pure none
        | `(some $e) | `(Option.some $e) =>
          match asExp? e with
          | some e => pure (some e)
          | none => throw ()
        | _ => throw ()
      let alignOpt : Option (TSyntax `num) ← match stripParens al with
        | `(none) | `(Option.none) => pure none
        | `(some $n:num) | `(Option.some $n:num) => pure (some n)
        | _ => throw ()
      let asOpt : Option (TSyntax `num) ← match stripParens as with
        | `(0) => pure none
        | `($n:num) => pure (some n)
        | _ => throw ()
      if isConst then
        `([llvm-global| @$name:nanollvm_rawid = $[addrspace($asOpt:num)]? constant $ty:nanollvm_type $[$initOpt:nanollvm_exp]? $[, align $alignOpt:num]?])
      else
        `([llvm-global| @$name:nanollvm_rawid = $[addrspace($asOpt:num)]? global $ty:nanollvm_type $[$initOpt:nanollvm_exp]? $[, align $alignOpt:num]?])
    | _, _, _ => throw ()
  | _ => throw ()

@[app_unexpander TopLevelEntity.typeDef]
def unexpandTopLevelEntityTypeDef : Unexpander
  | `($_ $nm $ty) =>
    match asRawId? nm, asType? ty with
    | some nm, some ty => `([llvm-entity| %$nm:nanollvm_rawid = type $ty:nanollvm_type])
    | _, _ => throw ()
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
