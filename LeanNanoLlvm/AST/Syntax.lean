import Lean
import LeanNanoLlvm.AST.AST

namespace LeanNanoLlvm.AST.Syntax

open Lean Lean.Meta Lean.Elab Lean.Elab.Term
open LeanNanoLlvm.AST
open scoped LeanNanoLlvm.AST.Syntax

deriving instance Lean.ToExpr for FloatType
deriving instance Lean.ToExpr for FastMathFlags
deriving instance Lean.ToExpr for ICmpPred
deriving instance Lean.ToExpr for FCmpPred
deriving instance Lean.ToExpr for GEPFlags

declare_syntax_cat nanollvm_rawid
scoped syntax ident : nanollvm_rawid
scoped syntax num : nanollvm_rawid

def elabNanoLlvmRawId : Syntax → TermElabM Expr
  | `(nanollvm_rawid| $s:ident) => mkAppM ``RawId.name #[mkStrLit s.getId.toString]
  | `(nanollvm_rawid| $n:num) => mkAppM ``RawId.anonymous #[mkNatLit n.getNat]
  | _ => throwUnsupportedSyntax

elab "[llvm-rawid|" p:nanollvm_rawid "]" : term => elabNanoLlvmRawId p

declare_syntax_cat nanollvm_identifier
scoped syntax "@" nanollvm_rawid : nanollvm_identifier
scoped syntax "%" nanollvm_rawid : nanollvm_identifier

def elabNanoLlvmIdentifier : Syntax → TermElabM Expr
  | `(nanollvm_identifier| @ $id:nanollvm_rawid) => do
    let rawid ← elabNanoLlvmRawId id
    mkAppM ``Identifier.global_id #[rawid]
  | `(nanollvm_identifier| % $id:nanollvm_rawid) => do
    let rawid ← elabNanoLlvmRawId id
    mkAppM ``Identifier.local_id #[rawid]
  | _ => throwUnsupportedSyntax

elab "[llvm-identifier|" p:nanollvm_identifier "]" : term => elabNanoLlvmIdentifier p

declare_syntax_cat nanollvm_instruction_id
scoped syntax "void " "(" num ")" : nanollvm_instruction_id
scoped syntax "%" nanollvm_rawid : nanollvm_instruction_id

def elabNanoLlvmInstructionId : Syntax → TermElabM Expr
  | `(nanollvm_instruction_id| void ($n:num)) =>
    mkAppM ``InstructionId.void #[mkNatLit n.getNat]
  | `(nanollvm_instruction_id | %$id:nanollvm_rawid) => do
    let rawid ← elabNanoLlvmRawId id
    mkAppM ``InstructionId.id #[rawid]
  | _ => throwUnsupportedSyntax

elab "[llvm-instruction-id|" p:nanollvm_instruction_id "]" : term => elabNanoLlvmInstructionId p

/-! ### Types (with Lean term antiquotation `i$(w)` for width polymorphism) -/

declare_syntax_cat nanollvm_type
declare_syntax_cat nanollvm_fn_param
scoped syntax nanollvm_type : nanollvm_fn_param
scoped syntax "..." : nanollvm_fn_param
scoped syntax "void" : nanollvm_type
scoped syntax ident : nanollvm_type
scoped syntax "i$(" term ")" : nanollvm_type
scoped syntax nanollvm_type " addrspace(" num ")" : nanollvm_type
scoped syntax "<" num &"x" nanollvm_type ">" : nanollvm_type
scoped syntax "[" num &"x" nanollvm_type "]" : nanollvm_type
scoped syntax "{" nanollvm_type,* "}" : nanollvm_type
scoped syntax "<{" nanollvm_type,* "}>" : nanollvm_type
scoped syntax "%" nanollvm_rawid : nanollvm_type
scoped syntax nanollvm_type "(" nanollvm_fn_param,* ")" : nanollvm_type

mutual
partial def elabNanoLlvmType : Syntax → TermElabM Expr
  | `(nanollvm_type| $id:ident) => do
    let s := id.getId.toString
    match s with
    | "half"   => mkAppM ``LlvmType.float #[mkConst ``FloatType.half]
    | "bfloat" => mkAppM ``LlvmType.float #[mkConst ``FloatType.bfloat]
    | "float"  => mkAppM ``LlvmType.float #[mkConst ``FloatType.float]
    | "double" => mkAppM ``LlvmType.float #[mkConst ``FloatType.double]
    | "fp128"  => mkAppM ``LlvmType.float #[mkConst ``FloatType.fp128]
    | "ptr"    => mkAppM ``LlvmType.ptr #[mkNatLit 0]
    | _ =>
      if s.startsWith "i" then
        let numStr := s.drop 1
        match numStr.toNat? with
        | some n => mkAppM ``LlvmType.int #[mkNatLit n]
        | none => throwErrorAt id "Invalid LLVM type: {s}"
      else
        throwErrorAt id "Unknown LLVM type: {s}"

  | `(nanollvm_type| i$($w:term)) => do
    let wExpr ← elabTermEnsuringType w (mkConst ``Nat)
    mkAppM ``LlvmType.int #[wExpr]

  | `(nanollvm_type| $base:nanollvm_type addrspace($as:num)) => do
    match base with
    | `(nanollvm_type| $id:ident) =>
      if id.getId.toString == "ptr" then
        mkAppM ``LlvmType.ptr #[mkNatLit as.getNat]
      else
        throwErrorAt base "Expected 'ptr' before addrspace(...), got {id}"
    | _ => throwErrorAt base "Expected 'ptr' before addrspace(...)"

  | `(nanollvm_type| < $n:num x $elem:nanollvm_type >) => do
    let elemTy ← elabNanoLlvmType elem
    mkAppM ``LlvmType.vector #[mkNatLit n.getNat, elemTy]

  | `(nanollvm_type| [ $n:num x $elem:nanollvm_type ]) => do
    let elemTy ← elabNanoLlvmType elem
    mkAppM ``LlvmType.array #[mkNatLit n.getNat, elemTy]

  | `(nanollvm_type| { $fields:nanollvm_type,* }) => do
    let fVals ← fields.getElems.mapM (fun x => elabNanoLlvmType x.raw)
    let fList ← mkListLit (mkConst ``LlvmType) fVals.toList
    mkAppM ``LlvmType.struct #[toExpr Bool.false, fList]

  | `(nanollvm_type| <{ $fields:nanollvm_type,* }>) => do
    let fVals ← fields.getElems.mapM (fun x => elabNanoLlvmType x.raw)
    let fList ← mkListLit (mkConst ``LlvmType) fVals.toList
    mkAppM ``LlvmType.struct #[toExpr Bool.true, fList]

  | `(nanollvm_type| %$nm:nanollvm_rawid) => do
    mkAppM ``LlvmType.named #[← elabNanoLlvmRawId nm]

  | `(nanollvm_type| $ret:nanollvm_type ( $params:nanollvm_fn_param,* )) => do
    let ret ← elabNanoLlvmRetType ret
    let mut argVals : Array Expr := #[]
    let mut isVarArg := false
    for p in params.getElems do
      if isVarArg then throwErrorAt p "Vararg '...' must be the last parameter"
      match p.raw with
      | `(nanollvm_fn_param| ...) => isVarArg := true
      | `(nanollvm_fn_param| $t:nanollvm_type) => argVals := argVals.push (← elabNanoLlvmType t)
      | _ => throwUnsupportedSyntax
    let argList ← mkListLit (mkConst ``LlvmType) argVals.toList
    mkAppM ``LlvmType.function #[ret, argList, toExpr isVarArg]

  | _ => throwUnsupportedSyntax

partial def elabNanoLlvmRetType : Syntax → TermElabM Expr
  | `(nanollvm_type| void) => pure (mkConst ``LlvmRetType.void)
  | stx => do
    let ty ← elabNanoLlvmType stx
    mkAppM ``LlvmRetType.ret #[ty]
end

elab "[llvm-type|" p:nanollvm_type "]" : term => elabNanoLlvmType p

/-! ### Value Attributes -/

private def mkIntLitExpr (i : Int) : MetaM Expr := do
  if i ≥ 0 then
    mkAppM ``Int.ofNat #[mkNatLit i.toNat]
  else
    mkAppM ``Int.negSucc #[mkNatLit ((-i - 1).toNat)]

declare_syntax_cat nanollvm_signed_int
scoped syntax num : nanollvm_signed_int
scoped syntax "-" num : nanollvm_signed_int

private def elabSignedInt : Syntax → MetaM Expr
  | `(nanollvm_signed_int| $n:num) => mkIntLitExpr (n.getNat : Int)
  | `(nanollvm_signed_int| -$n:num) => mkIntLitExpr (-(n.getNat : Int))
  | _ => throwUnsupportedSyntax

declare_syntax_cat nanollvm_value_attr
scoped syntax "noundef" : nanollvm_value_attr
scoped syntax "nonnull" : nanollvm_value_attr
scoped syntax "align " num : nanollvm_value_attr
scoped syntax "dereferenceable(" num ")" : nanollvm_value_attr
scoped syntax "dereferenceable_or_null(" num ")" : nanollvm_value_attr
scoped syntax "range(" nanollvm_signed_int ", " nanollvm_signed_int ")" : nanollvm_value_attr
scoped syntax "nofpclass(" num ")" : nanollvm_value_attr
scoped syntax "byval(" nanollvm_type ")" : nanollvm_value_attr
scoped syntax "sret(" nanollvm_type ")" : nanollvm_value_attr
scoped syntax "noalias" : nanollvm_value_attr
scoped syntax "readonly" : nanollvm_value_attr

def elabNanoLlvmValueAttr : Syntax → TermElabM Expr
  | `(nanollvm_value_attr| noundef) => pure (mkConst ``ValueAttr.noundef)
  | `(nanollvm_value_attr| nonnull) => pure (mkConst ``ValueAttr.nonnull)
  | `(nanollvm_value_attr| align $n:num) => mkAppM ``ValueAttr.align #[mkNatLit n.getNat]
  | `(nanollvm_value_attr| dereferenceable($n:num)) =>
      mkAppM ``ValueAttr.dereferenceable #[mkNatLit n.getNat]
  | `(nanollvm_value_attr| dereferenceable_or_null($n:num)) =>
      mkAppM ``ValueAttr.dereferenceableOrNull #[mkNatLit n.getNat]
  | `(nanollvm_value_attr| range($lo:nanollvm_signed_int, $hi:nanollvm_signed_int)) => do
      let loE ← elabSignedInt lo
      let hiE ← elabSignedInt hi
      mkAppM ``ValueAttr.range #[loE, hiE]
  | `(nanollvm_value_attr| nofpclass($m:num)) =>
      mkAppM ``ValueAttr.nofpclass #[mkNatLit m.getNat]
  | `(nanollvm_value_attr| byval($ty:nanollvm_type)) => do
      let tyE ← elabNanoLlvmType ty
      mkAppM ``ValueAttr.byval #[tyE]
  | `(nanollvm_value_attr| sret($ty:nanollvm_type)) => do
      let tyE ← elabNanoLlvmType ty
      mkAppM ``ValueAttr.sret #[tyE]
  | `(nanollvm_value_attr| noalias) => pure (mkConst ``ValueAttr.noalias)
  | `(nanollvm_value_attr| readonly) => pure (mkConst ``ValueAttr.readonly)
  | _ => throwUnsupportedSyntax

private def elabValueAttrList (attrs : Array (TSyntax `nanollvm_value_attr)) : TermElabM Expr := do
  let es ← attrs.toList.mapM (fun a => elabNanoLlvmValueAttr a.raw)
  mkListLit (mkConst ``ValueAttr) es

/-! ### Expressions & Constants -/

declare_syntax_cat nanollvm_exp
declare_syntax_cat nanollvm_typed_exp

scoped syntax nanollvm_type ppHardSpace nanollvm_exp : nanollvm_typed_exp

scoped syntax nanollvm_identifier : nanollvm_exp
scoped syntax "<" ident ":int>" : nanollvm_exp
scoped syntax ident : nanollvm_exp
scoped syntax num : nanollvm_exp
scoped syntax "-" num : nanollvm_exp
scoped syntax scientific : nanollvm_exp
scoped syntax "-" scientific : nanollvm_exp
scoped syntax "fbits(" num ")" : nanollvm_exp
scoped syntax "null" : nanollvm_exp
scoped syntax "zeroinitializer" : nanollvm_exp
scoped syntax "undef" : nanollvm_exp
scoped syntax "poison" : nanollvm_exp
scoped syntax "[" nanollvm_typed_exp,* "]" : nanollvm_exp
scoped syntax "{" nanollvm_typed_exp,* "}" : nanollvm_exp
scoped syntax "<{" nanollvm_typed_exp,* "}>" : nanollvm_exp
scoped syntax "<" nanollvm_typed_exp,+ ">" : nanollvm_exp
scoped syntax "splat" "(" nanollvm_typed_exp ")" : nanollvm_exp
scoped syntax "getelementptr" (" inbounds ")? "(" nanollvm_type ", " nanollvm_typed_exp (", " nanollvm_typed_exp)* ")" : nanollvm_exp
scoped syntax "ptrtoint" "(" nanollvm_type ppHardSpace nanollvm_exp " to " nanollvm_type ")" : nanollvm_exp
scoped syntax "ptrtoaddr" "(" nanollvm_type ppHardSpace nanollvm_exp " to " nanollvm_type ")" : nanollvm_exp
scoped syntax "inttoptr" "(" nanollvm_type ppHardSpace nanollvm_exp " to " nanollvm_type ")" : nanollvm_exp
scoped syntax "bitcast" "(" nanollvm_type ppHardSpace nanollvm_exp " to " nanollvm_type ")" : nanollvm_exp
scoped syntax "add" "(" nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_type ppHardSpace nanollvm_exp ")" : nanollvm_exp
scoped syntax "sub" "(" nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_type ppHardSpace nanollvm_exp ")" : nanollvm_exp

private def mkPairTyLlvmExp : MetaM Expr :=
  mkAppM ``Prod #[mkConst ``LlvmType, mkConst ``Exp]

mutual
partial def elabNanoLlvmTypedExp : Syntax → TermElabM Expr
  | `(nanollvm_typed_exp| $ty:nanollvm_type $e:nanollvm_exp) => do
    let ty ← elabNanoLlvmType ty
    let e ← elabNanoLlvmExp e
    mkAppM ``Prod.mk #[ty, e]
  | _ => throwUnsupportedSyntax

partial def elabNanoLlvmExp : Syntax → TermElabM Expr
  | `(nanollvm_exp| $id:nanollvm_identifier) => do
    let id ← elabNanoLlvmIdentifier id
    mkAppM ``Exp.identifier #[id]
  | `(nanollvm_exp| <$id:ident:int>) => do
    let e ← elabTerm id none
    let t ← whnf (← inferType e)
    if ← isDefEq t (mkConst ``Int) then
      mkAppM ``Exp.int #[e]
    else if ← isDefEq t (mkConst ``Nat) then
      mkAppM ``Exp.int #[← mkAppM ``Int.ofNat #[e]]
    else
      throwErrorAt id "Expected Int/Nat expression in LLVM expression, got type {t}"
  | `(nanollvm_exp| $id:ident) => do
    match id.getId.toString with
    | "true"  => mkAppM ``Exp.bool #[mkConst ``Bool.true]
    | "false" => mkAppM ``Exp.bool #[mkConst ``Bool.false]
    | other   => throwErrorAt id "Unknown LLVM expression keyword '{other}'"
  | `(nanollvm_exp| $n:num) => do
    let int ← mkAppM ``Int.ofNat #[mkNatLit n.getNat]
    mkAppM ``Exp.int #[int]
  | `(nanollvm_exp| -$n:num) => do
    let int ← mkIntLitExpr (-(n.getNat : Int))
    mkAppM ``Exp.int #[int]
  | `(nanollvm_exp| $s:scientific) => do
    let (m, negExp, e) := s.getScientific
    let exp10 : Int := if negExp then -(e : Int) else (e : Int)
    let exp10E ← mkIntLitExpr exp10
    mkAppM ``Exp.floatDec #[toExpr Bool.false, mkNatLit m, exp10E]
  | `(nanollvm_exp| -$s:scientific) => do
    let (m, negExp, e) := s.getScientific
    let exp10 : Int := if negExp then -(e : Int) else (e : Int)
    let exp10E ← mkIntLitExpr exp10
    mkAppM ``Exp.floatDec #[toExpr Bool.true, mkNatLit m, exp10E]
  | `(nanollvm_exp| fbits($n:num)) =>
    mkAppM ``Exp.floatBits #[mkNatLit n.getNat]
  | `(nanollvm_exp| null) => pure (mkConst ``Exp.null)
  | `(nanollvm_exp| zeroinitializer) => pure (mkConst ``Exp.zeroinitializer)
  | `(nanollvm_exp| undef) => pure (mkConst ``Exp.undef)
  | `(nanollvm_exp| poison) => pure (mkConst ``Exp.poison)
  | `(nanollvm_exp| [ $elems:nanollvm_typed_exp,* ]) => do
    let lst ← mkListLit (← mkPairTyLlvmExp) (← elems.getElems.toList.mapM (fun x => elabNanoLlvmTypedExp x.raw))
    mkAppM ``Exp.array #[lst]
  | `(nanollvm_exp| { $elems:nanollvm_typed_exp,* }) => do
    let lst ← mkListLit (← mkPairTyLlvmExp) (← elems.getElems.toList.mapM (fun x => elabNanoLlvmTypedExp x.raw))
    mkAppM ``Exp.struct #[toExpr Bool.false, lst]
  | `(nanollvm_exp| <{ $elems:nanollvm_typed_exp,* }>) => do
    let lst ← mkListLit (← mkPairTyLlvmExp) (← elems.getElems.toList.mapM (fun x => elabNanoLlvmTypedExp x.raw))
    mkAppM ``Exp.struct #[toExpr Bool.true, lst]
  | `(nanollvm_exp| < $elems:nanollvm_typed_exp,* >) => do
    let lst ← mkListLit (← mkPairTyLlvmExp) (← elems.getElems.toList.mapM (fun x => elabNanoLlvmTypedExp x.raw))
    mkAppM ``Exp.vector #[lst]
  | `(nanollvm_exp| splat ($te:nanollvm_typed_exp)) => do
    let e ← elabNanoLlvmTypedExp te
    mkAppM ``Exp.splat #[e]
  | `(nanollvm_exp| getelementptr $[inbounds%$ib]? ($baseTy:nanollvm_type, $ptr:nanollvm_typed_exp $[, $idxs:nanollvm_typed_exp]*)) => do
    let fl : GEPFlags := if ib.isSome then GEPFlags.mkInbounds else GEPFlags.none
    let flE ← mkAppM ``GEPFlags.mk #[toExpr fl.inbounds, toExpr fl.nusw, toExpr fl.nuw]
    let idxList ← mkListLit (← mkPairTyLlvmExp) (← idxs.toList.mapM (fun x => elabNanoLlvmTypedExp x.raw))
    mkAppM ``Exp.gepConst #[flE, ← elabNanoLlvmType baseTy, ← elabNanoLlvmTypedExp ptr, idxList]
  | `(nanollvm_exp| ptrtoint ($fTy:nanollvm_type $v:nanollvm_exp to $tTy:nanollvm_type)) => do
    mkAppM ``Exp.convConst #[mkConst ``ConversionOp.ptrtoint, ← elabNanoLlvmType fTy, ← elabNanoLlvmExp v, ← elabNanoLlvmType tTy]
  | `(nanollvm_exp| ptrtoaddr ($fTy:nanollvm_type $v:nanollvm_exp to $tTy:nanollvm_type)) => do
    mkAppM ``Exp.convConst #[mkConst ``ConversionOp.ptrtoaddr, ← elabNanoLlvmType fTy, ← elabNanoLlvmExp v, ← elabNanoLlvmType tTy]
  | `(nanollvm_exp| inttoptr ($fTy:nanollvm_type $v:nanollvm_exp to $tTy:nanollvm_type)) => do
    mkAppM ``Exp.convConst #[mkConst ``ConversionOp.inttoptr, ← elabNanoLlvmType fTy, ← elabNanoLlvmExp v, ← elabNanoLlvmType tTy]
  | `(nanollvm_exp| bitcast ($fTy:nanollvm_type $v:nanollvm_exp to $tTy:nanollvm_type)) => do
    mkAppM ``Exp.convConst #[mkConst ``ConversionOp.bitcast, ← elabNanoLlvmType fTy, ← elabNanoLlvmExp v, ← elabNanoLlvmType tTy]
  | `(nanollvm_exp| add ($ty:nanollvm_type $v1:nanollvm_exp, $_ty2:nanollvm_type $v2:nanollvm_exp)) => do
    let op ← mkAppM ``IntBinaryOp.add #[toExpr Bool.false, toExpr Bool.false]
    mkAppM ``Exp.binConst #[op, ← elabNanoLlvmType ty, ← elabNanoLlvmExp v1, ← elabNanoLlvmExp v2]
  | `(nanollvm_exp| sub ($ty:nanollvm_type $v1:nanollvm_exp, $_ty2:nanollvm_type $v2:nanollvm_exp)) => do
    let op ← mkAppM ``IntBinaryOp.sub #[toExpr Bool.false, toExpr Bool.false]
    mkAppM ``Exp.binConst #[op, ← elabNanoLlvmType ty, ← elabNanoLlvmExp v1, ← elabNanoLlvmExp v2]
  | _ => throwUnsupportedSyntax
end

elab "[llvm-exp|" p:nanollvm_exp "]" : term => elabNanoLlvmExp p

/-! ### Fast-Math Flags & Predicates -/

declare_syntax_cat nanollvm_fmf_flag
scoped syntax "fast" : nanollvm_fmf_flag
scoped syntax "nnan" : nanollvm_fmf_flag
scoped syntax "ninf" : nanollvm_fmf_flag
scoped syntax "nsz" : nanollvm_fmf_flag
scoped syntax "arcp" : nanollvm_fmf_flag
scoped syntax "contract" : nanollvm_fmf_flag
scoped syntax "afn" : nanollvm_fmf_flag
scoped syntax "reassoc" : nanollvm_fmf_flag

def elabFastMathFlags (flags : Array (TSyntax `nanollvm_fmf_flag)) : FastMathFlags :=
  flags.foldl (init := FastMathFlags.none) fun acc stx =>
    match stx.raw[0].getAtomVal with
    | "fast"     => FastMathFlags.fast
    | "nnan"     => { acc with «nnan» := Bool.true }
    | "ninf"     => { acc with «ninf» := Bool.true }
    | "nsz"      => { acc with «nsz» := Bool.true }
    | "arcp"     => { acc with «arcp» := Bool.true }
    | "contract" => { acc with «contract» := Bool.true }
    | "afn"      => { acc with «afn» := Bool.true }
    | "reassoc"  => { acc with «reassoc» := Bool.true }
    | _          => acc

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

def elabNanoLlvmIntBinOp (stx : Syntax) : TermElabM Expr := do
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

declare_syntax_cat nanollvm_fp_bin_op
scoped syntax "fadd" nanollvm_fmf_flag* : nanollvm_fp_bin_op
scoped syntax "fsub" nanollvm_fmf_flag* : nanollvm_fp_bin_op
scoped syntax "fmul" nanollvm_fmf_flag* : nanollvm_fp_bin_op
scoped syntax "fdiv" nanollvm_fmf_flag* : nanollvm_fp_bin_op
scoped syntax "frem" nanollvm_fmf_flag* : nanollvm_fp_bin_op

def elabNanoLlvmFpBinOp (stx : Syntax) : TermElabM Expr := do
  let fmf := elabFastMathFlags (stx[1].getArgs.map fun s => ⟨s⟩)
  match stx[0].getAtomVal with
  | "fadd" => return mkApp (mkConst ``FloatBinaryOp.fadd) (toExpr fmf)
  | "fsub" => return mkApp (mkConst ``FloatBinaryOp.fsub) (toExpr fmf)
  | "fmul" => return mkApp (mkConst ``FloatBinaryOp.fmul) (toExpr fmf)
  | "fdiv" => return mkApp (mkConst ``FloatBinaryOp.fdiv) (toExpr fmf)
  | "frem" => return mkApp (mkConst ``FloatBinaryOp.frem) (toExpr fmf)
  | op     => throwErrorAt stx "unknown FloatBinaryOp opcode: {op}"

def elabICmpPred (id : TSyntax `ident) : TermElabM Expr := do
  match id.getId.toString with
  | "eq"  => pure (toExpr ICmpPred.eq)
  | "ne"  => pure (toExpr ICmpPred.ne)
  | "ugt" => pure (toExpr ICmpPred.ugt)
  | "uge" => pure (toExpr ICmpPred.uge)
  | "ult" => pure (toExpr ICmpPred.ult)
  | "ule" => pure (toExpr ICmpPred.ule)
  | "sgt" => pure (toExpr ICmpPred.sgt)
  | "sge" => pure (toExpr ICmpPred.sge)
  | "slt" => pure (toExpr ICmpPred.slt)
  | "sle" => pure (toExpr ICmpPred.sle)
  | s     => throwErrorAt id "unknown icmp predicate: {s}"

def elabFCmpPred (id : TSyntax `ident) : TermElabM Expr := do
  match id.getId.toString with
  | "false" => pure (toExpr FCmpPred.ffalse)
  | "oeq"   => pure (toExpr FCmpPred.oeq)
  | "ogt"   => pure (toExpr FCmpPred.ogt)
  | "oge"   => pure (toExpr FCmpPred.oge)
  | "olt"   => pure (toExpr FCmpPred.olt)
  | "ole"   => pure (toExpr FCmpPred.ole)
  | "one"   => pure (toExpr FCmpPred.one)
  | "ord"   => pure (toExpr FCmpPred.ord)
  | "ueq"   => pure (toExpr FCmpPred.ueq)
  | "ugt"   => pure (toExpr FCmpPred.ugt)
  | "uge"   => pure (toExpr FCmpPred.uge)
  | "ult"   => pure (toExpr FCmpPred.ult)
  | "ule"   => pure (toExpr FCmpPred.ule)
  | "une"   => pure (toExpr FCmpPred.une)
  | "uno"   => pure (toExpr FCmpPred.uno)
  | "true"  => pure (toExpr FCmpPred.ftrue)
  | s       => throwErrorAt id "unknown fcmp predicate: {s}"

declare_syntax_cat nanollvm_conversion_op
scoped syntax "trunc" " nuw "? " nsw"? : nanollvm_conversion_op
scoped syntax "zext" " nneg "? : nanollvm_conversion_op
scoped syntax "sext" : nanollvm_conversion_op
scoped syntax "fptrunc" nanollvm_fmf_flag* : nanollvm_conversion_op
scoped syntax "fpext" nanollvm_fmf_flag* : nanollvm_conversion_op
scoped syntax "fptoui" : nanollvm_conversion_op
scoped syntax "fptosi" : nanollvm_conversion_op
scoped syntax "uitofp" " nneg "? nanollvm_fmf_flag* : nanollvm_conversion_op
scoped syntax "sitofp" nanollvm_fmf_flag* : nanollvm_conversion_op
scoped syntax "ptrtoint" : nanollvm_conversion_op
scoped syntax "ptrtoaddr" : nanollvm_conversion_op
scoped syntax "inttoptr" : nanollvm_conversion_op
scoped syntax "bitcast" : nanollvm_conversion_op
scoped syntax "addrspacecast" : nanollvm_conversion_op

def elabNanoLlvmConversionOp (stx : Syntax) : TermElabM Expr := do
  let flag (i : Nat) : Bool := !stx[i].isNone
  match stx[0].getAtomVal with
  | "trunc"         => return mkAppN (mkConst ``ConversionOp.trunc) #[toExpr (flag 1), toExpr (flag 2)]
  | "zext"          => return mkApp  (mkConst ``ConversionOp.zext) (toExpr (flag 1))
  | "sext"          => return mkConst ``ConversionOp.sext
  | "fptrunc"       =>
      let fmf := elabFastMathFlags (stx[1].getArgs.map fun s => ⟨s⟩)
      return mkApp (mkConst ``ConversionOp.fptrunc) (toExpr fmf)
  | "fpext"         =>
      let fmf := elabFastMathFlags (stx[1].getArgs.map fun s => ⟨s⟩)
      return mkApp (mkConst ``ConversionOp.fpext) (toExpr fmf)
  | "fptoui"        => return mkConst ``ConversionOp.fptoui
  | "fptosi"        => return mkConst ``ConversionOp.fptosi
  | "uitofp"        =>
      let fmf := elabFastMathFlags (stx[2].getArgs.map fun s => ⟨s⟩)
      return mkAppN (mkConst ``ConversionOp.uitofp) #[toExpr (flag 1), toExpr fmf]
  | "sitofp"        =>
      let fmf := elabFastMathFlags (stx[1].getArgs.map fun s => ⟨s⟩)
      return mkApp (mkConst ``ConversionOp.sitofp) (toExpr fmf)
  | "ptrtoint"      => return mkConst ``ConversionOp.ptrtoint
  | "ptrtoaddr"     => return mkConst ``ConversionOp.ptrtoaddr
  | "inttoptr"      => return mkConst ``ConversionOp.inttoptr
  | "bitcast"       => return mkConst ``ConversionOp.bitcast
  | "addrspacecast" => return mkConst ``ConversionOp.addrspacecast
  | op              => throwErrorAt stx "unknown ConversionOp opcode: {op}"

elab "[llvm-conversion-op|" p:nanollvm_conversion_op "]" : term => elabNanoLlvmConversionOp p

/-! ### Instructions -/

declare_syntax_cat nanollvm_phi_incoming
scoped syntax "[" nanollvm_exp "," "%" nanollvm_rawid "]" : nanollvm_phi_incoming

declare_syntax_cat nanollvm_gep_flag
scoped syntax "inbounds" : nanollvm_gep_flag
scoped syntax "nusw" : nanollvm_gep_flag
scoped syntax "nuw" : nanollvm_gep_flag

def elabGEPFlags (flags : Array (TSyntax `nanollvm_gep_flag)) : GEPFlags :=
  flags.foldl (init := GEPFlags.none) fun acc stx =>
    match stx.raw[0].getAtomVal with
    | "inbounds" => { acc with «inbounds» := Bool.true, «nusw» := Bool.true }
    | "nusw"     => { acc with «nusw» := Bool.true }
    | "nuw"      => { acc with «nuw» := Bool.true }
    | _          => acc

declare_syntax_cat nanollvm_alloca_opt
scoped syntax "align " num : nanollvm_alloca_opt
scoped syntax "addrspace(" num ")" : nanollvm_alloca_opt
scoped syntax nanollvm_typed_exp : nanollvm_alloca_opt

declare_syntax_cat nanollvm_load_opt
scoped syntax "align " num : nanollvm_load_opt
scoped syntax "!noundef" : nanollvm_load_opt
scoped syntax "!nonnull" : nanollvm_load_opt
scoped syntax "!range(" nanollvm_signed_int ", " nanollvm_signed_int ")" : nanollvm_load_opt

declare_syntax_cat nanollvm_call_arg
scoped syntax nanollvm_type nanollvm_value_attr* ppHardSpace nanollvm_exp : nanollvm_call_arg

declare_syntax_cat nanollvm_shuffle_elem
scoped syntax nanollvm_type ppHardSpace num : nanollvm_shuffle_elem
scoped syntax nanollvm_type ppHardSpace "poison" : nanollvm_shuffle_elem

declare_syntax_cat nanollvm_instruction
scoped syntax nanollvm_int_bin_op ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_exp : nanollvm_instruction
scoped syntax "fneg" nanollvm_fmf_flag* ppHardSpace nanollvm_type ppHardSpace nanollvm_exp : nanollvm_instruction
scoped syntax nanollvm_fp_bin_op ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_exp : nanollvm_instruction
scoped syntax "icmp" " samesign "? ident ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_exp : nanollvm_instruction
scoped syntax "fcmp" nanollvm_fmf_flag* ident ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_exp : nanollvm_instruction
scoped syntax nanollvm_conversion_op ppHardSpace nanollvm_type ppHardSpace nanollvm_exp " to " nanollvm_type : nanollvm_instruction
scoped syntax "select" nanollvm_fmf_flag* ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_type ppHardSpace nanollvm_exp : nanollvm_instruction
scoped syntax "phi" nanollvm_fmf_flag* ppHardSpace nanollvm_type ppHardSpace nanollvm_phi_incoming,+ : nanollvm_instruction
scoped syntax "alloca" ppHardSpace nanollvm_type (", " nanollvm_alloca_opt)* : nanollvm_instruction
scoped syntax "load" " volatile "? ppHardSpace nanollvm_type ", " nanollvm_type ppHardSpace nanollvm_exp (", " nanollvm_load_opt)* : nanollvm_instruction
scoped syntax "store" " volatile "? ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_type ppHardSpace nanollvm_exp (", " "align " num)? : nanollvm_instruction
scoped syntax "getelementptr" nanollvm_gep_flag* ppHardSpace nanollvm_type ", " nanollvm_type ppHardSpace nanollvm_exp (", " nanollvm_typed_exp)* : nanollvm_instruction
scoped syntax "extractvalue" ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " num,+ : nanollvm_instruction
scoped syntax "insertvalue" ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_type ppHardSpace nanollvm_exp ", " num,+ : nanollvm_instruction
scoped syntax "extractelement" ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_type ppHardSpace nanollvm_exp : nanollvm_instruction
scoped syntax "insertelement" ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_type ppHardSpace nanollvm_exp : nanollvm_instruction
scoped syntax "shufflevector" ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_type ppHardSpace nanollvm_exp ", " "<" num &"x" &"i32" ">" " <" nanollvm_shuffle_elem,+ ">" : nanollvm_instruction
scoped syntax "call" nanollvm_fmf_flag* nanollvm_value_attr* ppHardSpace nanollvm_type ppHardSpace nanollvm_exp "(" nanollvm_call_arg,* ")" : nanollvm_instruction
scoped syntax "freeze" ppHardSpace nanollvm_type ppHardSpace nanollvm_exp : nanollvm_instruction

private def mkOptionExpr (ty : Expr) : Option Expr → MetaM Expr
  | none => mkAppOptM ``Option.none #[ty]
  | some e => mkAppOptM ``Option.some #[ty, e]

def elabNanoLlvmInstruction : Syntax → TermElabM Expr
  | `(nanollvm_instruction| $op:nanollvm_int_bin_op $ty:nanollvm_type $op1:nanollvm_exp, $op2:nanollvm_exp) => do
    mkAppM ``Instruction.intBinaryOp #[← elabNanoLlvmIntBinOp op, ← elabNanoLlvmType ty, ← elabNanoLlvmExp op1, ← elabNanoLlvmExp op2]
  | `(nanollvm_instruction| fneg $flags:nanollvm_fmf_flag* $ty:nanollvm_type $v:nanollvm_exp) => do
    let op := mkApp (mkConst ``FloatUnaryOp.fneg) (toExpr (elabFastMathFlags flags))
    mkAppM ``Instruction.floatUnaryOp #[op, ← elabNanoLlvmType ty, ← elabNanoLlvmExp v]
  | `(nanollvm_instruction| $op:nanollvm_fp_bin_op $ty:nanollvm_type $op1:nanollvm_exp, $op2:nanollvm_exp) => do
    mkAppM ``Instruction.floatBinaryOp #[← elabNanoLlvmFpBinOp op, ← elabNanoLlvmType ty, ← elabNanoLlvmExp op1, ← elabNanoLlvmExp op2]
  | `(nanollvm_instruction| icmp $[samesign%$ss]? $pred:ident $ty:nanollvm_type $op1:nanollvm_exp, $op2:nanollvm_exp) => do
    mkAppM ``Instruction.icmp #[toExpr ss.isSome, ← elabICmpPred pred, ← elabNanoLlvmType ty, ← elabNanoLlvmExp op1, ← elabNanoLlvmExp op2]
  | `(nanollvm_instruction| fcmp $flags:nanollvm_fmf_flag* $pred:ident $ty:nanollvm_type $op1:nanollvm_exp, $op2:nanollvm_exp) => do
    mkAppM ``Instruction.fcmp #[toExpr (elabFastMathFlags flags), ← elabFCmpPred pred, ← elabNanoLlvmType ty, ← elabNanoLlvmExp op1, ← elabNanoLlvmExp op2]
  | `(nanollvm_instruction| $op:nanollvm_conversion_op $fromTy:nanollvm_type $v:nanollvm_exp to $toTy:nanollvm_type) => do
    mkAppM ``Instruction.conversionOp #[← elabNanoLlvmConversionOp op, ← elabNanoLlvmType fromTy, ← elabNanoLlvmExp v, ← elabNanoLlvmType toTy]
  | `(nanollvm_instruction| select $flags:nanollvm_fmf_flag* $cTy:nanollvm_type $c:nanollvm_exp, $vTy:nanollvm_type $tv:nanollvm_exp, $_fvTy:nanollvm_type $fv:nanollvm_exp) => do
    mkAppM ``Instruction.select #[toExpr (elabFastMathFlags flags), ← elabNanoLlvmType cTy, ← elabNanoLlvmExp c, ← elabNanoLlvmType vTy, ← elabNanoLlvmExp tv, ← elabNanoLlvmExp fv]
  | `(nanollvm_instruction| phi $flags:nanollvm_fmf_flag* $ty:nanollvm_type $incs:nanollvm_phi_incoming,*) => do
    let pairTy ← mkAppM ``Prod #[mkConst ``Exp, mkConst ``RawId]
    let incExprs ← incs.getElems.toList.mapM fun inc =>
      match inc.raw with
      | `(nanollvm_phi_incoming| [ $e:nanollvm_exp, %$lbl:nanollvm_rawid ]) => do
        mkAppM ``Prod.mk #[← elabNanoLlvmExp e, ← elabNanoLlvmRawId lbl]
      | _ => throwUnsupportedSyntax
    let lst ← mkListLit pairTy incExprs
    mkAppM ``Instruction.phi #[← elabNanoLlvmType ty, toExpr (elabFastMathFlags flags), lst]
  | `(nanollvm_instruction| alloca $ty:nanollvm_type $[, $opts:nanollvm_alloca_opt]*) => do
    let tyE ← elabNanoLlvmType ty
    let mut numElOpt : Option Expr := none
    let mut alignOptVal : Option Expr := none
    let mut asVal : Nat := 0
    for opt in opts do
      match opt.raw with
      | `(nanollvm_alloca_opt| align $al:num) => alignOptVal := some (mkNatLit al.getNat)
      | `(nanollvm_alloca_opt| addrspace($as:num)) => asVal := as.getNat
      | `(nanollvm_alloca_opt| $te:nanollvm_typed_exp) => numElOpt := some (← elabNanoLlvmTypedExp te)
      | _ => throwUnsupportedSyntax
    let numElE ← mkOptionExpr (← mkPairTyLlvmExp) numElOpt
    let alignOpt ← mkOptionExpr (mkConst ``Nat) alignOptVal
    mkAppM ``Instruction.alloca #[tyE, numElE, alignOpt, mkNatLit asVal]
  | `(nanollvm_instruction| load $[volatile%$vol]? $ty:nanollvm_type, $pTy:nanollvm_type $ptrExp:nanollvm_exp $[, $opts:nanollvm_load_opt]*) => do
    let mut alignOptVal : Option Expr := none
    let mut hasNoundef : Bool := Bool.false
    let mut mdAttrs : Array Expr := #[]
    for opt in opts do
      match opt.raw with
      | `(nanollvm_load_opt| align $al:num) => alignOptVal := some (mkNatLit al.getNat)
      | `(nanollvm_load_opt| !noundef) => hasNoundef := Bool.true
      | `(nanollvm_load_opt| !nonnull) => mdAttrs := mdAttrs.push (mkConst ``ValueAttr.nonnull)
      | `(nanollvm_load_opt| !range($lo:nanollvm_signed_int, $hi:nanollvm_signed_int)) => do
          let loE ← elabSignedInt lo
          let hiE ← elabSignedInt hi
          mdAttrs := mdAttrs.push (← mkAppM ``ValueAttr.range #[loE, hiE])
      | _ => throwUnsupportedSyntax
    let alignOpt ← mkOptionExpr (mkConst ``Nat) alignOptVal
    let mdList ← mkListLit (mkConst ``ValueAttr) mdAttrs.toList
    mkAppM ``Instruction.load #[← elabNanoLlvmType ty, ← elabNanoLlvmType pTy, ← elabNanoLlvmExp ptrExp, alignOpt, toExpr vol.isSome, toExpr hasNoundef, mdList]
  | `(nanollvm_instruction| store $[volatile%$vol]? $vTy:nanollvm_type $v:nanollvm_exp, $pTy:nanollvm_type $ptrExp:nanollvm_exp $[, align $al:num]?) => do
    let alignOpt ← mkOptionExpr (mkConst ``Nat) (al.map fun a => mkNatLit a.getNat)
    mkAppM ``Instruction.store #[← elabNanoLlvmType vTy, ← elabNanoLlvmExp v, ← elabNanoLlvmType pTy, ← elabNanoLlvmExp ptrExp, alignOpt, toExpr vol.isSome]
  | `(nanollvm_instruction| getelementptr $flags:nanollvm_gep_flag* $baseTy:nanollvm_type, $pTy:nanollvm_type $ptrExp:nanollvm_exp $[, $idxs:nanollvm_typed_exp]*) => do
    let idxList ← mkListLit (← mkPairTyLlvmExp) (← idxs.toList.mapM (fun x => elabNanoLlvmTypedExp x.raw))
    mkAppM ``Instruction.getelementptr #[toExpr (elabGEPFlags flags), ← elabNanoLlvmType baseTy, ← elabNanoLlvmType pTy, ← elabNanoLlvmExp ptrExp, idxList]
  | `(nanollvm_instruction| extractvalue $aggTy:nanollvm_type $agg:nanollvm_exp, $idxs:num,*) => do
    let idxList ← mkListLit (mkConst ``Nat) (idxs.getElems.toList.map fun n => mkNatLit n.getNat)
    mkAppM ``Instruction.extractvalue #[← elabNanoLlvmType aggTy, ← elabNanoLlvmExp agg, idxList]
  | `(nanollvm_instruction| insertvalue $aggTy:nanollvm_type $agg:nanollvm_exp, $valTy:nanollvm_type $val:nanollvm_exp, $idxs:num,*) => do
    let idxList ← mkListLit (mkConst ``Nat) (idxs.getElems.toList.map fun n => mkNatLit n.getNat)
    mkAppM ``Instruction.insertvalue #[← elabNanoLlvmType aggTy, ← elabNanoLlvmExp agg, ← elabNanoLlvmType valTy, ← elabNanoLlvmExp val, idxList]
  | `(nanollvm_instruction| extractelement $vecTy:nanollvm_type $vec:nanollvm_exp, $idxTy:nanollvm_type $idx:nanollvm_exp) => do
    mkAppM ``Instruction.extractelement #[← elabNanoLlvmType vecTy, ← elabNanoLlvmExp vec, ← elabNanoLlvmType idxTy, ← elabNanoLlvmExp idx]
  | `(nanollvm_instruction| insertelement $vecTy:nanollvm_type $vec:nanollvm_exp, $valTy:nanollvm_type $val:nanollvm_exp, $idxTy:nanollvm_type $idx:nanollvm_exp) => do
    mkAppM ``Instruction.insertelement #[← elabNanoLlvmType vecTy, ← elabNanoLlvmExp vec, ← elabNanoLlvmType valTy, ← elabNanoLlvmExp val, ← elabNanoLlvmType idxTy, ← elabNanoLlvmExp idx]
  | `(nanollvm_instruction| shufflevector $vecTy:nanollvm_type $v1:nanollvm_exp, $_vecTy2:nanollvm_type $v2:nanollvm_exp, < $_mLen:num x i32 > < $mask:nanollvm_shuffle_elem,* >) => do
    let optNatTy ← mkAppM ``Option #[mkConst ``Nat]
    let maskElems ← mask.getElems.toList.mapM fun el =>
      match el.raw with
      | `(nanollvm_shuffle_elem| $_t:nanollvm_type $n:num) => mkOptionExpr (mkConst ``Nat) (some (mkNatLit n.getNat))
      | `(nanollvm_shuffle_elem| $_t:nanollvm_type poison) => mkOptionExpr (mkConst ``Nat) none
      | _ => throwUnsupportedSyntax
    let maskList ← mkListLit optNatTy maskElems
    mkAppM ``Instruction.shufflevector #[← elabNanoLlvmType vecTy, ← elabNanoLlvmExp v1, ← elabNanoLlvmExp v2, maskList]
  | `(nanollvm_instruction| call $flags:nanollvm_fmf_flag* $retAttrs:nanollvm_value_attr* $retTy:nanollvm_type $callee:nanollvm_exp ( $args:nanollvm_call_arg,* )) => do
    let attrListT ← mkAppM ``List #[mkConst ``ValueAttr]
    let argInnerT ← mkAppM ``Prod #[mkConst ``Exp, attrListT]
    let argTupleT ← mkAppM ``Prod #[mkConst ``LlvmType, argInnerT]
    let argExprs ← args.getElems.toList.mapM fun a =>
      match a.raw with
      | `(nanollvm_call_arg| $t:nanollvm_type $attrs:nanollvm_value_attr* $e:nanollvm_exp) => do
        let inner ← mkAppM ``Prod.mk #[← elabNanoLlvmExp e, ← elabValueAttrList attrs]
        mkAppM ``Prod.mk #[← elabNanoLlvmType t, inner]
      | _ => throwUnsupportedSyntax
    let argList ← mkListLit argTupleT argExprs
    mkAppM ``Instruction.call #[← elabNanoLlvmRetType retTy, toExpr (elabFastMathFlags flags), ← elabNanoLlvmExp callee, argList, ← elabValueAttrList retAttrs]
  | `(nanollvm_instruction| freeze $ty:nanollvm_type $v:nanollvm_exp) => do
    let tv ← mkAppM ``Prod.mk #[← elabNanoLlvmType ty, ← elabNanoLlvmExp v]
    mkAppM ``Instruction.freeze #[tv]
  | _ => throwUnsupportedSyntax

elab "[llvm-instruction|" p:nanollvm_instruction "]" : term => elabNanoLlvmInstruction p

/-! ### Terminators -/

declare_syntax_cat nanollvm_switch_case
scoped syntax nanollvm_type ppHardSpace nanollvm_signed_int ", " "label " "%" nanollvm_rawid : nanollvm_switch_case

declare_syntax_cat nanollvm_terminator
scoped syntax "ret " "void" : nanollvm_terminator
scoped syntax "ret " nanollvm_type ppHardSpace nanollvm_exp : nanollvm_terminator
scoped syntax "br " "label " "%" nanollvm_rawid : nanollvm_terminator
scoped syntax "br " &"i1" ppHardSpace nanollvm_exp ", " "label " "%" nanollvm_rawid ", " "label " "%" nanollvm_rawid : nanollvm_terminator
scoped syntax "switch " nanollvm_type ppHardSpace nanollvm_exp ", " "label " "%" nanollvm_rawid " [" nanollvm_switch_case* "]" : nanollvm_terminator
scoped syntax "unreachable" : nanollvm_terminator

def elabNanoLlvmTerminator : Syntax → TermElabM Expr
  | `(nanollvm_terminator| ret void) => pure (mkConst ``Terminator.retVoid)
  | `(nanollvm_terminator| ret $ty:nanollvm_type $e:nanollvm_exp) => do
    let te ← mkAppM ``Prod.mk #[← elabNanoLlvmType ty, ← elabNanoLlvmExp e]
    mkAppM ``Terminator.ret #[te]
  | `(nanollvm_terminator| br label %$dest:nanollvm_rawid) => do
    mkAppM ``Terminator.br #[← elabNanoLlvmRawId dest]
  | `(nanollvm_terminator| br i1 $cond:nanollvm_exp, label %$tDest:nanollvm_rawid, label %$fDest:nanollvm_rawid) => do
    mkAppM ``Terminator.condBr #[← elabNanoLlvmExp cond, ← elabNanoLlvmRawId tDest, ← elabNanoLlvmRawId fDest]
  | `(nanollvm_terminator| switch $ty:nanollvm_type $cond:nanollvm_exp, label %$defDest:nanollvm_rawid [ $cases:nanollvm_switch_case* ]) => do
    let pairTy ← mkAppM ``Prod #[mkConst ``Int, mkConst ``RawId]
    let caseExprs ← cases.toList.mapM fun c =>
      match c.raw with
      | `(nanollvm_switch_case| $_t:nanollvm_type $v:nanollvm_signed_int, label %$lbl:nanollvm_rawid) => do
        mkAppM ``Prod.mk #[← elabSignedInt v, ← elabNanoLlvmRawId lbl]
      | _ => throwUnsupportedSyntax
    let caseList ← mkListLit pairTy caseExprs
    mkAppM ``Terminator.switch #[← elabNanoLlvmType ty, ← elabNanoLlvmExp cond, ← elabNanoLlvmRawId defDest, caseList]
  | `(nanollvm_terminator| unreachable) => pure (mkConst ``Terminator.unreachable)
  | _ => throwUnsupportedSyntax

elab "[llvm-terminator|" p:nanollvm_terminator "]" : term => elabNanoLlvmTerminator p

/-! ### Declarations, Blocks, Definitions, Globals, Modules -/

declare_syntax_cat nanollvm_decl_arg
scoped syntax nanollvm_type nanollvm_value_attr* : nanollvm_decl_arg
scoped syntax "..." : nanollvm_decl_arg

declare_syntax_cat nanollvm_declaration
scoped syntax "declare " nanollvm_value_attr* nanollvm_type ppHardSpace "@" nanollvm_rawid "(" nanollvm_decl_arg,* ")" : nanollvm_declaration

def elabNanoLlvmDeclaration : Syntax → TermElabM Expr
  | `(nanollvm_declaration| declare $retAttrs:nanollvm_value_attr* $retTy:nanollvm_type @$id:nanollvm_rawid($params:nanollvm_decl_arg,*)) => do
    let idE ← elabNanoLlvmRawId id
    let retTyE ← elabNanoLlvmRetType retTy
    let mut argTys : Array Expr := #[]
    let mut argAttrs : Array Expr := #[]
    let mut isVarArg := false
    for p in params.getElems do
      if isVarArg then throwErrorAt p "Vararg '...' must be the last parameter"
      match p.raw with
      | `(nanollvm_decl_arg| ...) => isVarArg := true
      | `(nanollvm_decl_arg| $ty:nanollvm_type $attrs:nanollvm_value_attr*) =>
        argTys := argTys.push (← elabNanoLlvmType ty)
        argAttrs := argAttrs.push (← elabValueAttrList attrs)
      | _ => throwUnsupportedSyntax
    let argList ← mkListLit (mkConst ``LlvmType) argTys.toList
    let attrListT ← mkAppM ``List #[mkConst ``ValueAttr]
    let argAttrsList ← mkListLit attrListT argAttrs.toList
    let fnTy ← mkAppM ``LlvmType.function #[retTyE, argList, toExpr isVarArg]
    mkAppM ``Declaration.mk #[idE, fnTy, argAttrsList, ← elabValueAttrList retAttrs]
  | _ => throwUnsupportedSyntax

elab "[llvm-declaration|" p:nanollvm_declaration "]" : term => elabNanoLlvmDeclaration p

declare_syntax_cat nanollvm_codeline
scoped syntax "%" nanollvm_rawid " = " nanollvm_instruction : nanollvm_codeline
scoped syntax nanollvm_instruction : nanollvm_codeline

def elabNanoLlvmCodeline (lineno : Nat) : Syntax → TermElabM Expr
  | `(nanollvm_codeline| %$id:nanollvm_rawid = $instr:nanollvm_instruction) => do
    let id ← mkAppM ``InstructionId.id #[← elabNanoLlvmRawId id]
    mkAppM ``Prod.mk #[id, ← elabNanoLlvmInstruction instr]
  | `(nanollvm_codeline| $instr:nanollvm_instruction) => do
    let id ← mkAppM ``InstructionId.void #[mkNatLit lineno]
    mkAppM ``Prod.mk #[id, ← elabNanoLlvmInstruction instr]
  | _ => throwUnsupportedSyntax

elab "[llvm-codeline|" p:nanollvm_codeline "]" : term => elabNanoLlvmCodeline 1 p

declare_syntax_cat nanollvm_code
scoped syntax ppDedent(ppLine nanollvm_codeline)* : nanollvm_code

def elabNanoLlvmCode (lineno : Nat) : Syntax → TermElabM (Expr × Nat)
  | `(nanollvm_code| $lines:nanollvm_codeline*) => do
    let ty ← mkAppM ``Prod #[mkConst ``InstructionId, mkConst ``Instruction]
    let mut elabed : Array Expr := #[]
    for offset in [:lines.size] do
      elabed := elabed.push (← elabNanoLlvmCodeline (lineno + offset) lines[offset]!)
    pure (← mkListLit ty elabed.toList, elabed.size)
  | _ => throwUnsupportedSyntax

elab "[llvm-code|" p:nanollvm_code "]" : term => do
  pure (← elabNanoLlvmCode 1 p).1

declare_syntax_cat nanollvm_block
scoped syntax nanollvm_rawid ": " ppIndent(nanollvm_code ppLine nanollvm_terminator) : nanollvm_block

def elabNanoLlvmBlock (lineno : Nat) : Syntax → TermElabM (Expr × Nat)
  | `(nanollvm_block| $id:nanollvm_rawid:
  $code:nanollvm_code $term:nanollvm_terminator) => do
    let id ← elabNanoLlvmRawId id
    let (code, nLines) ← elabNanoLlvmCode lineno code
    let term ← elabNanoLlvmTerminator term
    let termId ← mkAppM ``InstructionId.void #[mkNatLit (lineno + nLines)]
    let termPair ← mkAppM ``Prod.mk #[termId, term]
    pure (← mkAppM ``Block.mk #[id, code, termPair], nLines + 1)
  | _ => throwUnsupportedSyntax

elab "[llvm-block|" p:nanollvm_block "]" : term => do
  pure (← elabNanoLlvmBlock 1 p).1

declare_syntax_cat nanollvm_arg
scoped syntax nanollvm_type nanollvm_value_attr* " %" nanollvm_rawid : nanollvm_arg
scoped syntax "..." : nanollvm_arg

elab "[llvm-arg|" p:nanollvm_arg "]" : term => do
  match p.raw with
  | `(nanollvm_arg| $ty:nanollvm_type $_attrs:nanollvm_value_attr* %$id:nanollvm_rawid) =>
    mkAppM ``Prod.mk #[← elabNanoLlvmType ty, ← elabNanoLlvmRawId id]
  | _ => throwUnsupportedSyntax

declare_syntax_cat nanollvm_definition
scoped syntax "define " nanollvm_value_attr* nanollvm_type ppHardSpace "@" nanollvm_rawid "(" nanollvm_arg,* ") "
       ppDedent(ppDedent("{" (ppLine nanollvm_block)+ ppLine "}")) : nanollvm_definition

def elabNanoLlvmDefinition : Syntax → TermElabM Expr
  | `(nanollvm_definition| define $retAttrs:nanollvm_value_attr* $retTy:nanollvm_type @$id:nanollvm_rawid($args:nanollvm_arg,*) {
      $blocks:nanollvm_block*
    }) => do
    let idE ← elabNanoLlvmRawId id
    let retTyE ← elabNanoLlvmRetType retTy
    let mut argTys : Array Expr := #[]
    let mut argAttrs : Array Expr := #[]
    let mut argNames : Array Expr := #[]
    let mut isVarArg := false
    for a in args.getElems do
      if isVarArg then throwErrorAt a "Vararg '...' must be the last parameter"
      match a.raw with
      | `(nanollvm_arg| ...) => isVarArg := true
      | `(nanollvm_arg| $ty:nanollvm_type $attrs:nanollvm_value_attr* %$nm:nanollvm_rawid) =>
        argTys := argTys.push (← elabNanoLlvmType ty)
        argAttrs := argAttrs.push (← elabValueAttrList attrs)
        argNames := argNames.push (← elabNanoLlvmRawId nm)
      | _ => throwUnsupportedSyntax
    let argList ← mkListLit (mkConst ``LlvmType) argTys.toList
    let attrListT ← mkAppM ``List #[mkConst ``ValueAttr]
    let argAttrsList ← mkListLit attrListT argAttrs.toList
    let argNameList ← mkListLit (mkConst ``RawId) argNames.toList
    let fnTy ← mkAppM ``LlvmType.function #[retTyE, argList, toExpr isVarArg]
    let mut curLine := 1
    let mut blockExprs : Array Expr := #[]
    for blk in blocks do
      let (bE, nLines) ← elabNanoLlvmBlock curLine blk
      curLine := curLine + nLines
      blockExprs := blockExprs.push bE
    let blockList ← mkListLit (mkConst ``Block) blockExprs.toList
    let decl ← mkAppM ``Declaration.mk #[idE, fnTy, argAttrsList, ← elabValueAttrList retAttrs]
    mkAppM ``Definition.mk #[decl, argNameList, blockList]
  | _ => throwUnsupportedSyntax

elab "[llvm-definition|" p:nanollvm_definition "]" : term => elabNanoLlvmDefinition p

declare_syntax_cat nanollvm_global
scoped syntax "@" nanollvm_rawid " = " ("addrspace(" num ") ")? "global " nanollvm_type (ppHardSpace nanollvm_exp)? (", " "align " num)? : nanollvm_global
scoped syntax "@" nanollvm_rawid " = " ("addrspace(" num ") ")? "constant " nanollvm_type (ppHardSpace nanollvm_exp)? (", " "align " num)? : nanollvm_global

def elabNanoLlvmGlobal : Syntax → TermElabM Expr
  | `(nanollvm_global| @$id:nanollvm_rawid = $[addrspace($as:num)]? global $ty:nanollvm_type $[$init:nanollvm_exp]? $[, align $al:num]?) => do
    let initOpt ← mkOptionExpr (mkConst ``Exp) (← init.mapM (fun e => elabNanoLlvmExp e.raw))
    let alignOpt ← mkOptionExpr (mkConst ``Nat) (al.map fun a => mkNatLit a.getNat)
    let asNat := (as.map (·.getNat)).getD 0
    mkAppM ``GlobalVariable.mk #[← elabNanoLlvmRawId id, ← elabNanoLlvmType ty, toExpr Bool.false, initOpt, alignOpt, mkNatLit asNat]
  | `(nanollvm_global| @$id:nanollvm_rawid = $[addrspace($as:num)]? constant $ty:nanollvm_type $[$init:nanollvm_exp]? $[, align $al:num]?) => do
    let initOpt ← mkOptionExpr (mkConst ``Exp) (← init.mapM (fun e => elabNanoLlvmExp e.raw))
    let alignOpt ← mkOptionExpr (mkConst ``Nat) (al.map fun a => mkNatLit a.getNat)
    let asNat := (as.map (·.getNat)).getD 0
    mkAppM ``GlobalVariable.mk #[← elabNanoLlvmRawId id, ← elabNanoLlvmType ty, toExpr Bool.true, initOpt, alignOpt, mkNatLit asNat]
  | _ => throwUnsupportedSyntax

elab "[llvm-global|" p:nanollvm_global "]" : term => elabNanoLlvmGlobal p

declare_syntax_cat nanollvm_typedef
scoped syntax "%" nanollvm_rawid " = " "type " nanollvm_type : nanollvm_typedef

declare_syntax_cat nanollvm_entity
scoped syntax nanollvm_typedef : nanollvm_entity
scoped syntax nanollvm_global : nanollvm_entity
scoped syntax nanollvm_declaration : nanollvm_entity
scoped syntax nanollvm_definition : nanollvm_entity

def elabNanoLlvmEntity : Syntax → TermElabM Expr
  | `(nanollvm_entity| $td:nanollvm_typedef) =>
    match td.raw with
    | `(nanollvm_typedef| %$nm:nanollvm_rawid = type $ty:nanollvm_type) => do
      mkAppM ``TopLevelEntity.typeDef #[← elabNanoLlvmRawId nm, ← elabNanoLlvmType ty]
    | _ => throwUnsupportedSyntax
  | `(nanollvm_entity| $gv:nanollvm_global) => do mkAppM ``TopLevelEntity.global #[← elabNanoLlvmGlobal gv]
  | `(nanollvm_entity| $decl:nanollvm_declaration) => do mkAppM ``TopLevelEntity.declaration #[← elabNanoLlvmDeclaration decl]
  | `(nanollvm_entity| $defn:nanollvm_definition) => do mkAppM ``TopLevelEntity.definition #[← elabNanoLlvmDefinition defn]
  | _ => throwUnsupportedSyntax

elab "[llvm-entity|" p:nanollvm_entity "]" : term => elabNanoLlvmEntity p

declare_syntax_cat nanollvm
scoped syntax ppDedent(nanollvm_entity ppLine)* : nanollvm

def elabNanoLlvm : Syntax → TermElabM Expr
  | `(nanollvm| $entity:nanollvm_entity*) => do
    let entities ← mkListLit (mkConst ``TopLevelEntity) (← entity.toList.mapM (fun e => elabNanoLlvmEntity e.raw))
    mkAppM ``TopLevel.mk #[entities]
  | _ => throwUnsupportedSyntax

elab "[llvm|" ppLine p:nanollvm "]" : term => elabNanoLlvm p

end LeanNanoLlvm.AST.Syntax
