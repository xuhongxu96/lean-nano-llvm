import Lean
import LeanNanoLlvm.AST.AST

namespace LeanNanoLlvm.AST.Syntax

open Lean Lean.Meta Lean.Elab Lean.Elab.Term
open LeanNanoLlvm.AST
open scoped LeanNanoLlvm.AST.Syntax

deriving instance Lean.ToExpr for DenormalModeKind
deriving instance Lean.ToExpr for DenormalMode
deriving instance Lean.ToExpr for RawId
deriving instance Lean.ToExpr for Identifier
deriving instance Lean.ToExpr for InstructionId
deriving instance Lean.ToExpr for FloatType
deriving instance Lean.ToExpr for FastMathFlags
deriving instance Lean.ToExpr for ICmpPred
deriving instance Lean.ToExpr for FCmpPred
deriving instance Lean.ToExpr for GEPFlags
deriving instance Lean.ToExpr for IntBinaryOp
deriving instance Lean.ToExpr for FloatUnaryOp
deriving instance Lean.ToExpr for FloatBinaryOp
deriving instance Lean.ToExpr for ConversionOp

mutual
  private def llvmRetTypeToExpr : LlvmRetType → Expr
    | .void => mkConst ``LlvmRetType.void
    | .ret ty => mkApp (mkConst ``LlvmRetType.ret) (llvmTypeToExpr ty)

  private def llvmTypeToExpr : LlvmType → Expr
    | .int w => mkApp (mkConst ``LlvmType.int) (toExpr w)
    | .byte w => mkApp (mkConst ``LlvmType.byte) (toExpr w)
    | .float ft => mkApp (mkConst ``LlvmType.float) (toExpr ft)
    | .ptr as => mkApp (mkConst ``LlvmType.ptr) (toExpr as)
    | .vector n elem => mkApp2 (mkConst ``LlvmType.vector) (toExpr n) (llvmTypeToExpr elem)
    | .array n elem => mkApp2 (mkConst ``LlvmType.array) (toExpr n) (llvmTypeToExpr elem)
    | .struct packed fields =>
      mkApp2 (mkConst ``LlvmType.struct) (toExpr packed) (llvmTypeListToExpr fields)
    | .named nm => mkApp (mkConst ``LlvmType.named) (toExpr nm)
    | .function ret args isVarArg =>
      mkApp3 (mkConst ``LlvmType.function) (llvmRetTypeToExpr ret) (llvmTypeListToExpr args) (toExpr isVarArg)

  private def llvmTypeListToExpr : List LlvmType → Expr
    | [] => mkApp (mkConst ``List.nil [levelZero]) (mkConst ``LlvmType)
    | t :: ts => mkApp3 (mkConst ``List.cons [levelZero]) (mkConst ``LlvmType) (llvmTypeToExpr t) (llvmTypeListToExpr ts)
end

instance : ToExpr LlvmRetType where
  toExpr := llvmRetTypeToExpr
  toTypeExpr := mkConst ``LlvmRetType

instance : ToExpr LlvmType where
  toExpr := llvmTypeToExpr
  toTypeExpr := mkConst ``LlvmType

deriving instance Lean.ToExpr for ValueAttr
deriving instance Lean.ToExpr for CallSiteInfo

private def mkPairExpr (α β : Expr) (a b : Expr) : Expr :=
  mkApp4 (mkConst ``Prod.mk [levelZero, levelZero]) α β a b

private def mkPairTyExpr (α β : Expr) : Expr :=
  mkApp2 (mkConst ``Prod [levelZero, levelZero]) α β

mutual
  private def expToExpr : Exp → Expr
    | .identifier id => mkApp (mkConst ``Exp.identifier) (toExpr id)
    | .bool b => mkApp (mkConst ``Exp.bool) (toExpr b)
    | .int x => mkApp (mkConst ``Exp.int) (toExpr x)
    | .floatBits b => mkApp (mkConst ``Exp.floatBits) (toExpr b)
    | .floatDec neg m e => mkApp3 (mkConst ``Exp.floatDec) (toExpr neg) (toExpr m) (toExpr e)
    | .floatSpecial neg isInf quiet payload =>
      mkApp4 (mkConst ``Exp.floatSpecial) (toExpr neg) (toExpr isInf) (toExpr quiet) (toExpr payload)
    | .blockAddress fn blk => mkApp2 (mkConst ``Exp.blockAddress) (toExpr fn) (toExpr blk)
    | .null => mkConst ``Exp.null
    | .zeroinitializer => mkConst ``Exp.zeroinitializer
    | .undef => mkConst ``Exp.undef
    | .poison => mkConst ``Exp.poison
    | .array elems => mkApp (mkConst ``Exp.array) (expTypedListToExpr elems)
    | .struct packed fields => mkApp2 (mkConst ``Exp.struct) (toExpr packed) (expTypedListToExpr fields)
    | .vector elems => mkApp (mkConst ``Exp.vector) (expTypedListToExpr elems)
    | .splat (t, e) =>
      mkApp (mkConst ``Exp.splat) (mkPairExpr (mkConst ``LlvmType) (mkConst ``Exp) (toExpr t) (expToExpr e))
    | .gepConst flags baseTy (pTy, pExp) idxs =>
      mkApp4 (mkConst ``Exp.gepConst) (toExpr flags) (toExpr baseTy)
        (mkPairExpr (mkConst ``LlvmType) (mkConst ``Exp) (toExpr pTy) (expToExpr pExp))
        (expTypedListToExpr idxs)
    | .convConst op fromTy val toTy =>
      mkApp4 (mkConst ``Exp.convConst) (toExpr op) (toExpr fromTy) (expToExpr val) (toExpr toTy)
    | .binConst op ty v1 v2 =>
      mkApp4 (mkConst ``Exp.binConst) (toExpr op) (toExpr ty) (expToExpr v1) (expToExpr v2)
    | .insertElemConst vecTy vec elemTy elem idxTy idx =>
      mkApp6 (mkConst ``Exp.insertElemConst) (toExpr vecTy) (expToExpr vec) (toExpr elemTy) (expToExpr elem) (toExpr idxTy) (expToExpr idx)
    | .extractElemConst vecTy vec idxTy idx =>
      mkApp4 (mkConst ``Exp.extractElemConst) (toExpr vecTy) (expToExpr vec) (toExpr idxTy) (expToExpr idx)
    | .shuffleVecConst vecTy v1 v2 mask =>
      mkApp4 (mkConst ``Exp.shuffleVecConst) (toExpr vecTy) (expToExpr v1) (expToExpr v2) (toExpr mask)

  private def expTypedListToExpr : List (LlvmType × Exp) → Expr
    | [] => mkApp (mkConst ``List.nil [levelZero]) (mkPairTyExpr (mkConst ``LlvmType) (mkConst ``Exp))
    | (t, e) :: rest =>
      let pairTy := mkPairTyExpr (mkConst ``LlvmType) (mkConst ``Exp)
      let pair := mkPairExpr (mkConst ``LlvmType) (mkConst ``Exp) (toExpr t) (expToExpr e)
      mkApp3 (mkConst ``List.cons [levelZero]) pairTy pair (expTypedListToExpr rest)
end

instance : ToExpr Exp where
  toExpr := expToExpr
  toTypeExpr := mkConst ``Exp

deriving instance Lean.ToExpr for Instruction
deriving instance Lean.ToExpr for Terminator
deriving instance Lean.ToExpr for Declaration
deriving instance Lean.ToExpr for Block
deriving instance Lean.ToExpr for Definition
deriving instance Lean.ToExpr for GlobalVariable
deriving instance Lean.ToExpr for TopLevelEntity
deriving instance Lean.ToExpr for TopLevel

declare_syntax_cat nanollvm_rawid
scoped syntax ident : nanollvm_rawid
scoped syntax num : nanollvm_rawid
scoped syntax str : nanollvm_rawid

def elabNanoLlvmRawId : Syntax → TermElabM Expr
  | `(nanollvm_rawid| $s:ident) => mkAppM ``RawId.name #[mkStrLit s.getId.toString]
  | `(nanollvm_rawid| $n:num) => mkAppM ``RawId.anonymous #[mkNatLit n.getNat]
  | `(nanollvm_rawid| $s:str) => mkAppM ``RawId.name #[mkStrLit s.getString]
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
scoped syntax "b$(" term ")" : nanollvm_type
scoped syntax nanollvm_type " addrspace(" num ")" : nanollvm_type
scoped syntax "<" num ppHardSpace &"x" ppHardSpace nanollvm_type ">" : nanollvm_type
scoped syntax "[" num ppHardSpace &"x" ppHardSpace nanollvm_type "]" : nanollvm_type
scoped syntax "{" nanollvm_type,* "}" : nanollvm_type
scoped syntax "<{" nanollvm_type,* "}>" : nanollvm_type
scoped syntax "%" nanollvm_rawid : nanollvm_type
scoped syntax nanollvm_type "(" nanollvm_fn_param,* ")" : nanollvm_type

mutual
private def elabNanoLlvmTypeAux : Nat → Syntax → TermElabM Expr
  | 0, stx => throwErrorAt stx "LLVM type nesting depth exceeded"
  | fuel + 1, stx =>
    match stx with
    | `(nanollvm_type| $id:ident) => do
      let s := id.getId.toString
      match s with
      | "half"      => mkAppM ``LlvmType.float #[mkConst ``FloatType.half]
      | "bfloat"    => mkAppM ``LlvmType.float #[mkConst ``FloatType.bfloat]
      | "float"     => mkAppM ``LlvmType.float #[mkConst ``FloatType.float]
      | "double"    => mkAppM ``LlvmType.float #[mkConst ``FloatType.double]
      | "x86_fp80"  => mkAppM ``LlvmType.float #[mkConst ``FloatType.x86_fp80]
      | "fp128"     => mkAppM ``LlvmType.float #[mkConst ``FloatType.fp128]
      | "ppc_fp128" => mkAppM ``LlvmType.float #[mkConst ``FloatType.ppc_fp128]
      | "ptr"       => mkAppM ``LlvmType.ptr #[mkNatLit 0]
      | _ =>
        if s.startsWith "i" then
          let numStr := s.drop 1
          match numStr.toNat? with
          | some n => mkAppM ``LlvmType.int #[mkNatLit n]
          | none => throwErrorAt id "Invalid LLVM type: {s}"
        else if s.startsWith "b" then
          let numStr := s.drop 1
          match numStr.toNat? with
          | some n => mkAppM ``LlvmType.byte #[mkNatLit n]
          | none => throwErrorAt id "Invalid LLVM type: {s}"
        else
          throwErrorAt id "Unknown LLVM type: {s}"

    | `(nanollvm_type| i$($w:term)) => do
      let wExpr ← elabTermEnsuringType w (mkConst ``Nat)
      mkAppM ``LlvmType.int #[wExpr]

    | `(nanollvm_type| b$($w:term)) => do
      let wExpr ← elabTermEnsuringType w (mkConst ``Nat)
      mkAppM ``LlvmType.byte #[wExpr]

    | `(nanollvm_type| $base:nanollvm_type addrspace($as:num)) => do
      match base with
      | `(nanollvm_type| $id:ident) =>
        if id.getId.toString == "ptr" then
          mkAppM ``LlvmType.ptr #[mkNatLit as.getNat]
        else
          throwErrorAt base "Expected 'ptr' before addrspace(...), got {id}"
      | _ => throwErrorAt base "Expected 'ptr' before addrspace(...)"

    | `(nanollvm_type| < $n:num x $elem:nanollvm_type >) => do
      let elemTy ← elabNanoLlvmTypeAux fuel elem
      mkAppM ``LlvmType.vector #[mkNatLit n.getNat, elemTy]

    | `(nanollvm_type| [ $n:num x $elem:nanollvm_type ]) => do
      let elemTy ← elabNanoLlvmTypeAux fuel elem
      mkAppM ``LlvmType.array #[mkNatLit n.getNat, elemTy]

    | `(nanollvm_type| { $fields:nanollvm_type,* }) => do
      let fVals ← fields.getElems.mapM (fun x => elabNanoLlvmTypeAux fuel x.raw)
      let fList ← mkListLit (mkConst ``LlvmType) fVals.toList
      mkAppM ``LlvmType.struct #[toExpr Bool.false, fList]

    | `(nanollvm_type| <{ $fields:nanollvm_type,* }>) => do
      let fVals ← fields.getElems.mapM (fun x => elabNanoLlvmTypeAux fuel x.raw)
      let fList ← mkListLit (mkConst ``LlvmType) fVals.toList
      mkAppM ``LlvmType.struct #[toExpr Bool.true, fList]

    | `(nanollvm_type| %$nm:nanollvm_rawid) => do
      mkAppM ``LlvmType.named #[← elabNanoLlvmRawId nm]

    | `(nanollvm_type| $ret:nanollvm_type ( $params:nanollvm_fn_param,* )) => do
      let ret ← elabNanoLlvmRetTypeAux fuel ret
      let mut argVals : Array Expr := #[]
      let mut isVarArg := false
      for p in params.getElems do
        if isVarArg then throwErrorAt p "Vararg '...' must be the last parameter"
        match p.raw with
        | `(nanollvm_fn_param| ...) => isVarArg := true
        | `(nanollvm_fn_param| $t:nanollvm_type) => argVals := argVals.push (← elabNanoLlvmTypeAux fuel t)
        | _ => throwUnsupportedSyntax
      let argList ← mkListLit (mkConst ``LlvmType) argVals.toList
      mkAppM ``LlvmType.function #[ret, argList, toExpr isVarArg]

    | _ => throwUnsupportedSyntax

private def elabNanoLlvmRetTypeAux : Nat → Syntax → TermElabM Expr
  | 0, stx => throwErrorAt stx "LLVM return type nesting depth exceeded"
  | fuel + 1, stx =>
    match stx with
    | `(nanollvm_type| void) => pure (mkConst ``LlvmRetType.void)
    | stx => do
      let ty ← elabNanoLlvmTypeAux fuel stx
      mkAppM ``LlvmRetType.ret #[ty]
end

def elabNanoLlvmType (stx : Syntax) : TermElabM Expr := elabNanoLlvmTypeAux 1000 stx
def elabNanoLlvmRetType (stx : Syntax) : TermElabM Expr := elabNanoLlvmRetTypeAux 1000 stx

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

declare_syntax_cat nanollvm_range_pair
scoped syntax nanollvm_signed_int ", " nanollvm_signed_int : nanollvm_range_pair

declare_syntax_cat nanollvm_value_attr
scoped syntax "noundef" : nanollvm_value_attr
scoped syntax "nonnull" : nanollvm_value_attr
scoped syntax "align " num : nanollvm_value_attr
scoped syntax "dereferenceable(" num ")" : nanollvm_value_attr
scoped syntax "dereferenceable_or_null(" num ")" : nanollvm_value_attr
scoped syntax "range(" nanollvm_signed_int ", " nanollvm_signed_int ")" : nanollvm_value_attr
scoped syntax "range_list(" nanollvm_range_pair,* ")" : nanollvm_value_attr
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
  | `(nanollvm_value_attr| range_list($pairs:nanollvm_range_pair,*)) => do
      let pairTy ← mkAppM ``Prod #[mkConst ``Int, mkConst ``Int]
      let pairEs ← pairs.getElems.toList.mapM fun p =>
        match p.raw with
        | `(nanollvm_range_pair| $lo:nanollvm_signed_int, $hi:nanollvm_signed_int) => do
          mkAppM ``Prod.mk #[← elabSignedInt lo, ← elabSignedInt hi]
        | _ => throwUnsupportedSyntax
      let lst ← mkListLit pairTy pairEs
      mkAppM ``ValueAttr.rangeList #[lst]
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

/-! ### Fast-Math Flags, GEP Flags, Operators & Predicates -/

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

declare_syntax_cat nanollvm_int_bin_op
scoped syntax "add" " nuw"? " nsw"? : nanollvm_int_bin_op
scoped syntax "sub" " nuw"? " nsw"? : nanollvm_int_bin_op
scoped syntax "mul" " nuw"? " nsw"? : nanollvm_int_bin_op
scoped syntax "shl" " nuw"? " nsw"? : nanollvm_int_bin_op
scoped syntax "udiv" " exact"? : nanollvm_int_bin_op
scoped syntax "sdiv" " exact"? : nanollvm_int_bin_op
scoped syntax "lshr" " exact"? : nanollvm_int_bin_op
scoped syntax "ashr" " exact"? : nanollvm_int_bin_op
scoped syntax "urem" : nanollvm_int_bin_op
scoped syntax "srem" : nanollvm_int_bin_op
scoped syntax "and" : nanollvm_int_bin_op
scoped syntax "or" " disjoint"? : nanollvm_int_bin_op
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
scoped syntax "trunc" " nuw"? " nsw"? : nanollvm_conversion_op
scoped syntax "zext" " nneg"? : nanollvm_conversion_op
scoped syntax "sext" : nanollvm_conversion_op
scoped syntax "fptrunc" nanollvm_fmf_flag* : nanollvm_conversion_op
scoped syntax "fpext" nanollvm_fmf_flag* : nanollvm_conversion_op
scoped syntax "fptoui" : nanollvm_conversion_op
scoped syntax "fptosi" : nanollvm_conversion_op
scoped syntax "uitofp" " nneg"? nanollvm_fmf_flag* : nanollvm_conversion_op
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

declare_syntax_cat nanollvm_shuffle_elem
scoped syntax nanollvm_type ppHardSpace num : nanollvm_shuffle_elem
scoped syntax nanollvm_type ppHardSpace "poison" : nanollvm_shuffle_elem

private def mkOptionExpr (ty : Expr) : Option Expr → MetaM Expr
  | none => mkAppOptM ``Option.none #[ty]
  | some e => mkAppOptM ``Option.some #[ty, e]

private def elabShuffleMask (mask : Syntax.TSepArray `nanollvm_shuffle_elem ",") : TermElabM Expr := do
  let optNatTy ← mkAppM ``Option #[mkConst ``Nat]
  let maskElems ← mask.getElems.toList.mapM fun el =>
    match el.raw with
    | `(nanollvm_shuffle_elem| $_t:nanollvm_type $n:num) => mkOptionExpr (mkConst ``Nat) (some (mkNatLit n.getNat))
    | `(nanollvm_shuffle_elem| $_t:nanollvm_type poison) => mkOptionExpr (mkConst ``Nat) none
    | _ => throwUnsupportedSyntax
  mkListLit optNatTy maskElems

/-! ### Expressions & Constants -/

declare_syntax_cat nanollvm_exp
declare_syntax_cat nanollvm_typed_exp

scoped syntax nanollvm_type ppHardSpace nanollvm_exp : nanollvm_typed_exp

scoped syntax nanollvm_identifier : nanollvm_exp
scoped syntax "<" ident ":int>" : nanollvm_exp
scoped syntax atomic(ident notFollowedBy(":")) : nanollvm_exp
scoped syntax num : nanollvm_exp
scoped syntax "-" num : nanollvm_exp
scoped syntax scientific : nanollvm_exp
scoped syntax "-" scientific : nanollvm_exp
scoped syntax "fbits(" num ")" : nanollvm_exp
scoped syntax "fspecial(" ("+" <|> "-") ident ("(" num ")")? ")" : nanollvm_exp
scoped syntax "blockaddress(" "@" nanollvm_rawid ", " "%" nanollvm_rawid ")" : nanollvm_exp
scoped syntax "null" : nanollvm_exp
scoped syntax "zeroinitializer" : nanollvm_exp
scoped syntax "undef" : nanollvm_exp
scoped syntax "poison" : nanollvm_exp
scoped syntax "[" nanollvm_typed_exp,* "]" : nanollvm_exp
scoped syntax "{" nanollvm_typed_exp,* "}" : nanollvm_exp
scoped syntax "<{" nanollvm_typed_exp,* "}>" : nanollvm_exp
scoped syntax "<" nanollvm_typed_exp,+ ">" : nanollvm_exp
scoped syntax "splat" "(" nanollvm_typed_exp ")" : nanollvm_exp
scoped syntax "getelementptr" nanollvm_gep_flag* "(" nanollvm_type ", " nanollvm_typed_exp (", " nanollvm_typed_exp)* ")" : nanollvm_exp
scoped syntax nanollvm_conversion_op "(" nanollvm_type ppHardSpace nanollvm_exp " to " nanollvm_type ")" : nanollvm_exp
scoped syntax nanollvm_int_bin_op "(" nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_type ppHardSpace nanollvm_exp ")" : nanollvm_exp
scoped syntax "insertelement" "(" nanollvm_typed_exp ", " nanollvm_typed_exp ", " nanollvm_typed_exp ")" : nanollvm_exp
scoped syntax "extractelement" "(" nanollvm_typed_exp ", " nanollvm_typed_exp ")" : nanollvm_exp
scoped syntax "shufflevector" "(" nanollvm_typed_exp ", " nanollvm_typed_exp ", " "<" num ppHardSpace &"x" ppHardSpace &"i32" ">" " <" nanollvm_shuffle_elem,+ ">" ")" : nanollvm_exp

private def mkPairTyLlvmExp : MetaM Expr :=
  mkAppM ``Prod #[mkConst ``LlvmType, mkConst ``Exp]

mutual
private def elabNanoLlvmTypedExpAux : Nat → Syntax → TermElabM Expr
  | 0, stx => throwErrorAt stx "LLVM typed expression nesting depth exceeded"
  | fuel + 1, stx =>
    match stx with
    | `(nanollvm_typed_exp| $ty:nanollvm_type $e:nanollvm_exp) => do
      let ty ← elabNanoLlvmType ty
      let e ← elabNanoLlvmExpAux fuel e
      mkAppM ``Prod.mk #[ty, e]
    | _ => throwUnsupportedSyntax

private def elabNanoLlvmExpAux : Nat → Syntax → TermElabM Expr
  | 0, stx => throwErrorAt stx "LLVM expression nesting depth exceeded"
  | fuel + 1, stx =>
    match stx with
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
    | `(nanollvm_exp| fspecial(+ $kind:ident $[($p:num)]?)) => do
      let payload := (p.map (·.getNat)).getD 0
      match kind.getId.toString with
      | "inf"  => mkAppM ``Exp.floatSpecial #[toExpr false, toExpr true, toExpr false, mkNatLit payload]
      | "qnan" => mkAppM ``Exp.floatSpecial #[toExpr false, toExpr false, toExpr true, mkNatLit payload]
      | "snan" => mkAppM ``Exp.floatSpecial #[toExpr false, toExpr false, toExpr false, mkNatLit payload]
      | other  => throwErrorAt kind "Unknown float special kind '{other}'"
    | `(nanollvm_exp| fspecial(- $kind:ident $[($p:num)]?)) => do
      let payload := (p.map (·.getNat)).getD 0
      match kind.getId.toString with
      | "inf"  => mkAppM ``Exp.floatSpecial #[toExpr true, toExpr true, toExpr false, mkNatLit payload]
      | "qnan" => mkAppM ``Exp.floatSpecial #[toExpr true, toExpr false, toExpr true, mkNatLit payload]
      | "snan" => mkAppM ``Exp.floatSpecial #[toExpr true, toExpr false, toExpr false, mkNatLit payload]
      | other  => throwErrorAt kind "Unknown float special kind '{other}'"
    | `(nanollvm_exp| blockaddress(@$fn:nanollvm_rawid, %$blk:nanollvm_rawid)) => do
      mkAppM ``Exp.blockAddress #[← elabNanoLlvmRawId fn, ← elabNanoLlvmRawId blk]
    | `(nanollvm_exp| null) => pure (mkConst ``Exp.null)
    | `(nanollvm_exp| zeroinitializer) => pure (mkConst ``Exp.zeroinitializer)
    | `(nanollvm_exp| undef) => pure (mkConst ``Exp.undef)
    | `(nanollvm_exp| poison) => pure (mkConst ``Exp.poison)
    | `(nanollvm_exp| [ $elems:nanollvm_typed_exp,* ]) => do
      let lst ← mkListLit (← mkPairTyLlvmExp) (← elems.getElems.toList.mapM (fun x => elabNanoLlvmTypedExpAux fuel x.raw))
      mkAppM ``Exp.array #[lst]
    | `(nanollvm_exp| { $elems:nanollvm_typed_exp,* }) => do
      let lst ← mkListLit (← mkPairTyLlvmExp) (← elems.getElems.toList.mapM (fun x => elabNanoLlvmTypedExpAux fuel x.raw))
      mkAppM ``Exp.struct #[toExpr Bool.false, lst]
    | `(nanollvm_exp| <{ $elems:nanollvm_typed_exp,* }>) => do
      let lst ← mkListLit (← mkPairTyLlvmExp) (← elems.getElems.toList.mapM (fun x => elabNanoLlvmTypedExpAux fuel x.raw))
      mkAppM ``Exp.struct #[toExpr Bool.true, lst]
    | `(nanollvm_exp| < $elems:nanollvm_typed_exp,* >) => do
      let lst ← mkListLit (← mkPairTyLlvmExp) (← elems.getElems.toList.mapM (fun x => elabNanoLlvmTypedExpAux fuel x.raw))
      mkAppM ``Exp.vector #[lst]
    | `(nanollvm_exp| splat ($te:nanollvm_typed_exp)) => do
      let e ← elabNanoLlvmTypedExpAux fuel te
      mkAppM ``Exp.splat #[e]
    | `(nanollvm_exp| getelementptr $flags:nanollvm_gep_flag* ($baseTy:nanollvm_type, $ptr:nanollvm_typed_exp $[, $idxs:nanollvm_typed_exp]*)) => do
      let flE := toExpr (elabGEPFlags flags)
      let idxList ← mkListLit (← mkPairTyLlvmExp) (← idxs.toList.mapM (fun x => elabNanoLlvmTypedExpAux fuel x.raw))
      mkAppM ``Exp.gepConst #[flE, ← elabNanoLlvmType baseTy, ← elabNanoLlvmTypedExpAux fuel ptr, idxList]
    | `(nanollvm_exp| $op:nanollvm_conversion_op ($fTy:nanollvm_type $v:nanollvm_exp to $tTy:nanollvm_type)) => do
      mkAppM ``Exp.convConst #[← elabNanoLlvmConversionOp op, ← elabNanoLlvmType fTy, ← elabNanoLlvmExpAux fuel v, ← elabNanoLlvmType tTy]
    | `(nanollvm_exp| $op:nanollvm_int_bin_op ($ty:nanollvm_type $v1:nanollvm_exp, $_ty2:nanollvm_type $v2:nanollvm_exp)) => do
      mkAppM ``Exp.binConst #[← elabNanoLlvmIntBinOp op, ← elabNanoLlvmType ty, ← elabNanoLlvmExpAux fuel v1, ← elabNanoLlvmExpAux fuel v2]
    | `(nanollvm_exp| insertelement ($vTe:nanollvm_typed_exp, $eTe:nanollvm_typed_exp, $iTe:nanollvm_typed_exp)) => do
      match vTe.raw, eTe.raw, iTe.raw with
      | `(nanollvm_typed_exp| $vTy:nanollvm_type $v:nanollvm_exp),
        `(nanollvm_typed_exp| $eTy:nanollvm_type $e:nanollvm_exp),
        `(nanollvm_typed_exp| $iTy:nanollvm_type $i:nanollvm_exp) =>
          mkAppM ``Exp.insertElemConst #[← elabNanoLlvmType vTy, ← elabNanoLlvmExpAux fuel v, ← elabNanoLlvmType eTy, ← elabNanoLlvmExpAux fuel e, ← elabNanoLlvmType iTy, ← elabNanoLlvmExpAux fuel i]
      | _, _, _ => throwUnsupportedSyntax
    | `(nanollvm_exp| extractelement ($vTe:nanollvm_typed_exp, $iTe:nanollvm_typed_exp)) => do
      match vTe.raw, iTe.raw with
      | `(nanollvm_typed_exp| $vTy:nanollvm_type $v:nanollvm_exp),
        `(nanollvm_typed_exp| $iTy:nanollvm_type $i:nanollvm_exp) =>
          mkAppM ``Exp.extractElemConst #[← elabNanoLlvmType vTy, ← elabNanoLlvmExpAux fuel v, ← elabNanoLlvmType iTy, ← elabNanoLlvmExpAux fuel i]
      | _, _ => throwUnsupportedSyntax
    | `(nanollvm_exp| shufflevector ($v1Te:nanollvm_typed_exp, $v2Te:nanollvm_typed_exp, < $_mLen:num x i32 > < $mask:nanollvm_shuffle_elem,* >)) => do
      match v1Te.raw, v2Te.raw with
      | `(nanollvm_typed_exp| $vTy:nanollvm_type $v1:nanollvm_exp),
        `(nanollvm_typed_exp| $_vTy2:nanollvm_type $v2:nanollvm_exp) =>
          mkAppM ``Exp.shuffleVecConst #[← elabNanoLlvmType vTy, ← elabNanoLlvmExpAux fuel v1, ← elabNanoLlvmExpAux fuel v2, ← elabShuffleMask mask]
      | _, _ => throwUnsupportedSyntax
    | _ => throwUnsupportedSyntax
end

def elabNanoLlvmTypedExp (stx : Syntax) : TermElabM Expr := elabNanoLlvmTypedExpAux 1000 stx
def elabNanoLlvmExp (stx : Syntax) : TermElabM Expr := elabNanoLlvmExpAux 1000 stx

elab "[llvm-exp|" p:nanollvm_exp "]" : term => elabNanoLlvmExp p

/-! ### Instructions -/

declare_syntax_cat nanollvm_phi_incoming
scoped syntax "[" nanollvm_exp ", " "%" nanollvm_rawid "]" : nanollvm_phi_incoming

declare_syntax_cat nanollvm_alloca_opt
scoped syntax "align " num : nanollvm_alloca_opt
scoped syntax "addrspace(" num ")" : nanollvm_alloca_opt
scoped syntax nanollvm_typed_exp : nanollvm_alloca_opt

declare_syntax_cat nanollvm_load_opt
scoped syntax "align " num : nanollvm_load_opt
scoped syntax "!" nanollvm_value_attr : nanollvm_load_opt

declare_syntax_cat nanollvm_call_arg
scoped syntax nanollvm_type nanollvm_value_attr* ppHardSpace nanollvm_exp : nanollvm_call_arg

declare_syntax_cat nanollvm_op_bundle
scoped syntax str "(" nanollvm_typed_exp,* ")" : nanollvm_op_bundle

declare_syntax_cat nanollvm_instruction
scoped syntax nanollvm_int_bin_op ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_exp : nanollvm_instruction
scoped syntax "fneg" nanollvm_fmf_flag* ppHardSpace nanollvm_type ppHardSpace nanollvm_exp : nanollvm_instruction
scoped syntax nanollvm_fp_bin_op ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_exp : nanollvm_instruction
scoped syntax "icmp" " samesign"? ppHardSpace ident ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_exp : nanollvm_instruction
scoped syntax "fcmp" nanollvm_fmf_flag* ppHardSpace ident ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_exp : nanollvm_instruction
scoped syntax nanollvm_conversion_op ppHardSpace nanollvm_type ppHardSpace nanollvm_exp " to " nanollvm_type : nanollvm_instruction
scoped syntax "select" nanollvm_fmf_flag* ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_type ppHardSpace nanollvm_exp : nanollvm_instruction
scoped syntax "phi" nanollvm_fmf_flag* ppHardSpace nanollvm_type ppHardSpace nanollvm_phi_incoming (atomic(", " nanollvm_phi_incoming))* (", " "!" nanollvm_value_attr)* : nanollvm_instruction
scoped syntax "alloca" ppHardSpace nanollvm_type (", " nanollvm_alloca_opt)* : nanollvm_instruction
scoped syntax "load" " volatile"? ppHardSpace nanollvm_type ", " nanollvm_type ppHardSpace nanollvm_exp (", " nanollvm_load_opt)* : nanollvm_instruction
scoped syntax "store" " volatile"? ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_type ppHardSpace nanollvm_exp (", " "align " num)? : nanollvm_instruction
scoped syntax "getelementptr" nanollvm_gep_flag* ppHardSpace nanollvm_type ", " nanollvm_type ppHardSpace nanollvm_exp (", " nanollvm_typed_exp)* : nanollvm_instruction
scoped syntax "extractvalue" ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " num,+ : nanollvm_instruction
scoped syntax "insertvalue" ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_type ppHardSpace nanollvm_exp ", " num,+ : nanollvm_instruction
scoped syntax "extractelement" ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_type ppHardSpace nanollvm_exp : nanollvm_instruction
scoped syntax "insertelement" ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_type ppHardSpace nanollvm_exp : nanollvm_instruction
scoped syntax "shufflevector" ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_type ppHardSpace nanollvm_exp ", " "<" num ppHardSpace &"x" ppHardSpace &"i32" ">" " <" nanollvm_shuffle_elem,+ ">" : nanollvm_instruction
scoped syntax ("tail ")? "call" nanollvm_fmf_flag* (" cc " str)? nanollvm_value_attr* ppHardSpace nanollvm_type ppHardSpace nanollvm_exp "(" nanollvm_call_arg,* ")" (" [" nanollvm_op_bundle,* "]")? (" noreturn")? : nanollvm_instruction
scoped syntax "freeze" ppHardSpace nanollvm_type ppHardSpace nanollvm_exp : nanollvm_instruction
scoped syntax "bitinsert" ppHardSpace nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_type ppHardSpace nanollvm_exp : nanollvm_instruction
scoped syntax "bitextract" ppHardSpace nanollvm_type ", " nanollvm_type ppHardSpace nanollvm_exp ", " nanollvm_type ppHardSpace nanollvm_exp : nanollvm_instruction

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
  | `(nanollvm_instruction| phi $flags:nanollvm_fmf_flag* $ty:nanollvm_type $inc0:nanollvm_phi_incoming $[, $incRest:nanollvm_phi_incoming]* $[, !$mds:nanollvm_value_attr]*) => do
    let pairTy ← mkAppM ``Prod #[mkConst ``Exp, mkConst ``RawId]
    let allIncs := #[inc0] ++ incRest
    let incExprs ← allIncs.toList.mapM fun inc =>
      match inc.raw with
      | `(nanollvm_phi_incoming| [ $e:nanollvm_exp, %$lbl:nanollvm_rawid ]) => do
        mkAppM ``Prod.mk #[← elabNanoLlvmExp e, ← elabNanoLlvmRawId lbl]
      | _ => throwUnsupportedSyntax
    let lst ← mkListLit pairTy incExprs
    mkAppM ``Instruction.phi #[← elabNanoLlvmType ty, toExpr (elabFastMathFlags flags), lst, ← elabValueAttrList mds]
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
      | `(nanollvm_load_opt| !$attr:nanollvm_value_attr) =>
        match attr.raw with
        | `(nanollvm_value_attr| noundef) => hasNoundef := Bool.true
        | _ => mdAttrs := mdAttrs.push (← elabNanoLlvmValueAttr attr.raw)
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
    mkAppM ``Instruction.shufflevector #[← elabNanoLlvmType vecTy, ← elabNanoLlvmExp v1, ← elabNanoLlvmExp v2, ← elabShuffleMask mask]
  | `(nanollvm_instruction| $[tail%$tl]? call $flags:nanollvm_fmf_flag* $[cc $ccName:str]? $retAttrs:nanollvm_value_attr* $retTy:nanollvm_type $callee:nanollvm_exp ( $args:nanollvm_call_arg,* ) $[[ $bundles:nanollvm_op_bundle,* ]]? $[noreturn%$nr]?) => do
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
    let teListTy ← mkAppM ``List #[← mkPairTyLlvmExp]
    let bundleTy ← mkAppM ``Prod #[mkConst ``String, teListTy]
    let bundleExprs ← match bundles with
      | none => pure []
      | some bs => bs.getElems.toList.mapM fun b =>
        match b.raw with
        | `(nanollvm_op_bundle| $tag:str ($tes:nanollvm_typed_exp,*)) => do
          let teEs ← tes.getElems.toList.mapM (fun x => elabNanoLlvmTypedExp x.raw)
          let teLst ← mkListLit (← mkPairTyLlvmExp) teEs
          mkAppM ``Prod.mk #[mkStrLit tag.getString, teLst]
        | _ => throwUnsupportedSyntax
    let bundleList ← mkListLit bundleTy bundleExprs
    -- The call's function type, as the IR parser records it (`CallSiteInfo.fnTy?`): written as the
    -- return type (`call i32 (ptr, ...) @printf(...)`), or else the non-variadic type of the
    -- arguments.
    let (retE, fnTyE) ← match retTy with
      | `(nanollvm_type| $r:nanollvm_type ( $_ps:nanollvm_fn_param,* )) => do
        pure (← elabNanoLlvmRetType r, ← elabNanoLlvmType retTy)
      | _ => do
        let retE ← elabNanoLlvmRetType retTy
        let argTyEs ← args.getElems.toList.mapM fun a =>
          match a.raw with
          | `(nanollvm_call_arg| $t:nanollvm_type $_attrs:nanollvm_value_attr* $_e:nanollvm_exp) =>
            elabNanoLlvmType t
          | _ => throwUnsupportedSyntax
        pure (retE, ← mkAppM ``LlvmType.function
          #[retE, ← mkListLit (mkConst ``LlvmType) argTyEs, toExpr false])
    let siteE ← mkAppM ``CallSiteInfo.mk #[toExpr tl.isSome,
      mkStrLit ((ccName.map (·.getString)).getD ""), ← mkAppM ``Option.some #[fnTyE]]
    mkAppM ``Instruction.call #[retE, toExpr (elabFastMathFlags flags), ← elabNanoLlvmExp callee, argList, ← elabValueAttrList retAttrs, bundleList, toExpr nr.isSome, siteE]
  | `(nanollvm_instruction| freeze $ty:nanollvm_type $v:nanollvm_exp) => do
    let tv ← mkAppM ``Prod.mk #[← elabNanoLlvmType ty, ← elabNanoLlvmExp v]
    mkAppM ``Instruction.freeze #[tv]
  | `(nanollvm_instruction| bitinsert $bTy:nanollvm_type $b:nanollvm_exp, $vTy:nanollvm_type $v:nanollvm_exp, $oTy:nanollvm_type $o:nanollvm_exp) => do
    mkAppM ``Instruction.bitinsert #[← elabNanoLlvmType bTy, ← elabNanoLlvmExp b, ← elabNanoLlvmType vTy, ← elabNanoLlvmExp v, ← elabNanoLlvmType oTy, ← elabNanoLlvmExp o]
  | `(nanollvm_instruction| bitextract $rTy:nanollvm_type, $sTy:nanollvm_type $s:nanollvm_exp, $oTy:nanollvm_type $o:nanollvm_exp) => do
    mkAppM ``Instruction.bitextract #[← elabNanoLlvmType rTy, ← elabNanoLlvmType sTy, ← elabNanoLlvmExp s, ← elabNanoLlvmType oTy, ← elabNanoLlvmExp o]
  | _ => throwUnsupportedSyntax

elab "[llvm-instruction|" p:nanollvm_instruction "]" : term => elabNanoLlvmInstruction p

/-! ### Terminators -/

declare_syntax_cat nanollvm_switch_case
scoped syntax nanollvm_type ppHardSpace nanollvm_signed_int ", " "label " "%" nanollvm_rawid : nanollvm_switch_case

declare_syntax_cat nanollvm_indirectbr_dest
scoped syntax "label " "%" nanollvm_rawid : nanollvm_indirectbr_dest

declare_syntax_cat nanollvm_terminator
scoped syntax "ret " "void" : nanollvm_terminator
scoped syntax "ret " nanollvm_type ppHardSpace nanollvm_exp : nanollvm_terminator
scoped syntax "br " "label " "%" nanollvm_rawid : nanollvm_terminator
scoped syntax "br " &"i1" ppHardSpace nanollvm_exp ", " "label " "%" nanollvm_rawid ", " "label " "%" nanollvm_rawid : nanollvm_terminator
scoped syntax "switch " nanollvm_type ppHardSpace nanollvm_exp ", " "label " "%" nanollvm_rawid " [" nanollvm_switch_case* "]" : nanollvm_terminator
scoped syntax "indirectbr " &"ptr" ppHardSpace nanollvm_exp ", " "[" nanollvm_indirectbr_dest,* "]" : nanollvm_terminator
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
  | `(nanollvm_terminator| indirectbr ptr $addr:nanollvm_exp, [ $dests:nanollvm_indirectbr_dest,* ]) => do
    let destExprs ← dests.getElems.toList.mapM fun d =>
      match d.raw with
      | `(nanollvm_indirectbr_dest| label %$lbl:nanollvm_rawid) => elabNanoLlvmRawId lbl
      | _ => throwUnsupportedSyntax
    let destList ← mkListLit (mkConst ``RawId) destExprs
    mkAppM ``Terminator.indirectBr #[← elabNanoLlvmExp addr, destList]
  | `(nanollvm_terminator| unreachable) => pure (mkConst ``Terminator.unreachable)
  | _ => throwUnsupportedSyntax

elab "[llvm-terminator|" p:nanollvm_terminator "]" : term => elabNanoLlvmTerminator p

/-! ### Declarations, Blocks, Definitions, Globals, Modules -/

declare_syntax_cat nanollvm_fn_attr
scoped syntax "noreturn" : nanollvm_fn_attr
scoped syntax "nobuiltin" : nanollvm_fn_attr
scoped syntax "denormal_fpenv(" ident "|" ident ")" : nanollvm_fn_attr

private def elabDenormalModeKind (id : TSyntax `ident) : TermElabM DenormalModeKind := do
  match id.getId.toString with
  | "ieee" => pure .ieee
  | "preservesign" => pure .preserveSign
  | "positivezero" => pure .positiveZero
  | other => throwErrorAt id "Unknown denormal mode kind '{other}'"

private def elabFnAttrs (attrs : Array (TSyntax `nanollvm_fn_attr)) : TermElabM (Bool × Bool × Option DenormalMode) := do
  let mut isNoReturn := false
  let mut isNoBuiltin := false
  let mut denorm : Option DenormalMode := none
  for a in attrs do
    match a.raw with
    | `(nanollvm_fn_attr| noreturn) => isNoReturn := true
    | `(nanollvm_fn_attr| nobuiltin) => isNoBuiltin := true
    | `(nanollvm_fn_attr| denormal_fpenv($outId:ident | $inId:ident)) =>
      let outK ← elabDenormalModeKind outId
      let inK ← elabDenormalModeKind inId
      denorm := some { input := inK, output := outK }
    | _ => throwUnsupportedSyntax
  pure (isNoReturn, isNoBuiltin, denorm)

declare_syntax_cat nanollvm_decl_arg
scoped syntax nanollvm_type nanollvm_value_attr* : nanollvm_decl_arg
scoped syntax "..." : nanollvm_decl_arg

declare_syntax_cat nanollvm_declaration
scoped syntax "declare " ("cc " str ppHardSpace)? nanollvm_value_attr* nanollvm_type ppHardSpace "@" nanollvm_rawid "(" nanollvm_decl_arg,* ")" nanollvm_fn_attr* : nanollvm_declaration

def elabNanoLlvmDeclaration : Syntax → TermElabM Expr
  | `(nanollvm_declaration| declare $[cc $ccName:str]? $retAttrs:nanollvm_value_attr* $retTy:nanollvm_type @$id:nanollvm_rawid($params:nanollvm_decl_arg,*) $fnAttrs:nanollvm_fn_attr*) => do
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
    let (isNoReturn, isNoBuiltin, denorm) ← elabFnAttrs fnAttrs
    let denormE ← mkOptionExpr (mkConst ``DenormalMode) (denorm.map toExpr)
    let ccStr := (ccName.map (·.getString)).getD ""
    mkAppM ``Declaration.mk #[idE, fnTy, argAttrsList, ← elabValueAttrList retAttrs, toExpr isNoReturn, toExpr isNoBuiltin, denormE, toExpr ccStr,
      ← mkOptionExpr (mkConst ``DenormalMode) none, ← mkOptionExpr (mkConst ``FunctionId) none]
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
scoped syntax "define " ("cc " str ppHardSpace)? nanollvm_value_attr* nanollvm_type ppHardSpace "@" nanollvm_rawid "(" nanollvm_arg,* ")" nanollvm_fn_attr* ppHardSpace
       ppDedent(ppDedent("{" (ppLine nanollvm_block)+ ppLine "}")) : nanollvm_definition

def elabNanoLlvmDefinition : Syntax → TermElabM Expr
  | `(nanollvm_definition| define $[cc $ccName:str]? $retAttrs:nanollvm_value_attr* $retTy:nanollvm_type @$id:nanollvm_rawid($args:nanollvm_arg,*) $fnAttrs:nanollvm_fn_attr* {
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
    let (isNoReturn, isNoBuiltin, denorm) ← elabFnAttrs fnAttrs
    let denormE ← mkOptionExpr (mkConst ``DenormalMode) (denorm.map toExpr)
    let ccStr := (ccName.map (·.getString)).getD ""
    let decl ← mkAppM ``Declaration.mk #[idE, fnTy, argAttrsList, ← elabValueAttrList retAttrs, toExpr isNoReturn, toExpr isNoBuiltin, denormE, toExpr ccStr,
      ← mkOptionExpr (mkConst ``DenormalMode) none, ← mkOptionExpr (mkConst ``FunctionId) none]
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
