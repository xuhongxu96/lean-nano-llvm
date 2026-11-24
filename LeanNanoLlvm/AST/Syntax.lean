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

/-! ### Types -/

declare_syntax_cat nanollvm_type
scoped syntax "void" : nanollvm_type
scoped syntax ident : nanollvm_type
scoped syntax nanollvm_type " addrspace(" num ")" : nanollvm_type
scoped syntax "i$" num : nanollvm_type
scoped syntax "<" num &"x" nanollvm_type ">" : nanollvm_type
scoped syntax "[" num &"x" nanollvm_type "]" : nanollvm_type
scoped syntax "{" nanollvm_type,* "}" : nanollvm_type
scoped syntax "<{" nanollvm_type,* "}>" : nanollvm_type
scoped syntax nanollvm_type "(" nanollvm_type,* ")" : nanollvm_type

mutual
partial def elabNanoLlvmType (φ : Nat) : Syntax → MetaM Expr
  | `(nanollvm_type| $id:ident) => do
    let s := id.getId.toString
    match s with
    | "half"   => mkAppOptM ``LlvmType.float #[mkNatLit φ, mkConst ``FloatType.half]
    | "bfloat" => mkAppOptM ``LlvmType.float #[mkNatLit φ, mkConst ``FloatType.bfloat]
    | "float"  => mkAppOptM ``LlvmType.float #[mkNatLit φ, mkConst ``FloatType.float]
    | "double" => mkAppOptM ``LlvmType.float #[mkNatLit φ, mkConst ``FloatType.double]
    | "fp128"  => mkAppOptM ``LlvmType.float #[mkNatLit φ, mkConst ``FloatType.fp128]
    | "ptr"    => mkAppOptM ``LlvmType.ptr #[mkNatLit φ, mkNatLit 0]
    | _ =>
      if s.startsWith "i" then
        let numStr := s.drop 1
        match numStr.toNat? with
        | some n =>
          let w ← mkAppOptM ``Width.concrete #[mkNatLit φ, mkNatLit n]
          mkAppM ``LlvmType.int #[w]
        | none => throwError "Invalid LLVM type: {s}"
      else
        throwError "Unknown LLVM type: {s}"

  | `(nanollvm_type| $base:nanollvm_type addrspace($as:num)) => do
    match base with
    | `(nanollvm_type| $id:ident) =>
      if id.getId.toString == "ptr" then
        mkAppOptM ``LlvmType.ptr #[mkNatLit φ, mkNatLit as.getNat]
      else
        throwError "Expected 'ptr' before addrspace(...), got {id}"
    | _ => throwError "Expected 'ptr' before addrspace(...)"

  | `(nanollvm_type| i$ $n:num) => do
    let idx := n.getNat
    if h : idx < φ then
      let i : Fin φ := ⟨idx, h⟩
      let w ← mkAppM ``Width.mvar #[toExpr i]
      mkAppM ``LlvmType.int #[w]
    else
      throwError "Width metavariable index {idx} out of bounds for φ = {φ}"

  | `(nanollvm_type| < $n:num x $elem:nanollvm_type >) => do
    let elemTy ← elabNanoLlvmType φ elem
    mkAppOptM ``LlvmType.vector #[mkNatLit φ, mkNatLit n.getNat, elemTy]

  | `(nanollvm_type| [ $n:num x $elem:nanollvm_type ]) => do
    let elemTy ← elabNanoLlvmType φ elem
    mkAppOptM ``LlvmType.array #[mkNatLit φ, mkNatLit n.getNat, elemTy]

  | `(nanollvm_type| { $fields:nanollvm_type,* }) => do
    let ty ← mkAppM ``LlvmType #[mkNatLit φ]
    let fVals ← fields.getElems.mapM (elabNanoLlvmType φ)
    let fList ← mkListLit ty fVals.toList
    mkAppOptM ``LlvmType.struct #[mkNatLit φ, toExpr false, fList]

  | `(nanollvm_type| <{ $fields:nanollvm_type,* }>) => do
    let ty ← mkAppM ``LlvmType #[mkNatLit φ]
    let fVals ← fields.getElems.mapM (elabNanoLlvmType φ)
    let fList ← mkListLit ty fVals.toList
    mkAppOptM ``LlvmType.struct #[mkNatLit φ, toExpr true, fList]

  | `(nanollvm_type| $ret:nanollvm_type ( $params:nanollvm_type,* )) => do
    let ty ← mkAppM ``LlvmType #[mkNatLit φ]
    let ret ← elabNanoLlvmRetType φ ret
    let argVals ← params.getElems.mapM (elabNanoLlvmType φ)
    let argList ← mkListLit ty argVals.toList
    mkAppOptM ``LlvmType.function #[mkNatLit φ, ret, argList, toExpr false]

  | _ => throwUnsupportedSyntax

partial def elabNanoLlvmRetType (φ : Nat) : Syntax → MetaM Expr
  | `(nanollvm_type| void) => mkAppOptM ``LlvmRetType.void #[mkNatLit φ]
  | stx => do
    let ty ← elabNanoLlvmType φ stx
    mkAppM ``LlvmRetType.ret #[ty]
end

elab "[llvm-" n:num "-type|" p:nanollvm_type "]" : term => elabNanoLlvmType n.getNat p
elab "[llvm-type|" p:nanollvm_type "]" : term => elabNanoLlvmType 0 p

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
scoped syntax "undef!" nanollvm_rawid : nanollvm_exp
scoped syntax "poison" : nanollvm_exp
scoped syntax "[" nanollvm_typed_exp,* "]" : nanollvm_exp
scoped syntax "{" nanollvm_typed_exp,* "}" : nanollvm_exp
scoped syntax "<{" nanollvm_typed_exp,* "}>" : nanollvm_exp
scoped syntax "<" nanollvm_typed_exp,+ ">" : nanollvm_exp
scoped syntax "splat" "(" nanollvm_typed_exp ")" : nanollvm_exp

private def mkIntLitExpr (i : Int) : MetaM Expr := do
  if i ≥ 0 then
    mkAppM ``Int.ofNat #[mkNatLit i.toNat]
  else
    mkAppM ``Int.negSucc #[mkNatLit ((-i - 1).toNat)]

mutual
partial def elabNanoLlvmTypedExp (φ : Nat) (undefStartIndex : Nat) : Syntax → MetaM (Expr × Nat)
  | `(nanollvm_typed_exp| $ty:nanollvm_type $e:nanollvm_exp) => do
    let ty ← elabNanoLlvmType φ ty
    let (e, next) ← elabNanoLlvmExp φ undefStartIndex e
    pure (← mkAppM ``Prod.mk #[ty, e], next)
  | _ => throwUnsupportedSyntax

partial def elabNanoLlvmExp (φ : Nat) (undefStartIndex : Nat) : Syntax → MetaM (Expr × Nat)
  | `(nanollvm_exp| $id:nanollvm_identifier) => do
    let id ← elabNanoLlvmIdentifier id
    pure (← mkAppOptM ``Exp.identifier #[mkNatLit φ, id], undefStartIndex)
  | `(nanollvm_exp| <$id:ident:int>) => do
    let lctx ← getLCtx
    match lctx.findFromUserName? id.getId with
    | some decl =>
      let e := decl.toExpr
      let t ← whnf (← inferType e)
      if ← isDefEq t (mkConst ``Int) then
        pure (← mkAppOptM ``Exp.int #[mkNatLit φ, e], undefStartIndex)
      else if ← isDefEq t (mkConst ``Nat) then
        pure (← mkAppOptM ``Exp.int #[mkNatLit φ, ← mkAppM ``Int.ofNat #[e]], undefStartIndex)
      else
        throwErrorAt id "Expected local Int/Nat variable in LLVM expression, got type {t}"
    | none =>
      throwErrorAt id "Unknown local identifier '{id.getId}' in LLVM expression"
  | `(nanollvm_exp| $id:ident) => do
    match id.getId.toString with
    | "true"  => pure (← mkAppOptM ``Exp.bool #[mkNatLit φ, Expr.const ``Bool.true []], undefStartIndex)
    | "false" => pure (← mkAppOptM ``Exp.bool #[mkNatLit φ, Expr.const ``Bool.false []], undefStartIndex)
    | other   => throwErrorAt id "Unknown LLVM expression keyword '{other}'"
  | `(nanollvm_exp| $n:num) => do
    let int ← mkAppM ``Int.ofNat #[mkNatLit n.getNat]
    pure (← mkAppOptM ``Exp.int #[mkNatLit φ, int], undefStartIndex)
  | `(nanollvm_exp| -$n:num) => do
    let int ← mkIntLitExpr (-(n.getNat : Int))
    pure (← mkAppOptM ``Exp.int #[mkNatLit φ, int], undefStartIndex)
  | `(nanollvm_exp| $s:scientific) => do
    let (m, negExp, e) := s.getScientific
    let exp10 : Int := if negExp then -(e : Int) else (e : Int)
    let exp10E ← mkIntLitExpr exp10
    pure (← mkAppOptM ``Exp.floatDec #[mkNatLit φ, toExpr Bool.false, mkNatLit m, exp10E], undefStartIndex)
  | `(nanollvm_exp| -$s:scientific) => do
    let (m, negExp, e) := s.getScientific
    let exp10 : Int := if negExp then -(e : Int) else (e : Int)
    let exp10E ← mkIntLitExpr exp10
    pure (← mkAppOptM ``Exp.floatDec #[mkNatLit φ, toExpr Bool.true, mkNatLit m, exp10E], undefStartIndex)
  | `(nanollvm_exp| fbits($n:num)) => do
    pure (← mkAppOptM ``Exp.floatBits #[mkNatLit φ, mkNatLit n.getNat], undefStartIndex)
  | `(nanollvm_exp| null) => do
    pure (← mkAppOptM ``Exp.null #[mkNatLit φ], undefStartIndex)
  | `(nanollvm_exp| zeroinitializer) => do
    pure (← mkAppOptM ``Exp.zeroinitializer #[mkNatLit φ], undefStartIndex)
  | `(nanollvm_exp| undef) => do
    let rawid ← mkAppM ``RawId.anonymous #[mkNatLit undefStartIndex]
    pure (← mkAppOptM ``Exp.undef #[mkNatLit φ, rawid], undefStartIndex + 1)
  | `(nanollvm_exp| undef!$rawid:nanollvm_rawid) => do
    let rawid ← elabNanoLlvmRawId rawid
    pure (← mkAppOptM ``Exp.undef #[mkNatLit φ, rawid], undefStartIndex)
  | `(nanollvm_exp| poison) => do
    pure (← mkAppOptM ``Exp.poison #[mkNatLit φ], undefStartIndex)
  | `(nanollvm_exp| [ $elems:nanollvm_typed_exp,* ]) => do
    let pairTy ← mkAppM ``Prod #[← mkAppM ``LlvmType #[mkNatLit φ], ← mkAppM ``Exp #[mkNatLit φ]]
    let mut next := undefStartIndex
    let mut acc : Array Expr := #[]
    for elem in elems.getElems do
      let (e, n') ← elabNanoLlvmTypedExp φ next elem
      next := n'
      acc := acc.push e
    let lst ← mkListLit pairTy acc.toList
    pure (← mkAppOptM ``Exp.array #[mkNatLit φ, lst], next)
  | `(nanollvm_exp| { $elems:nanollvm_typed_exp,* }) => do
    let pairTy ← mkAppM ``Prod #[← mkAppM ``LlvmType #[mkNatLit φ], ← mkAppM ``Exp #[mkNatLit φ]]
    let mut next := undefStartIndex
    let mut acc : Array Expr := #[]
    for elem in elems.getElems do
      let (e, n') ← elabNanoLlvmTypedExp φ next elem
      next := n'
      acc := acc.push e
    let lst ← mkListLit pairTy acc.toList
    pure (← mkAppOptM ``Exp.struct #[mkNatLit φ, toExpr Bool.false, lst], next)
  | `(nanollvm_exp| <{ $elems:nanollvm_typed_exp,* }>) => do
    let pairTy ← mkAppM ``Prod #[← mkAppM ``LlvmType #[mkNatLit φ], ← mkAppM ``Exp #[mkNatLit φ]]
    let mut next := undefStartIndex
    let mut acc : Array Expr := #[]
    for elem in elems.getElems do
      let (e, n') ← elabNanoLlvmTypedExp φ next elem
      next := n'
      acc := acc.push e
    let lst ← mkListLit pairTy acc.toList
    pure (← mkAppOptM ``Exp.struct #[mkNatLit φ, toExpr Bool.true, lst], next)
  | `(nanollvm_exp| < $elems:nanollvm_typed_exp,* >) => do
    let pairTy ← mkAppM ``Prod #[← mkAppM ``LlvmType #[mkNatLit φ], ← mkAppM ``Exp #[mkNatLit φ]]
    let mut next := undefStartIndex
    let mut acc : Array Expr := #[]
    for elem in elems.getElems do
      let (e, n') ← elabNanoLlvmTypedExp φ next elem
      next := n'
      acc := acc.push e
    let lst ← mkListLit pairTy acc.toList
    pure (← mkAppOptM ``Exp.vector #[mkNatLit φ, lst], next)
  | `(nanollvm_exp| splat ($te:nanollvm_typed_exp)) => do
    let (e, next) ← elabNanoLlvmTypedExp φ undefStartIndex te
    pure (← mkAppOptM ``Exp.splat #[mkNatLit φ, e], next)
  | _ => throwUnsupportedSyntax
end

elab "[llvm-" n:num "-" m:num "-exp|" p:nanollvm_exp "]" : term => do
  pure (← elabNanoLlvmExp n.getNat m.getNat p).fst
elab "[llvm-" m:num "-exp|" p:nanollvm_exp "]" : term => do
  pure (← elabNanoLlvmExp 0 m.getNat p).fst
elab "[llvm-exp|" p:nanollvm_exp "]" : term => do
  pure (← elabNanoLlvmExp 0 0 p).fst

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

def elabNanoLlvmIntBinOp (stx : Syntax) : MetaM Expr := do
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

def elabNanoLlvmFpBinOp (stx : Syntax) : MetaM Expr := do
  let fmf := elabFastMathFlags (stx[1].getArgs.map fun s => ⟨s⟩)
  match stx[0].getAtomVal with
  | "fadd" => return mkApp (mkConst ``FloatBinaryOp.fadd) (toExpr fmf)
  | "fsub" => return mkApp (mkConst ``FloatBinaryOp.fsub) (toExpr fmf)
  | "fmul" => return mkApp (mkConst ``FloatBinaryOp.fmul) (toExpr fmf)
  | "fdiv" => return mkApp (mkConst ``FloatBinaryOp.fdiv) (toExpr fmf)
  | "frem" => return mkApp (mkConst ``FloatBinaryOp.frem) (toExpr fmf)
  | op     => throwErrorAt stx "unknown FloatBinaryOp opcode: {op}"

def elabICmpPred (id : TSyntax `ident) : MetaM Expr := do
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

def elabFCmpPred (id : TSyntax `ident) : MetaM Expr := do
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

def elabNanoLlvmConversionOp (stx : Syntax) : MetaM Expr := do
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

declare_syntax_cat nanollvm_call_arg
scoped syntax nanollvm_type ppHardSpace nanollvm_exp : nanollvm_call_arg
scoped syntax nanollvm_type " noundef " nanollvm_exp : nanollvm_call_arg
scoped syntax nanollvm_type " nonnull " nanollvm_exp : nanollvm_call_arg

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
scoped syntax "call" nanollvm_fmf_flag* ppHardSpace nanollvm_type ppHardSpace nanollvm_exp "(" nanollvm_call_arg,* ")" : nanollvm_instruction
scoped syntax "freeze" ppHardSpace nanollvm_type ppHardSpace nanollvm_exp : nanollvm_instruction

private def mkOptionExpr (ty : Expr) : Option Expr → MetaM Expr
  | none => mkAppOptM ``Option.none #[ty]
  | some e => mkAppOptM ``Option.some #[ty, e]

def elabNanoLlvmInstruction (φ : Nat) (_lineno : Nat) (undefStartIndex : Nat) : Syntax → MetaM (Expr × Nat)
  | `(nanollvm_instruction| $op:nanollvm_int_bin_op $ty:nanollvm_type $op1:nanollvm_exp, $op2:nanollvm_exp) => do
    let op ← elabNanoLlvmIntBinOp op
    let ty ← elabNanoLlvmType φ ty
    let (op1, undefNext) ← elabNanoLlvmExp φ undefStartIndex op1
    let (op2, undefNext) ← elabNanoLlvmExp φ undefNext op2
    pure (← mkAppOptM ``Instruction.intBinaryOp #[mkNatLit φ, op, ty, op1, op2], undefNext)
  | `(nanollvm_instruction| fneg $flags:nanollvm_fmf_flag* $ty:nanollvm_type $v:nanollvm_exp) => do
    let fmf := elabFastMathFlags flags
    let op := mkApp (mkConst ``FloatUnaryOp.fneg) (toExpr fmf)
    let ty ← elabNanoLlvmType φ ty
    let (v, undefNext) ← elabNanoLlvmExp φ undefStartIndex v
    pure (← mkAppOptM ``Instruction.floatUnaryOp #[mkNatLit φ, op, ty, v], undefNext)
  | `(nanollvm_instruction| $op:nanollvm_fp_bin_op $ty:nanollvm_type $op1:nanollvm_exp, $op2:nanollvm_exp) => do
    let op ← elabNanoLlvmFpBinOp op
    let ty ← elabNanoLlvmType φ ty
    let (op1, undefNext) ← elabNanoLlvmExp φ undefStartIndex op1
    let (op2, undefNext) ← elabNanoLlvmExp φ undefNext op2
    pure (← mkAppOptM ``Instruction.floatBinaryOp #[mkNatLit φ, op, ty, op1, op2], undefNext)
  | `(nanollvm_instruction| icmp $[samesign%$ss]? $pred:ident $ty:nanollvm_type $op1:nanollvm_exp, $op2:nanollvm_exp) => do
    let predE ← elabICmpPred pred
    let ty ← elabNanoLlvmType φ ty
    let (op1, undefNext) ← elabNanoLlvmExp φ undefStartIndex op1
    let (op2, undefNext) ← elabNanoLlvmExp φ undefNext op2
    pure (← mkAppOptM ``Instruction.icmp #[mkNatLit φ, toExpr ss.isSome, predE, ty, op1, op2], undefNext)
  | `(nanollvm_instruction| fcmp $flags:nanollvm_fmf_flag* $pred:ident $ty:nanollvm_type $op1:nanollvm_exp, $op2:nanollvm_exp) => do
    let fmf := elabFastMathFlags flags
    let predE ← elabFCmpPred pred
    let ty ← elabNanoLlvmType φ ty
    let (op1, undefNext) ← elabNanoLlvmExp φ undefStartIndex op1
    let (op2, undefNext) ← elabNanoLlvmExp φ undefNext op2
    pure (← mkAppOptM ``Instruction.fcmp #[mkNatLit φ, toExpr fmf, predE, ty, op1, op2], undefNext)
  | `(nanollvm_instruction| $op:nanollvm_conversion_op $fromTy:nanollvm_type $v:nanollvm_exp to $toTy:nanollvm_type) => do
    let op ← elabNanoLlvmConversionOp op
    let fromTy ← elabNanoLlvmType φ fromTy
    let (v, undefNext) ← elabNanoLlvmExp φ undefStartIndex v
    let toTy ← elabNanoLlvmType φ toTy
    pure (← mkAppOptM ``Instruction.conversionOp #[mkNatLit φ, op, fromTy, v, toTy], undefNext)
  | `(nanollvm_instruction| select $flags:nanollvm_fmf_flag* $cTy:nanollvm_type $c:nanollvm_exp, $vTy:nanollvm_type $tv:nanollvm_exp, $_fvTy:nanollvm_type $fv:nanollvm_exp) => do
    let fmf := elabFastMathFlags flags
    let cTy ← elabNanoLlvmType φ cTy
    let (c, undefNext) ← elabNanoLlvmExp φ undefStartIndex c
    let vTy ← elabNanoLlvmType φ vTy
    let (tv, undefNext) ← elabNanoLlvmExp φ undefNext tv
    let (fv, undefNext) ← elabNanoLlvmExp φ undefNext fv
    pure (← mkAppOptM ``Instruction.select #[mkNatLit φ, toExpr fmf, cTy, c, vTy, tv, fv], undefNext)
  | `(nanollvm_instruction| phi $flags:nanollvm_fmf_flag* $ty:nanollvm_type $incs:nanollvm_phi_incoming,*) => do
    let fmf := elabFastMathFlags flags
    let ty ← elabNanoLlvmType φ ty
    let expTy ← mkAppM ``Exp #[mkNatLit φ]
    let pairTy ← mkAppM ``Prod #[expTy, mkConst ``RawId]
    let mut next := undefStartIndex
    let mut acc : Array Expr := #[]
    for inc in incs.getElems do
      match inc with
      | `(nanollvm_phi_incoming| [ $e:nanollvm_exp, %$lbl:nanollvm_rawid ]) =>
        let (eE, n') ← elabNanoLlvmExp φ next e
        next := n'
        let lblE ← elabNanoLlvmRawId lbl
        acc := acc.push (← mkAppM ``Prod.mk #[eE, lblE])
      | _ => throwUnsupportedSyntax
    let lst ← mkListLit pairTy acc.toList
    pure (← mkAppOptM ``Instruction.phi #[mkNatLit φ, ty, toExpr fmf, lst], next)
  | `(nanollvm_instruction| alloca $ty:nanollvm_type $[, $opts:nanollvm_alloca_opt]*) => do
    let tyE ← elabNanoLlvmType φ ty
    let pairTy ← mkAppM ``Prod #[← mkAppM ``LlvmType #[mkNatLit φ], ← mkAppM ``Exp #[mkNatLit φ]]
    let mut numElOpt : Option Expr := none
    let mut alignOptVal : Option Expr := none
    let mut asVal : Nat := 0
    let mut cur := undefStartIndex
    for opt in opts do
      match opt with
      | `(nanollvm_alloca_opt| align $al:num) => alignOptVal := some (mkNatLit al.getNat)
      | `(nanollvm_alloca_opt| addrspace($as:num)) => asVal := as.getNat
      | `(nanollvm_alloca_opt| $te:nanollvm_typed_exp) =>
        let (e, n') ← elabNanoLlvmTypedExp φ cur te
        numElOpt := some e
        cur := n'
      | _ => throwUnsupportedSyntax
    let numElE ← mkOptionExpr pairTy numElOpt
    let alignOpt ← mkOptionExpr (mkConst ``Nat) alignOptVal
    pure (← mkAppOptM ``Instruction.alloca #[mkNatLit φ, tyE, numElE, alignOpt, mkNatLit asVal], cur)
  | `(nanollvm_instruction| load $[volatile%$vol]? $ty:nanollvm_type, $pTy:nanollvm_type $ptrExp:nanollvm_exp $[, $opts:nanollvm_load_opt]*) => do
    let tyE ← elabNanoLlvmType φ ty
    let pTyE ← elabNanoLlvmType φ pTy
    let (ptrE, next) ← elabNanoLlvmExp φ undefStartIndex ptrExp
    let mut alignOptVal : Option Expr := none
    let mut hasNoundef : Bool := Bool.false
    for opt in opts do
      match opt with
      | `(nanollvm_load_opt| align $al:num) => alignOptVal := some (mkNatLit al.getNat)
      | `(nanollvm_load_opt| !noundef) => hasNoundef := Bool.true
      | _ => throwUnsupportedSyntax
    let alignOpt ← mkOptionExpr (mkConst ``Nat) alignOptVal
    pure (← mkAppOptM ``Instruction.load #[mkNatLit φ, tyE, pTyE, ptrE, alignOpt, toExpr vol.isSome, toExpr hasNoundef], next)
  | `(nanollvm_instruction| store $[volatile%$vol]? $vTy:nanollvm_type $v:nanollvm_exp, $pTy:nanollvm_type $ptrExp:nanollvm_exp $[, align $al:num]?) => do
    let vTyE ← elabNanoLlvmType φ vTy
    let (vE, next) ← elabNanoLlvmExp φ undefStartIndex v
    let pTyE ← elabNanoLlvmType φ pTy
    let (ptrE, next) ← elabNanoLlvmExp φ next ptrExp
    let alignOpt ← mkOptionExpr (mkConst ``Nat) (al.map fun a => mkNatLit a.getNat)
    pure (← mkAppOptM ``Instruction.store #[mkNatLit φ, vTyE, vE, pTyE, ptrE, alignOpt, toExpr vol.isSome], next)
  | `(nanollvm_instruction| getelementptr $flags:nanollvm_gep_flag* $baseTy:nanollvm_type, $pTy:nanollvm_type $ptrExp:nanollvm_exp $[, $idxs:nanollvm_typed_exp]*) => do
    let gFlags := elabGEPFlags flags
    let baseTyE ← elabNanoLlvmType φ baseTy
    let pTyE ← elabNanoLlvmType φ pTy
    let (ptrE, next) ← elabNanoLlvmExp φ undefStartIndex ptrExp
    let pairTy ← mkAppM ``Prod #[← mkAppM ``LlvmType #[mkNatLit φ], ← mkAppM ``Exp #[mkNatLit φ]]
    let mut cur := next
    let mut acc : Array Expr := #[]
    for idx in idxs do
      let (e, n') ← elabNanoLlvmTypedExp φ cur idx
      cur := n'
      acc := acc.push e
    let idxList ← mkListLit pairTy acc.toList
    pure (← mkAppOptM ``Instruction.getelementptr #[mkNatLit φ, toExpr gFlags, baseTyE, pTyE, ptrE, idxList], cur)
  | `(nanollvm_instruction| extractvalue $aggTy:nanollvm_type $agg:nanollvm_exp, $idxs:num,*) => do
    let aggTyE ← elabNanoLlvmType φ aggTy
    let (aggE, next) ← elabNanoLlvmExp φ undefStartIndex agg
    let idxList ← mkListLit (mkConst ``Nat) (idxs.getElems.toList.map fun n => mkNatLit n.getNat)
    pure (← mkAppOptM ``Instruction.extractvalue #[mkNatLit φ, aggTyE, aggE, idxList], next)
  | `(nanollvm_instruction| insertvalue $aggTy:nanollvm_type $agg:nanollvm_exp, $valTy:nanollvm_type $val:nanollvm_exp, $idxs:num,*) => do
    let aggTyE ← elabNanoLlvmType φ aggTy
    let (aggE, next) ← elabNanoLlvmExp φ undefStartIndex agg
    let valTyE ← elabNanoLlvmType φ valTy
    let (valE, next) ← elabNanoLlvmExp φ next val
    let idxList ← mkListLit (mkConst ``Nat) (idxs.getElems.toList.map fun n => mkNatLit n.getNat)
    pure (← mkAppOptM ``Instruction.insertvalue #[mkNatLit φ, aggTyE, aggE, valTyE, valE, idxList], next)
  | `(nanollvm_instruction| extractelement $vecTy:nanollvm_type $vec:nanollvm_exp, $idxTy:nanollvm_type $idx:nanollvm_exp) => do
    let vecTyE ← elabNanoLlvmType φ vecTy
    let (vecE, next) ← elabNanoLlvmExp φ undefStartIndex vec
    let idxTyE ← elabNanoLlvmType φ idxTy
    let (idxE, next) ← elabNanoLlvmExp φ next idx
    pure (← mkAppOptM ``Instruction.extractelement #[mkNatLit φ, vecTyE, vecE, idxTyE, idxE], next)
  | `(nanollvm_instruction| insertelement $vecTy:nanollvm_type $vec:nanollvm_exp, $valTy:nanollvm_type $val:nanollvm_exp, $idxTy:nanollvm_type $idx:nanollvm_exp) => do
    let vecTyE ← elabNanoLlvmType φ vecTy
    let (vecE, next) ← elabNanoLlvmExp φ undefStartIndex vec
    let valTyE ← elabNanoLlvmType φ valTy
    let (valE, next) ← elabNanoLlvmExp φ next val
    let idxTyE ← elabNanoLlvmType φ idxTy
    let (idxE, next) ← elabNanoLlvmExp φ next idx
    pure (← mkAppOptM ``Instruction.insertelement #[mkNatLit φ, vecTyE, vecE, valTyE, valE, idxTyE, idxE], next)
  | `(nanollvm_instruction| shufflevector $vecTy:nanollvm_type $v1:nanollvm_exp, $_vecTy2:nanollvm_type $v2:nanollvm_exp, < $_mLen:num x i32 > < $mask:nanollvm_shuffle_elem,* >) => do
    let vecTyE ← elabNanoLlvmType φ vecTy
    let (v1E, next) ← elabNanoLlvmExp φ undefStartIndex v1
    let (v2E, next) ← elabNanoLlvmExp φ next v2
    let optNatTy ← mkAppM ``Option #[mkConst ``Nat]
    let maskElems ← mask.getElems.toList.mapM fun el =>
      match el with
      | `(nanollvm_shuffle_elem| $_t:nanollvm_type $n:num) => mkOptionExpr (mkConst ``Nat) (some (mkNatLit n.getNat))
      | `(nanollvm_shuffle_elem| $_t:nanollvm_type poison) => mkOptionExpr (mkConst ``Nat) none
      | _ => throwUnsupportedSyntax
    let maskList ← mkListLit optNatTy maskElems
    pure (← mkAppOptM ``Instruction.shufflevector #[mkNatLit φ, vecTyE, v1E, v2E, maskList], next)
  | `(nanollvm_instruction| call $flags:nanollvm_fmf_flag* $retTy:nanollvm_type $callee:nanollvm_exp ( $args:nanollvm_call_arg,* )) => do
    let fmf := elabFastMathFlags flags
    let retTyE ← elabNanoLlvmRetType φ retTy
    let (calleeE, next) ← elabNanoLlvmExp φ undefStartIndex callee
    let tyT ← mkAppM ``LlvmType #[mkNatLit φ]
    let expT ← mkAppM ``Exp #[mkNatLit φ]
    let attrT ← mkAppM ``ValueAttr #[mkNatLit φ]
    let attrListT ← mkAppM ``List #[attrT]
    let argInnerT ← mkAppM ``Prod #[expT, attrListT]
    let argTupleT ← mkAppM ``Prod #[tyT, argInnerT]
    let mut cur := next
    let mut acc : Array Expr := #[]
    for a in args.getElems do
      match a with
      | `(nanollvm_call_arg| $t:nanollvm_type $e:nanollvm_exp) =>
        let tE ← elabNanoLlvmType φ t
        let (eE, n') ← elabNanoLlvmExp φ cur e
        cur := n'
        let emptyAttrs ← mkListLit attrT []
        let inner ← mkAppM ``Prod.mk #[eE, emptyAttrs]
        acc := acc.push (← mkAppM ``Prod.mk #[tE, inner])
      | `(nanollvm_call_arg| $t:nanollvm_type noundef $e:nanollvm_exp) =>
        let tE ← elabNanoLlvmType φ t
        let (eE, n') ← elabNanoLlvmExp φ cur e
        cur := n'
        let attrs ← mkListLit attrT [← mkAppOptM ``ValueAttr.noundef #[mkNatLit φ]]
        let inner ← mkAppM ``Prod.mk #[eE, attrs]
        acc := acc.push (← mkAppM ``Prod.mk #[tE, inner])
      | `(nanollvm_call_arg| $t:nanollvm_type nonnull $e:nanollvm_exp) =>
        let tE ← elabNanoLlvmType φ t
        let (eE, n') ← elabNanoLlvmExp φ cur e
        cur := n'
        let attrs ← mkListLit attrT [← mkAppOptM ``ValueAttr.nonnull #[mkNatLit φ]]
        let inner ← mkAppM ``Prod.mk #[eE, attrs]
        acc := acc.push (← mkAppM ``Prod.mk #[tE, inner])
      | _ => throwUnsupportedSyntax
    let argList ← mkListLit argTupleT acc.toList
    let retAttrs ← mkListLit attrT []
    pure (← mkAppOptM ``Instruction.call #[mkNatLit φ, retTyE, toExpr fmf, calleeE, argList, retAttrs], cur)
  | `(nanollvm_instruction| freeze $ty:nanollvm_type $v:nanollvm_exp) => do
    let ty ← elabNanoLlvmType φ ty
    let (v, undefNext) ← elabNanoLlvmExp φ undefStartIndex v
    let tv ← mkAppM ``Prod.mk #[ty, v]
    pure (← mkAppOptM ``Instruction.freeze #[mkNatLit φ, tv], undefNext)
  | _ => throwUnsupportedSyntax

elab "[llvm-" n:num "-" m:num "-instruction|" p:nanollvm_instruction "]" : term => do
  pure (← elabNanoLlvmInstruction n.getNat m.getNat m.getNat p).fst
elab "[llvm-" n:num "-instruction|" p:nanollvm_instruction "]" : term => do
  pure (← elabNanoLlvmInstruction n.getNat 0 0 p).fst
elab "[llvm-instruction|" p:nanollvm_instruction "]" : term => do
  pure (← elabNanoLlvmInstruction 0 0 0 p).fst

/-! ### Terminators -/

declare_syntax_cat nanollvm_switch_case
scoped syntax nanollvm_type ppHardSpace num ", " "label " "%" nanollvm_rawid : nanollvm_switch_case
scoped syntax nanollvm_type ppHardSpace "-" num ", " "label " "%" nanollvm_rawid : nanollvm_switch_case

declare_syntax_cat nanollvm_terminator
scoped syntax "ret " "void" : nanollvm_terminator
scoped syntax "ret " nanollvm_type ppHardSpace nanollvm_exp : nanollvm_terminator
scoped syntax "br " "label " "%" nanollvm_rawid : nanollvm_terminator
scoped syntax "br " &"i1" ppHardSpace nanollvm_exp ", " "label " "%" nanollvm_rawid ", " "label " "%" nanollvm_rawid : nanollvm_terminator
scoped syntax "switch " nanollvm_type ppHardSpace nanollvm_exp ", " "label " "%" nanollvm_rawid " [" nanollvm_switch_case* "]" : nanollvm_terminator
scoped syntax "unreachable" : nanollvm_terminator

def elabNanoLlvmTerminator (φ : Nat) (undefStartIndex : Nat) : Syntax → MetaM (Expr × Nat)
  | `(nanollvm_terminator| ret void) => do
    pure (← mkAppOptM ``Terminator.retVoid #[mkNatLit φ], undefStartIndex)
  | `(nanollvm_terminator| ret $ty:nanollvm_type $e:nanollvm_exp) => do
    let ty ← elabNanoLlvmType φ ty
    let (e, undefNext) ← elabNanoLlvmExp φ undefStartIndex e
    let te ← mkAppM ``Prod.mk #[ty, e]
    pure (← mkAppOptM ``Terminator.ret #[mkNatLit φ, te], undefNext)
  | `(nanollvm_terminator| br label %$dest:nanollvm_rawid) => do
    let destE ← elabNanoLlvmRawId dest
    pure (← mkAppOptM ``Terminator.br #[mkNatLit φ, destE], undefStartIndex)
  | `(nanollvm_terminator| br i1 $cond:nanollvm_exp, label %$tDest:nanollvm_rawid, label %$fDest:nanollvm_rawid) => do
    let (condE, next) ← elabNanoLlvmExp φ undefStartIndex cond
    let tE ← elabNanoLlvmRawId tDest
    let fE ← elabNanoLlvmRawId fDest
    pure (← mkAppOptM ``Terminator.condBr #[mkNatLit φ, condE, tE, fE], next)
  | `(nanollvm_terminator| switch $ty:nanollvm_type $cond:nanollvm_exp, label %$defDest:nanollvm_rawid [ $cases:nanollvm_switch_case* ]) => do
    let tyE ← elabNanoLlvmType φ ty
    let (condE, next) ← elabNanoLlvmExp φ undefStartIndex cond
    let defE ← elabNanoLlvmRawId defDest
    let pairTy ← mkAppM ``Prod #[mkConst ``Int, mkConst ``RawId]
    let caseExprs ← cases.toList.mapM fun c =>
      match c with
      | `(nanollvm_switch_case| $_t:nanollvm_type $n:num, label %$lbl:nanollvm_rawid) => do
        let iE ← mkIntLitExpr (n.getNat : Int)
        let lE ← elabNanoLlvmRawId lbl
        mkAppM ``Prod.mk #[iE, lE]
      | `(nanollvm_switch_case| $_t:nanollvm_type -$n:num, label %$lbl:nanollvm_rawid) => do
        let iE ← mkIntLitExpr (-(n.getNat : Int))
        let lE ← elabNanoLlvmRawId lbl
        mkAppM ``Prod.mk #[iE, lE]
      | _ => throwUnsupportedSyntax
    let caseList ← mkListLit pairTy caseExprs
    pure (← mkAppOptM ``Terminator.switch #[mkNatLit φ, tyE, condE, defE, caseList], next)
  | `(nanollvm_terminator| unreachable) => do
    pure (← mkAppOptM ``Terminator.unreachable #[mkNatLit φ], undefStartIndex)
  | _ => throwUnsupportedSyntax

elab "[llvm-" n:num "-" m:num "-terminator|" p:nanollvm_terminator "]" : term => do
  pure (← elabNanoLlvmTerminator n.getNat m.getNat p).fst
elab "[llvm-" n:num "-terminator|" p:nanollvm_terminator "]" : term => do
  pure (← elabNanoLlvmTerminator n.getNat 0 p).fst
elab "[llvm-terminator|" p:nanollvm_terminator "]" : term => do
  pure (← elabNanoLlvmTerminator 0 0 p).fst

/-! ### Declarations, Blocks, Definitions, Globals, Modules -/

declare_syntax_cat nanollvm_declaration
scoped syntax "declare " nanollvm_type ppHardSpace "@" nanollvm_rawid "(" nanollvm_type,* ")" : nanollvm_declaration

def elabNanoLlvmDeclaration (φ : Nat) : Syntax → MetaM Expr
  | `(nanollvm_declaration| declare $retTy:nanollvm_type @$id:nanollvm_rawid($params:nanollvm_type,*)) => do
    let id ← elabNanoLlvmRawId id
    let ty ← mkAppM ``LlvmType #[mkNatLit φ]
    let retTy ← elabNanoLlvmRetType φ retTy
    let argVals ← params.getElems.mapM (elabNanoLlvmType φ)
    let argList ← mkListLit ty argVals.toList
    let fnTy ← mkAppOptM ``LlvmType.function #[mkNatLit φ, retTy, argList, toExpr Bool.false]
    let attrT ← mkAppM ``ValueAttr #[mkNatLit φ]
    let attrListT ← mkAppM ``List #[attrT]
    let emptyArgAttrs ← mkListLit attrListT []
    let emptyRetAttrs ← mkListLit attrT []
    mkAppOptM ``Declaration.mk #[mkNatLit φ, id, fnTy, emptyArgAttrs, emptyRetAttrs]
  | _ => throwUnsupportedSyntax

elab "[llvm-" n:num "-declaration|" p:nanollvm_declaration "]" : term => elabNanoLlvmDeclaration n.getNat p
elab "[llvm-declaration|" p:nanollvm_declaration "]" : term => elabNanoLlvmDeclaration 0 p

declare_syntax_cat nanollvm_codeline
scoped syntax "%" nanollvm_rawid " = " nanollvm_instruction : nanollvm_codeline
scoped syntax nanollvm_instruction : nanollvm_codeline

def elabNanoLlvmCodeline (φ : Nat) (lineno : Nat) (undefStartIndex : Nat) : Syntax → MetaM (Expr × Nat)
  | `(nanollvm_codeline| %$id:nanollvm_rawid = $instr:nanollvm_instruction) => do
    let id ← elabNanoLlvmRawId id
    let id ← mkAppM ``InstructionId.id #[id]
    let (instr, undefNext) ← elabNanoLlvmInstruction φ lineno undefStartIndex instr
    pure (← mkAppM ``Prod.mk #[id, instr], undefNext)
  | `(nanollvm_codeline| $instr:nanollvm_instruction) => do
    let id ← mkAppM ``InstructionId.void #[mkNatLit lineno]
    let (instr, undefNext) ← elabNanoLlvmInstruction φ lineno undefStartIndex instr
    pure (← mkAppM ``Prod.mk #[id, instr], undefNext)
  | _ => throwUnsupportedSyntax

elab "[llvm-" n:num "-" l:num "-codeline|" p:nanollvm_codeline "]" : term => do
  pure (← elabNanoLlvmCodeline n.getNat l.getNat 0 p).fst
elab "[llvm-codeline|" p:nanollvm_codeline "]" : term => do
  pure (← elabNanoLlvmCodeline 0 1 0 p).fst

declare_syntax_cat nanollvm_code
scoped syntax ppDedent(ppLine nanollvm_codeline)* : nanollvm_code

def elabNanoLlvmCode (φ : Nat) (lineno : Nat) (undefStartIndex : Nat) : Syntax → MetaM (Expr × Nat × Nat)
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
    pure (← mkListLit ty elabedCodelines.toList, elabedCodelines.size, undefNext)
  | _ => throwUnsupportedSyntax

elab "[llvm-" n:num "-" l:num "-code|" p:nanollvm_code "]" : term => do
  pure (← elabNanoLlvmCode n.getNat l.getNat 0 p).1
elab "[llvm-code|" p:nanollvm_code "]" : term => do
  pure (← elabNanoLlvmCode 0 1 0 p).1

declare_syntax_cat nanollvm_block
scoped syntax nanollvm_rawid ": " ppIndent(nanollvm_code ppLine nanollvm_terminator) : nanollvm_block

def elabNanoLlvmBlock (φ : Nat) (lineno : Nat) (undefStartIndex : Nat) : Syntax → MetaM (Expr × Nat × Nat)
  | `(nanollvm_block| $id:nanollvm_rawid:
  $code:nanollvm_code $term:nanollvm_terminator) => do
    let id ← elabNanoLlvmRawId id
    let (code, nLines, undefNext) ← elabNanoLlvmCode φ lineno undefStartIndex code
    let (term, undefNext) ← elabNanoLlvmTerminator φ undefNext term
    let termId ← mkAppM ``InstructionId.void #[mkNatLit (lineno + nLines)]
    let term ← mkAppM ``Prod.mk #[termId, term]
    pure (← mkAppM ``Block.mk #[id, code, term], nLines + 1, undefNext)
  | _ => throwUnsupportedSyntax

elab "[llvm-" n:num "-" l:num "-block|" p:nanollvm_block "]" : term => do
  pure (← elabNanoLlvmBlock n.getNat l.getNat 0 p).1
elab "[llvm-block|" p:nanollvm_block "]" : term => do
  pure (← elabNanoLlvmBlock 0 1 0 p).1

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
  let (ty, id) ← elabNanoLlvmArg 0 p
  mkAppM ``Prod.mk #[ty, id]

declare_syntax_cat nanollvm_definition
scoped syntax "define " nanollvm_type ppHardSpace "@" nanollvm_rawid "(" nanollvm_arg,* ") "
       ppDedent(ppDedent("{" (ppLine nanollvm_block)+ ppLine "}")) : nanollvm_definition

def elabNanoLlvmDefinition (φ : Nat) : Syntax → MetaM Expr
  | `(nanollvm_definition| define $retTy:nanollvm_type @$id:nanollvm_rawid($args:nanollvm_arg,*) {
    $blocks:nanollvm_block*
    }) => do
    let id ← elabNanoLlvmRawId id
    let argTy ← mkAppM ``LlvmType #[mkNatLit φ]
    let retTy ← elabNanoLlvmRetType φ retTy
    let argTys ← args.getElems.mapM (fun a => do pure (← elabNanoLlvmArg φ a).fst)
    let argNames ← args.getElems.mapM (fun a => do pure (← elabNanoLlvmArg φ a).snd)
    let argList ← mkListLit argTy argTys.toList
    let argNameList ← mkListLit (mkConst ``RawId) argNames.toList
    let fnTy ← mkAppOptM ``LlvmType.function #[mkNatLit φ, retTy, argList, toExpr Bool.false]
    let blockTy ← mkAppOptM ``Block #[mkNatLit φ]
    let mut curLine := 1
    let mut curUndef := 0
    let mut blockExprs : Array Expr := #[]
    for blk in blocks do
      let (bE, nLines, nextUndef) ← elabNanoLlvmBlock φ curLine curUndef blk
      curLine := curLine + nLines
      curUndef := nextUndef
      blockExprs := blockExprs.push bE
    let blockList ← mkListLit blockTy blockExprs.toList
    let attrT ← mkAppM ``ValueAttr #[mkNatLit φ]
    let attrListT ← mkAppM ``List #[attrT]
    let emptyArgAttrs ← mkListLit attrListT []
    let emptyRetAttrs ← mkListLit attrT []
    let decl ← mkAppOptM ``Declaration.mk #[mkNatLit φ, id, fnTy, emptyArgAttrs, emptyRetAttrs]
    mkAppOptM ``Definition.mk #[mkNatLit φ, decl, argNameList, blockList]
  | _ => throwUnsupportedSyntax

elab "[llvm-" n:num "-definition|" p:nanollvm_definition "]" : term => elabNanoLlvmDefinition n.getNat p
elab "[llvm-definition|" p:nanollvm_definition "]" : term => elabNanoLlvmDefinition 0 p

declare_syntax_cat nanollvm_global
scoped syntax "@" nanollvm_rawid " = " "global " nanollvm_type ppHardSpace nanollvm_exp (", " "align " num)? : nanollvm_global
scoped syntax "@" nanollvm_rawid " = " "constant " nanollvm_type ppHardSpace nanollvm_exp (", " "align " num)? : nanollvm_global

def elabNanoLlvmGlobal (φ : Nat) : Syntax → MetaM Expr
  | `(nanollvm_global| @$id:nanollvm_rawid = global $ty:nanollvm_type $init:nanollvm_exp $[, align $al:num]?) => do
    let idE ← elabNanoLlvmRawId id
    let tyE ← elabNanoLlvmType φ ty
    let (initE, _) ← elabNanoLlvmExp φ 0 init
    let expTy ← mkAppM ``Exp #[mkNatLit φ]
    let initOpt ← mkOptionExpr expTy (some initE)
    let alignOpt ← mkOptionExpr (mkConst ``Nat) (al.map fun a => mkNatLit a.getNat)
    mkAppOptM ``GlobalVariable.mk #[mkNatLit φ, idE, tyE, toExpr Bool.false, initOpt, alignOpt, mkNatLit 0]
  | `(nanollvm_global| @$id:nanollvm_rawid = constant $ty:nanollvm_type $init:nanollvm_exp $[, align $al:num]?) => do
    let idE ← elabNanoLlvmRawId id
    let tyE ← elabNanoLlvmType φ ty
    let (initE, _) ← elabNanoLlvmExp φ 0 init
    let expTy ← mkAppM ``Exp #[mkNatLit φ]
    let initOpt ← mkOptionExpr expTy (some initE)
    let alignOpt ← mkOptionExpr (mkConst ``Nat) (al.map fun a => mkNatLit a.getNat)
    mkAppOptM ``GlobalVariable.mk #[mkNatLit φ, idE, tyE, toExpr Bool.true, initOpt, alignOpt, mkNatLit 0]
  | _ => throwUnsupportedSyntax

elab "[llvm-" n:num "-global|" p:nanollvm_global "]" : term => elabNanoLlvmGlobal n.getNat p
elab "[llvm-global|" p:nanollvm_global "]" : term => elabNanoLlvmGlobal 0 p

declare_syntax_cat nanollvm_entity
scoped syntax nanollvm_global : nanollvm_entity
scoped syntax nanollvm_declaration : nanollvm_entity
scoped syntax nanollvm_definition : nanollvm_entity

def elabNanoLlvmEntity (φ : Nat) : Syntax → MetaM Expr
  | `(nanollvm_entity| $gv:nanollvm_global) => do
    let gv ← elabNanoLlvmGlobal φ gv
    mkAppOptM ``TopLevelEntity.global #[mkNatLit φ, gv]
  | `(nanollvm_entity| $decl:nanollvm_declaration) => do
    let decl ← elabNanoLlvmDeclaration φ decl
    mkAppOptM ``TopLevelEntity.declaration #[mkNatLit φ, decl]
  | `(nanollvm_entity| $defn:nanollvm_definition) => do
    let defn ← elabNanoLlvmDefinition φ defn
    mkAppOptM ``TopLevelEntity.definition #[mkNatLit φ, defn]
  | _ => throwUnsupportedSyntax

elab "[llvm-" n:num "-entity|" p:nanollvm_entity "]" : term => elabNanoLlvmEntity n.getNat p
elab "[llvm-entity|" p:nanollvm_entity "]" : term => elabNanoLlvmEntity 0 p

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
elab "[llvm|" ppLine p:nanollvm "]" : term => elabNanoLlvm 0 p

end LeanNanoLlvm.AST.Syntax
