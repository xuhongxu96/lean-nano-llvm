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
  | `(nanollvm_type| void) => mkAppM ``LlvmRetType.void #[]
  | stx => do
    let ty ← elabNanoLlvmType φ stx
    mkAppM ``LlvmRetType.ret #[ty]
end

end LeanNanoLlvm.AST.Syntax
