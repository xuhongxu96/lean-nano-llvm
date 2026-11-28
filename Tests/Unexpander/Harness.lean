import Lean
import LeanNanoLlvm.AST

/-!
# Unexpander Tests

Verifies `LeanNanoLlvm.AST.Unexpander` with two complementary checks:
1. **Round-trip property tests** (`#test_unexpand` and `#test_unexpand_ll_file`):
   pretty-print an AST `Expr` via `PrettyPrinter.ppExpr`, assert that no macro-hygiene
   daggers (`✝`) or raw AST constructor names leak, re-parse and re-elaborate the
   pretty-printed Lean term, and assert definitional equality with the original AST
   (canonicalizing synthetic `InstructionId.void` counters and default-padded fields for
   externally parsed `.ll` files).
2. **Formatting snapshots** (`#guard_msgs`): lock down whitespace, indentation, and
   hygiene for representative constructs.
-/

namespace Tests.Unexpander

open Lean Elab Command Term Meta PrettyPrinter
open LeanNanoLlvm.AST

/-! ### Test Harness -/

private def leakedSubstrings : List String := [
  "✝",
  "LeanNanoLlvm.AST.",
  "RawId.",
  "Identifier.",
  "InstructionId.",
  "LlvmType.",
  "LlvmRetType.",
  "FloatType.",
  "FastMathFlags.",
  "GEPFlags.",
  "ICmpPred.",
  "FCmpPred.",
  "IntBinaryOp.",
  "FloatUnaryOp.",
  "FloatBinaryOp.",
  "ConversionOp.",
  "ValueAttr.",
  "Exp.",
  "CallSiteInfo.",
  "Instruction.",
  "Terminator.",
  "Declaration.",
  "Block.",
  "Definition.",
  "GlobalVariable.",
  "TopLevelEntity.",
  "TopLevel.",
  "DenormalMode.",
  "DenormalModeKind."
]

private def checkNoLeaks (rendered : String) : Except String Unit := do
  for needle in leakedSubstrings do
    if (rendered.splitOn needle).length > 1 then
      throw s!"Unexpander leaked '{needle}' in:\n{rendered}"
  pure ()

private def normalizeVoidIds (e : Expr) : Expr :=
  e.replace fun sub =>
    if sub.isAppOfArity ``InstructionId.void 1 then
      some (mkApp (mkConst ``InstructionId.void) (mkNatLit 0))
    else
      none

private def canonicalizeGEPFlags (f : GEPFlags) : GEPFlags :=
  if f.inbounds then { f with nusw := true } else f

mutual
  private def canonicalizeExp : Exp → Exp
    | .array elems => .array (canonicalizeExpList elems)
    | .struct p elems => .struct p (canonicalizeExpList elems)
    | .vector elems => .vector (canonicalizeExpList elems)
    | .splat (t, e) => .splat (t, canonicalizeExp e)
    | .gepConst fl bTy (pTy, pExp) idxs =>
      .gepConst (canonicalizeGEPFlags fl) bTy (pTy, canonicalizeExp pExp)
        (canonicalizeExpList idxs)
    | .convConst op fTy v tTy => .convConst op fTy (canonicalizeExp v) tTy
    | .binConst op ty v1 v2 => .binConst op ty (canonicalizeExp v1) (canonicalizeExp v2)
    | .insertElemConst vTy v eTy e iTy i =>
      .insertElemConst vTy (canonicalizeExp v) eTy (canonicalizeExp e) iTy (canonicalizeExp i)
    | .extractElemConst vTy v iTy i =>
      .extractElemConst vTy (canonicalizeExp v) iTy (canonicalizeExp i)
    | .shuffleVecConst vTy v1 v2 m =>
      .shuffleVecConst vTy (canonicalizeExp v1) (canonicalizeExp v2) m
    | other => other

  private def canonicalizeExpList : List (LlvmType × Exp) → List (LlvmType × Exp)
    | [] => []
    | (t, e) :: rest => (t, canonicalizeExp e) :: canonicalizeExpList rest
end

private def canonicalizeInstruction : Instruction → Instruction
  | .intBinaryOp op t v1 v2 => .intBinaryOp op t (canonicalizeExp v1) (canonicalizeExp v2)
  | .floatUnaryOp op t v => .floatUnaryOp op t (canonicalizeExp v)
  | .floatBinaryOp op t v1 v2 => .floatBinaryOp op t (canonicalizeExp v1) (canonicalizeExp v2)
  | .icmp ss p t v1 v2 => .icmp ss p t (canonicalizeExp v1) (canonicalizeExp v2)
  | .fcmp fmf p t v1 v2 => .fcmp fmf p t (canonicalizeExp v1) (canonicalizeExp v2)
  | .conversionOp op fTy v tTy => .conversionOp op fTy (canonicalizeExp v) tTy
  | .select fmf cTy c vTy tv fv =>
    .select fmf cTy (canonicalizeExp c) vTy (canonicalizeExp tv) (canonicalizeExp fv)
  | .phi ty fmf incs md =>
    .phi ty fmf (incs.map fun (e, b) => (canonicalizeExp e, b)) md
  | .alloca ty numEl al as =>
    .alloca ty (numEl.map fun (t, e) => (t, canonicalizeExp e)) al as
  | .load ty pTy p al vol nu md =>
    .load ty pTy (canonicalizeExp p) al vol nu md
  | .store vTy v pTy p al vol =>
    .store vTy (canonicalizeExp v) pTy (canonicalizeExp p) al vol
  | .getelementptr fl bTy pTy p idxs =>
    .getelementptr (canonicalizeGEPFlags fl) bTy pTy (canonicalizeExp p)
      (idxs.map fun (t, e) => (t, canonicalizeExp e))
  | .extractvalue aTy a idxs => .extractvalue aTy (canonicalizeExp a) idxs
  | .insertvalue aTy a vTy v idxs =>
    .insertvalue aTy (canonicalizeExp a) vTy (canonicalizeExp v) idxs
  | .extractelement vTy v iTy i =>
    .extractelement vTy (canonicalizeExp v) iTy (canonicalizeExp i)
  | .insertelement vTy v valTy val iTy i =>
    .insertelement vTy (canonicalizeExp v) valTy (canonicalizeExp val) iTy (canonicalizeExp i)
  | .shufflevector vTy v1 v2 m =>
    .shufflevector vTy (canonicalizeExp v1) (canonicalizeExp v2) m
  | .call retTy fmf callee args retAttrs bundles nr site =>
    .call retTy fmf (canonicalizeExp callee)
      (args.map fun (t, e, a) => (t, canonicalizeExp e, a))
      retAttrs
      (bundles.map fun (tag, tes) => (tag, tes.map fun (t, e) => (t, canonicalizeExp e)))
      -- the call's function type (`CallSiteInfo.fnTy?`) is recorded by the syntax as by the IR
      -- parser (printed when variadic, inferred from the arguments otherwise)
      nr site
  | .freeze (t, v) => .freeze (t, canonicalizeExp v)
  | .bitinsert bTy b vTy v oTy o =>
    .bitinsert bTy (canonicalizeExp b) vTy (canonicalizeExp v) oTy (canonicalizeExp o)
  | .bitextract rTy sTy s oTy o =>
    .bitextract rTy sTy (canonicalizeExp s) oTy (canonicalizeExp o)

private def canonicalizeTerminator : Terminator → Terminator
  | .ret (t, v) => .ret (t, canonicalizeExp v)
  | .condBr c t f => .condBr (canonicalizeExp c) t f
  | .switch ty c d cs => .switch ty (canonicalizeExp c) d cs
  | .indirectBr a ds => .indirectBr (canonicalizeExp a) ds
  | other => other

private def canonicalizeInstrId : InstructionId → InstructionId
  | .void _ => .void 0
  | other => other

private def canonicalizeBlock (b : Block) : Block :=
  { b with
    code := b.code.map fun (iid, instr) => (canonicalizeInstrId iid, canonicalizeInstruction instr)
    terminator := (canonicalizeInstrId b.terminator.1, canonicalizeTerminator b.terminator.2) }

private def canonicalizeDeclaration (d : LeanNanoLlvm.AST.Declaration) : LeanNanoLlvm.AST.Declaration :=
  let nArgs := match d.type with
    | .function _ args _ => args.length
    | _ => d.argAttrs.length
  let padded := (List.range nArgs).map fun i => d.argAttrs.getD i []
  { d with argAttrs := padded }

private def canonicalizeGlobal (g : GlobalVariable) : GlobalVariable :=
  { g with initializer := g.initializer.map canonicalizeExp }

private def canonicalizeTopLevel (tl : TopLevel) : TopLevel :=
  ⟨tl.entities.map fun
    | .typeDef nm ty => .typeDef nm ty
    | .global gv => .global (canonicalizeGlobal gv)
    | .declaration d => .declaration (canonicalizeDeclaration d)
    | .definition defn =>
      .definition { defn with
        prototype := canonicalizeDeclaration defn.prototype
        blocks := defn.blocks.map canonicalizeBlock }⟩

private def roundTripExpr (origExpr : Expr) (expectedTy? : Option Expr) (canonVoid : Bool)
    (tag : String) : TermElabM Unit := do
  let fmt ← PrettyPrinter.ppExpr origExpr
  let rendered := fmt.pretty 120
  match checkNoLeaks rendered with
  | .error msg => throwError "[{tag}] {msg}"
  | .ok () => pure ()
  let env ← getEnv
  let wrapped := s!"open scoped LeanNanoLlvm.AST.Syntax in\n{rendered}"
  match Lean.Parser.runParserCategory env `term wrapped s!"<{tag}>" with
  | .error parseErr =>
    throwError "[{tag}] Failed to re-parse unexpanded output:\n{rendered}\nParse error: {parseErr}"
  | .ok stx =>
    let reElab ← elabTerm stx expectedTy?
    synthesizeSyntheticMVarsNoPostponing
    let reElab ← instantiateMVars reElab
    let lhs := if canonVoid then normalizeVoidIds origExpr else origExpr
    let rhs := if canonVoid then normalizeVoidIds reElab else reElab
    unless ← isDefEq lhs rhs do
      throwError "[{tag}] Round-trip AST mismatch!\nUnexpanded:\n{rendered}\nOriginal: {lhs}\nRe-elaborated: {rhs}"

elab "#test_unexpand " t:term : command =>
  liftTermElabM do
    let e ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let ty ← inferType e
    roundTripExpr e (some ty) false "test_unexpand"

elab "#test_unexpand_canon " t:term : command =>
  liftTermElabM do
    let e ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let ty ← inferType e
    roundTripExpr e (some ty) true "test_unexpand_canon"

elab "#test_unexpand_ll_file " path:str : command =>
  liftTermElabM do
    let p := path.getString
    let content ← IO.FS.readFile p
    match LeanNanoLlvm.AST.Parser.parseLlvmModule content with
    | .error err => throwError "[{p}] Parser error: {err}"
    | .ok parsed =>
      let canon := canonicalizeTopLevel parsed.topLevel
      let e := toExpr canon
      roundTripExpr e (some (mkConst ``TopLevel)) true p

end Tests.Unexpander
