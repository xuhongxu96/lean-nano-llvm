import LeanNanoLlvm.AST.AST

/-!
# Named type resolution

A module's `%T = type ...` definitions are substituted into every type that mentions `%T`,
so that the semantics only sees structural types. Resolution is bounded by a depth, which
also rejects cyclic definitions.
-/

namespace LeanNanoLlvm.AST

section TypeResolution

private def lookupTypeDef (defs : List (LocalId × LlvmType)) (nm : LocalId) : Option LlvmType :=
  (defs.find? (fun p => p.1 == nm)).map (·.2)

/-- Resolve all `LlvmType.named` references using `defs` (bounded depth prevents cyclic type loops). -/
def resolveType (defs : List (LocalId × LlvmType)) : Nat → LlvmType → Except String LlvmType
  | 0, .named nm => .error s!"Cyclic or overly deep named type %{nm}"
  | 0, ty => .ok ty
  | fuel + 1, ty =>
    match ty with
    | .int w => .ok (.int w)
    | .byte w => .ok (.byte w)
    | .float ft => .ok (.float ft)
    | .ptr as => .ok (.ptr as)
    | .named nm =>
      match lookupTypeDef defs nm with
      | some body => resolveType defs fuel body
      | none => .error s!"Undefined named type %{nm}"
    | .vector n elem => do .ok (.vector n (← resolveType defs fuel elem))
    | .array n elem => do .ok (.array n (← resolveType defs fuel elem))
    | .struct packed fs => do
      let fs' ← fs.mapM (resolveType defs fuel)
      .ok (.struct packed fs')
    | .function ret args isVarArg => do
      let ret' ← match ret with
        | .void => .ok .void
        | .ret r => do .ok (.ret (← resolveType defs fuel r))
      let args' ← args.mapM (resolveType defs fuel)
      .ok (.function ret' args' isVarArg)

private def resolveRetType (defs : List (LocalId × LlvmType)) (fuel : Nat) :
    LlvmRetType → Except String LlvmRetType
  | .void => .ok .void
  | .ret ty => do .ok (.ret (← resolveType defs fuel ty))

private def resolveAttr (defs : List (LocalId × LlvmType)) (fuel : Nat) :
    ValueAttr → Except String ValueAttr
  | .byval ty => do .ok (.byval (← resolveType defs fuel ty))
  | .sret ty => do .ok (.sret (← resolveType defs fuel ty))
  | a => .ok a

mutual
private def resolveExp (defs : List (LocalId × LlvmType)) (fuel : Nat) :
    Exp → Except String Exp
  | .array es => do .ok (.array (← resolveTypedExpList defs fuel es))
  | .struct p es => do .ok (.struct p (← resolveTypedExpList defs fuel es))
  | .vector es => do .ok (.vector (← resolveTypedExpList defs fuel es))
  | .splat (t, e) => do .ok (.splat (← resolveType defs fuel t, ← resolveExp defs fuel e))
  | .gepConst fl bTy (pTy, pE) idxs => do
    let bTy' ← resolveType defs fuel bTy
    let pTy' ← resolveType defs fuel pTy
    let pE' ← resolveExp defs fuel pE
    let idxs' ← resolveTypedExpList defs fuel idxs
    .ok (.gepConst fl bTy' (pTy', pE') idxs')
  | .convConst op fTy e tTy => do
    .ok (.convConst op (← resolveType defs fuel fTy) (← resolveExp defs fuel e) (← resolveType defs fuel tTy))
  | .binConst op ty e1 e2 => do
    .ok (.binConst op (← resolveType defs fuel ty) (← resolveExp defs fuel e1) (← resolveExp defs fuel e2))
  | .insertElemConst vecTy vec elemTy elem idxTy idx => do
    .ok (.insertElemConst (← resolveType defs fuel vecTy) (← resolveExp defs fuel vec)
      (← resolveType defs fuel elemTy) (← resolveExp defs fuel elem)
      (← resolveType defs fuel idxTy) (← resolveExp defs fuel idx))
  | .extractElemConst vecTy vec idxTy idx => do
    .ok (.extractElemConst (← resolveType defs fuel vecTy) (← resolveExp defs fuel vec)
      (← resolveType defs fuel idxTy) (← resolveExp defs fuel idx))
  | .shuffleVecConst vecTy v1 v2 mask => do
    .ok (.shuffleVecConst (← resolveType defs fuel vecTy) (← resolveExp defs fuel v1)
      (← resolveExp defs fuel v2) mask)
  | e => .ok e

private def resolveTypedExpList (defs : List (LocalId × LlvmType)) (fuel : Nat) :
    List (LlvmType × Exp) → Except String (List (LlvmType × Exp))
  | [] => .ok []
  | (t, e) :: rest => do
    let t' ← resolveType defs fuel t
    let e' ← resolveExp defs fuel e
    let rest' ← resolveTypedExpList defs fuel rest
    .ok ((t', e') :: rest')
end

private def resolveInstr (defs : List (LocalId × LlvmType)) (fuel : Nat) :
    Instruction → Except String Instruction
  | .intBinaryOp op t e1 e2 => do .ok (.intBinaryOp op (← resolveType defs fuel t) (← resolveExp defs fuel e1) (← resolveExp defs fuel e2))
  | .floatUnaryOp op t e => do .ok (.floatUnaryOp op (← resolveType defs fuel t) (← resolveExp defs fuel e))
  | .floatBinaryOp op t e1 e2 => do .ok (.floatBinaryOp op (← resolveType defs fuel t) (← resolveExp defs fuel e1) (← resolveExp defs fuel e2))
  | .icmp ss pr t e1 e2 => do .ok (.icmp ss pr (← resolveType defs fuel t) (← resolveExp defs fuel e1) (← resolveExp defs fuel e2))
  | .fcmp fmf pr t e1 e2 => do .ok (.fcmp fmf pr (← resolveType defs fuel t) (← resolveExp defs fuel e1) (← resolveExp defs fuel e2))
  | .conversionOp op fTy e tTy => do .ok (.conversionOp op (← resolveType defs fuel fTy) (← resolveExp defs fuel e) (← resolveType defs fuel tTy))
  | .select fmf cTy c vTy tv fv => do .ok (.select fmf (← resolveType defs fuel cTy) (← resolveExp defs fuel c) (← resolveType defs fuel vTy) (← resolveExp defs fuel tv) (← resolveExp defs fuel fv))
  | .phi ty fmf inc md => do
    let ty' ← resolveType defs fuel ty
    let inc' ← inc.mapM fun (e, b) => do .ok (← resolveExp defs fuel e, b)
    let md' ← md.mapM (resolveAttr defs fuel)
    .ok (.phi ty' fmf inc' md')
  | .alloca aTy cnt? al as => do
    let aTy' ← resolveType defs fuel aTy
    let cnt?' ← match cnt? with
      | none => .ok none
      | some (t, e) => do .ok (some (← resolveType defs fuel t, ← resolveExp defs fuel e))
    .ok (.alloca aTy' cnt?' al as)
  | .load ty pTy p al vol nu md => do
    let ty' ← resolveType defs fuel ty
    let pTy' ← resolveType defs fuel pTy
    let p' ← resolveExp defs fuel p
    let md' ← md.mapM (resolveAttr defs fuel)
    .ok (.load ty' pTy' p' al vol nu md')
  | .store vTy v pTy p al vol => do
    .ok (.store (← resolveType defs fuel vTy) (← resolveExp defs fuel v) (← resolveType defs fuel pTy) (← resolveExp defs fuel p) al vol)
  | .getelementptr fl bTy pTy p idxs => do
    let bTy' ← resolveType defs fuel bTy
    let pTy' ← resolveType defs fuel pTy
    let p' ← resolveExp defs fuel p
    let idxs' ← idxs.mapM fun (t, e) => do .ok (← resolveType defs fuel t, ← resolveExp defs fuel e)
    .ok (.getelementptr fl bTy' pTy' p' idxs')
  | .extractvalue aTy a idxs => do .ok (.extractvalue (← resolveType defs fuel aTy) (← resolveExp defs fuel a) idxs)
  | .insertvalue aTy a vTy v idxs => do .ok (.insertvalue (← resolveType defs fuel aTy) (← resolveExp defs fuel a) (← resolveType defs fuel vTy) (← resolveExp defs fuel v) idxs)
  | .extractelement vTy v iTy i => do .ok (.extractelement (← resolveType defs fuel vTy) (← resolveExp defs fuel v) (← resolveType defs fuel iTy) (← resolveExp defs fuel i))
  | .insertelement vTy v valTy val iTy i => do .ok (.insertelement (← resolveType defs fuel vTy) (← resolveExp defs fuel v) (← resolveType defs fuel valTy) (← resolveExp defs fuel val) (← resolveType defs fuel iTy) (← resolveExp defs fuel i))
  | .shufflevector vTy v1 v2 m => do .ok (.shufflevector (← resolveType defs fuel vTy) (← resolveExp defs fuel v1) (← resolveExp defs fuel v2) m)
  | .call rTy fmf callee args retAttrs bundles isNoRet site => do
    let rTy' ← resolveRetType defs fuel rTy
    let callee' ← resolveExp defs fuel callee
    let args' ← args.mapM fun (t, e, as) => do
      .ok (← resolveType defs fuel t, ← resolveExp defs fuel e, ← as.mapM (resolveAttr defs fuel))
    let retAttrs' ← retAttrs.mapM (resolveAttr defs fuel)
    let bundles' ← bundles.mapM fun (tag, bargs) => do
      let bargs' ← bargs.mapM fun (t, e) => do .ok (← resolveType defs fuel t, ← resolveExp defs fuel e)
      .ok (tag, bargs')
    .ok (.call rTy' fmf callee' args' retAttrs' bundles' isNoRet site)
  | .freeze (t, e) => do .ok (.freeze (← resolveType defs fuel t, ← resolveExp defs fuel e))
  | .bitinsert bTy b vTy v oTy o => do
    .ok (.bitinsert (← resolveType defs fuel bTy) (← resolveExp defs fuel b)
      (← resolveType defs fuel vTy) (← resolveExp defs fuel v)
      (← resolveType defs fuel oTy) (← resolveExp defs fuel o))
  | .bitextract rTy sTy s oTy o => do
    .ok (.bitextract (← resolveType defs fuel rTy) (← resolveType defs fuel sTy) (← resolveExp defs fuel s)
      (← resolveType defs fuel oTy) (← resolveExp defs fuel o))

private def resolveTerm (defs : List (LocalId × LlvmType)) (fuel : Nat) :
    Terminator → Except String Terminator
  | .retVoid => .ok .retVoid
  | .ret (t, e) => do .ok (.ret (← resolveType defs fuel t, ← resolveExp defs fuel e))
  | .br d => .ok (.br d)
  | .condBr c t f => do .ok (.condBr (← resolveExp defs fuel c) t f)
  | .switch ty c d cs => do .ok (.switch (← resolveType defs fuel ty) (← resolveExp defs fuel c) d cs)
  | .indirectBr a ds => do .ok (.indirectBr (← resolveExp defs fuel a) ds)
  | .unreachable => .ok .unreachable

private def resolveDecl (defs : List (LocalId × LlvmType)) (fuel : Nat) (d : Declaration) :
    Except String Declaration := do
  let ty' ← resolveType defs fuel d.type
  let argAttrs' ← d.argAttrs.mapM (fun as => as.mapM (resolveAttr defs fuel))
  let retAttrs' ← d.retAttrs.mapM (resolveAttr defs fuel)
  .ok { d with type := ty', argAttrs := argAttrs', retAttrs := retAttrs' }

/-- Resolve all named struct types (`%T = type { ... }`) in a `TopLevel` module. -/
def TopLevel.resolveTypes (m : TopLevel) (maxDepth : Nat := 64) : Except String TopLevel := do
  let defs : List (LocalId × LlvmType) := m.entities.filterMap fun
    | .typeDef nm ty => some (nm, ty)
    | _ => none
  let mut out : List TopLevelEntity := []
  for ent in m.entities do
    match ent with
    | .typeDef _ _ => pure ()
    | .global gv =>
      let ty' ← resolveType defs maxDepth gv.ty
      let init' ← match gv.initializer with
        | none => .ok none
        | some e => do .ok (some (← resolveExp defs maxDepth e))
      out := out ++ [.global { gv with ty := ty', initializer := init' }]
    | .declaration decl =>
      out := out ++ [.declaration (← resolveDecl defs maxDepth decl)]
    | .definition defn =>
      let proto' ← resolveDecl defs maxDepth defn.prototype
      let blocks' ← defn.blocks.mapM fun blk => do
        let code' ← blk.code.mapM fun (iid, ins) => do .ok (iid, ← resolveInstr defs maxDepth ins)
        let term' ← resolveTerm defs maxDepth blk.terminator.2
        .ok { blk with code := code', terminator := (blk.terminator.1, term') }
      out := out ++ [.definition { defn with prototype := proto', blocks := blocks' }]
  .ok ⟨out⟩

end TypeResolution

end LeanNanoLlvm.AST
