import LeanNanoLlvm.AST.Resolve
import LeanNanoLlvm.Semantics.Exec

/-!
# Module initialization and top-level runners

`initModuleExec` lays out a module's globals and functions in memory (two passes, so
initializers may refer to any global), and `runModuleFunction` / `runDefinition` execute a
function of an initialized module with `runSteps`.
-/

namespace LeanNanoLlvm.Semantics

open AST

/-! ### Module Initialization & Top-Level Runners -/

mutual
private def collectAddrTakenExp : Exp → List GlobalId × List GlobalId
  | .identifier (.global_id gid) => ([gid], [])
  | .blockAddress fn blk => ([], [blockAddrKey fn blk])
  | .array es | .struct _ es | .vector es => collectAddrTakenTypedList es
  | .splat (_, e) => collectAddrTakenExp e
  | .gepConst _ _ (_, p) idxs =>
    let (f1, b1) := collectAddrTakenExp p
    let (f2, b2) := collectAddrTakenTypedList idxs
    (f1 ++ f2, b1 ++ b2)
  | .convConst _ _ e _ => collectAddrTakenExp e
  | .binConst _ _ e1 e2 =>
    let (f1, b1) := collectAddrTakenExp e1
    let (f2, b2) := collectAddrTakenExp e2
    (f1 ++ f2, b1 ++ b2)
  | .insertElemConst _ v _ e _ idx =>
    let (f1, b1) := collectAddrTakenExp v
    let (f2, b2) := collectAddrTakenExp e
    let (f3, b3) := collectAddrTakenExp idx
    (f1 ++ f2 ++ f3, b1 ++ b2 ++ b3)
  | .extractElemConst _ v _ idx =>
    let (f1, b1) := collectAddrTakenExp v
    let (f2, b2) := collectAddrTakenExp idx
    (f1 ++ f2, b1 ++ b2)
  | .shuffleVecConst _ v1 v2 _ =>
    let (f1, b1) := collectAddrTakenExp v1
    let (f2, b2) := collectAddrTakenExp v2
    (f1 ++ f2, b1 ++ b2)
  | _ => ([], [])

private def collectAddrTakenTypedList : List (LlvmType × Exp) → List GlobalId × List GlobalId
  | [] => ([], [])
  | (_, e) :: rest =>
    let (f1, b1) := collectAddrTakenExp e
    let (f2, b2) := collectAddrTakenTypedList rest
    (f1 ++ f2, b1 ++ b2)
end

private def collectAddrTakenInstr (fnTys : List (GlobalId × LlvmType)) :
    Instruction → List GlobalId × List GlobalId
  | .intBinaryOp _ _ e1 e2 | .floatBinaryOp _ _ e1 e2 | .icmp _ _ _ e1 e2 | .fcmp _ _ _ e1 e2 =>
    let (f1, b1) := collectAddrTakenExp e1; let (f2, b2) := collectAddrTakenExp e2; (f1 ++ f2, b1 ++ b2)
  | .floatUnaryOp _ _ e | .conversionOp _ _ e _ | .load _ _ e _ _ _ _ | .extractvalue _ e _ | .freeze (_, e) =>
    collectAddrTakenExp e
  | .select _ _ c _ tv fv =>
    let (f1, b1) := collectAddrTakenExp c; let (f2, b2) := collectAddrTakenExp tv; let (f3, b3) := collectAddrTakenExp fv
    (f1 ++ f2 ++ f3, b1 ++ b2 ++ b3)
  | .phi _ _ inc _ =>
    inc.foldl (init := ([], [])) fun (fs, bs) (e, _) =>
      let (f1, b1) := collectAddrTakenExp e; (fs ++ f1, bs ++ b1)
  | .alloca _ (some (_, e)) _ _ => collectAddrTakenExp e
  | .alloca _ none _ _ => ([], [])
  | .store _ v _ p _ _ | .insertvalue _ v _ p _ | .extractelement _ v _ p | .shufflevector _ v p _ | .bitextract _ _ v _ p =>
    let (f1, b1) := collectAddrTakenExp v; let (f2, b2) := collectAddrTakenExp p; (f1 ++ f2, b1 ++ b2)
  | .getelementptr _ _ _ p idxs =>
    let (f1, b1) := collectAddrTakenExp p; let (f2, b2) := collectAddrTakenTypedList idxs; (f1 ++ f2, b1 ++ b2)
  | .insertelement _ v _ e _ idx | .bitinsert _ v _ e _ idx =>
    let (f1, b1) := collectAddrTakenExp v; let (f2, b2) := collectAddrTakenExp e; let (f3, b3) := collectAddrTakenExp idx
    (f1 ++ f2 ++ f3, b1 ++ b2 ++ b3)
  | .call _ _ callee args _ bundles _ site =>
    -- A direct call `@f(...)` does NOT take the address of `@f`, unless the call's function type
    -- differs from `@f`'s: LLVM then calls through `@f` as a pointer (`getCalledFunction` is
    -- null), and llubi gives `@f` an address. Non-direct callees and arguments take addresses.
    let (fc, bc) := match callee with
      | .identifier (.global_id f) =>
        match site.fnTy?, (fnTys.find? (fun (p : GlobalId × LlvmType) => p.1 == f)).map (fun (p : GlobalId × LlvmType) => p.2) with
        | some ct, some ft => if ct.beq ft then ([], []) else ([f], [])
        | _, _ => ([], [])
      | other => collectAddrTakenExp other
    let (fa, ba) := args.foldl (init := (fc, bc)) fun (fs, bs) (_, e, _) =>
      let (f1, b1) := collectAddrTakenExp e; (fs ++ f1, bs ++ b1)
    bundles.foldl (init := (fa, ba)) fun (fs, bs) (_, bes) =>
      let (f1, b1) := collectAddrTakenTypedList bes; (fs ++ f1, bs ++ b1)

private def collectAddrTakenTerm : Terminator → List GlobalId × List GlobalId
  | .ret (_, e) | .condBr e _ _ | .switch _ e _ _ | .indirectBr e _ => collectAddrTakenExp e
  | _ => ([], [])

private def collectAddrTaken (ents : List TopLevelEntity) : List GlobalId × List GlobalId :=
  let fnTys : List (GlobalId × LlvmType) := ents.filterMap fun
    | .declaration d => some (d.name, d.type)
    | .definition d => some (d.prototype.name, d.prototype.type)
    | _ => none
  ents.foldl (init := ([], [])) fun (fs, bs) ent =>
    match ent with
    | .global gv =>
      match gv.initializer with
      | some e => let (f1, b1) := collectAddrTakenExp e; (fs ++ f1, bs ++ b1)
      | none => (fs, bs)
    | .definition defn =>
      defn.blocks.foldl (init := (fs, bs)) fun (fs1, bs1) blk =>
        let (fs2, bs2) := blk.code.foldl (init := (fs1, bs1)) fun (fa, ba) (_, ins) =>
          let (f1, b1) := collectAddrTakenInstr fnTys ins; (fa ++ f1, ba ++ b1)
        let (ft, bt) := collectAddrTakenTerm blk.terminator.2
        (fs2 ++ ft, bs2 ++ bt)
    | _ => (fs, bs)

private def registerBlockAddrs (dl : DataLayout) (cfg : SemanticsConfig)
    (takenBlks : List GlobalId) (fnName : FunctionId) :
    List Block → MemoryState → Except ExecError MemoryState
  | [], mem => .ok mem
  | blk :: rest, mem =>
    let key := blockAddrKey fnName blk.id
    if takenBlks.contains key then
      match mem.allocate dl cfg 0 1 key.toString dl.programAddrSpace .zeroed .func true with
      | .error e => .error e
      | .ok (obj, mem') =>
        let ptr := MemoryState.derivePointer dl obj
        registerBlockAddrs dl cfg takenBlks fnName rest (mem'.insertFuncAddr key obj.baseAddr ptr)
    else
      registerBlockAddrs dl cfg takenBlks fnName rest mem

private theorem registerBlockAddrs_wf {dl cfg takenBlks fnName blks mem mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : registerBlockAddrs dl cfg takenBlks fnName blks mem = .ok mem') :
    MemoryState.WellFormed mem' := by
  induction blks generalizing mem with
  | nil => unfold registerBlockAddrs at h; cases h; exact hwf
  | cons blk rest ih =>
    unfold registerBlockAddrs at h
    dsimp only at h
    split at h
    · cases ha : mem.allocate dl cfg 0 1 (blockAddrKey fnName blk.id).toString dl.programAddrSpace .zeroed .func true with
      | error e => rw [ha] at h; cases h
      | ok p =>
        rw [ha] at h; obtain ⟨obj, m1⟩ := p
        exact ih (MemoryState.insertFuncAddr_preserves_wf (MemoryState.allocate_preserves_wf hwf ha) _ _ _) h
    · exact ih hwf h

/-- Module-initialization order of `llubi::Context::initGlobalValues`: function (and block)
address objects for all functions first, then global variables. -/
def functionsFirst (ents : List TopLevelEntity) : List TopLevelEntity :=
  ents.filter (fun | .global _ => false | _ => true) ++ ents.filter (fun | .global _ => true | _ => false)

private def initModulePass1 (dl : DataLayout) (cfg : SemanticsConfig)
    (takenFns takenBlks : List GlobalId) :
    List TopLevelEntity → MemoryState → AssocMap FunctionId Definition → AssocMap FunctionId Declaration →
    Except ExecError (MemoryState × AssocMap FunctionId Definition × AssocMap FunctionId Declaration)
  | [], mem, fns, decls => .ok (mem, fns, decls)
  | ent :: rest, mem, fns, decls =>
    match ent with
    | .declaration decl =>
      if takenFns.contains decl.name then
        match mem.allocate dl cfg 0 1 decl.name.toString dl.programAddrSpace .zeroed .func true with
        | .error e => .error e
        | .ok (obj, mem') =>
          let ptr := MemoryState.derivePointer dl obj
          let mem'' := mem'.insertFuncAddr decl.name obj.baseAddr ptr
          initModulePass1 dl cfg takenFns takenBlks rest mem'' fns (decls.insert decl.name decl)
      else
        initModulePass1 dl cfg takenFns takenBlks rest mem fns (decls.insert decl.name decl)
    | .definition defn =>
      let afterFn : Except ExecError MemoryState :=
        if takenFns.contains defn.prototype.name then
          match mem.allocate dl cfg 0 1 defn.prototype.name.toString dl.programAddrSpace .zeroed .func true with
          | .error e => .error e
          | .ok (obj, mem') =>
            let ptr := MemoryState.derivePointer dl obj
            .ok (mem'.insertFuncAddr defn.prototype.name obj.baseAddr ptr)
        else .ok mem
      match afterFn with
      | .error e => .error e
      | .ok mem'' =>
        match registerBlockAddrs dl cfg takenBlks defn.prototype.name defn.blocks mem'' with
        | .error e => .error e
        | .ok mem''' => initModulePass1 dl cfg takenFns takenBlks rest mem''' (fns.insert defn.prototype.name defn) decls
    | .global gv =>
      let size := dl.typeAllocSize gv.ty
      let effAlign := dl.globalAlign gv.ty gv.align gv.initializer.isSome
      let initKind := if gv.initializer.isSome then MemInitKind.zeroed else MemInitKind.uninitialized
      match mem.allocate dl cfg size effAlign gv.name.toString gv.addrSpace initKind .global gv.isConstant with
      | .error e => .error e
      | .ok (obj, mem') =>
        let ptr := MemoryState.derivePointer dl obj
        let mem'' := mem'.insertGlobalAddr gv.name ptr
        initModulePass1 dl cfg takenFns takenBlks rest mem'' fns decls
    | .typeDef _ _ => initModulePass1 dl cfg takenFns takenBlks rest mem fns decls

private def initModulePass2 (dl : DataLayout) (cfg : SemanticsConfig) :
    List TopLevelEntity → MemoryState → OracleState →
    Except ExecError (MemoryState × OracleState)
  | [], mem, o => .ok (mem, o)
  | ent :: rest, mem, o =>
    match ent with
    | .global gv =>
      match gv.initializer with
      | none => initModulePass2 dl cfg rest mem o
      | some initExp =>
        match execExp dl cfg ∅ mem gv.ty initExp o with
        | .error e => .error e
        | .ok (initVal, m1, o1) =>
          let m2 := match m1.globalAddrs.get? gv.name with
            | some ptr =>
              match ptr.prov with
              | .concrete aid =>
                m1.writeObjectBytes aid 0 (valueToBytes dl cfg initVal gv.ty)
              | _ => m1
            | none => m1
          initModulePass2 dl cfg rest m2 (drawPtrTags initVal o1)
    | _ => initModulePass2 dl cfg rest mem o

/-- Initialize all globals, declarations, and function addresses for a `TopLevel` module. -/
def initModuleExec (mod : TopLevel) (cfg : SemanticsConfig := .modern)
    (dl : DataLayout := .default64LE) (oracle : OracleState := default) :
    Except ExecError (MemoryState × AssocMap FunctionId Definition × AssocMap FunctionId Declaration × OracleState) :=
  match mod.resolveTypes with
  | .error msg => .error (.staticError msg)
  | .ok resolvedMod =>
    let (takenFns, takenBlks) := collectAddrTaken resolvedMod.entities
    match initModulePass1 dl cfg takenFns takenBlks (functionsFirst resolvedMod.entities) {} ∅ ∅ with
    | .error e => .error e
    | .ok (mem1, fns, decls) =>
      match initModulePass2 dl cfg resolvedMod.entities mem1 oracle with
      | .error e => .error e
      | .ok (mem2, o2) => .ok (mem2, fns, decls, o2)

private theorem initModulePass1_wf {dl cfg takenFns takenBlks ents mem fns decls mem' fns' decls'}
    (hwf : MemoryState.WellFormed mem)
    (h : initModulePass1 dl cfg takenFns takenBlks ents mem fns decls = .ok (mem', fns', decls')) :
    MemoryState.WellFormed mem' := by
  induction ents generalizing mem fns decls with
  | nil => unfold initModulePass1 at h; cases h; exact hwf
  | cons ent rest ih =>
    unfold initModulePass1 at h
    cases ent with
    | declaration decl =>
      dsimp only at h
      split at h
      · cases ha : mem.allocate dl cfg 0 1 decl.name.toString dl.programAddrSpace .zeroed .func true with
        | error e => rw [ha] at h; cases h
        | ok p =>
          rw [ha] at h; obtain ⟨obj, m1⟩ := p
          exact ih (MemoryState.insertFuncAddr_preserves_wf (MemoryState.allocate_preserves_wf hwf ha) _ _ _) h
      · exact ih hwf h
    | definition defn =>
      dsimp only at h
      have hwfAfter : ∀ m2, ((if takenFns.contains defn.prototype.name then
            match mem.allocate dl cfg 0 1 defn.prototype.name.toString dl.programAddrSpace .zeroed .func true with
            | .error e => .error e
            | .ok (obj, mem') => .ok (mem'.insertFuncAddr defn.prototype.name obj.baseAddr (MemoryState.derivePointer dl obj))
          else .ok mem) : Except ExecError MemoryState) = .ok m2 → MemoryState.WellFormed m2 := by
        intro m2 hm2
        split at hm2
        · cases ha : mem.allocate dl cfg 0 1 defn.prototype.name.toString dl.programAddrSpace .zeroed .func true with
          | error e => rw [ha] at hm2; cases hm2
          | ok p =>
            rw [ha] at hm2; obtain ⟨obj, m1⟩ := p; cases hm2
            exact MemoryState.insertFuncAddr_preserves_wf (MemoryState.allocate_preserves_wf hwf ha) _ _ _
        · cases hm2; exact hwf
      split at h
      · cases h
      · rename_i m2 hm2
        have hwf1 := hwfAfter m2 hm2
        cases hb : registerBlockAddrs dl cfg takenBlks defn.prototype.name defn.blocks m2 with
        | error e => rw [hb] at h; cases h
        | ok m3 => rw [hb] at h; exact ih (registerBlockAddrs_wf hwf1 hb) h
    | global gv =>
      dsimp only at h
      cases ha : mem.allocate dl cfg (dl.typeAllocSize gv.ty) (dl.globalAlign gv.ty gv.align gv.initializer.isSome)
          gv.name.toString gv.addrSpace
          (if gv.initializer.isSome then MemInitKind.zeroed else MemInitKind.uninitialized)
          .global gv.isConstant with
      | error e => rw [ha] at h; cases h
      | ok p =>
        rw [ha] at h; obtain ⟨obj, m1⟩ := p
        exact ih (MemoryState.insertGlobalAddr_preserves_wf (MemoryState.allocate_preserves_wf hwf ha) _ _) h
    | typeDef _ _ => exact ih hwf h

private theorem initModulePass2_wf {dl cfg ents mem o mem' o'}
    (hwf : MemoryState.WellFormed mem)
    (h : initModulePass2 dl cfg ents mem o = .ok (mem', o')) :
    MemoryState.WellFormed mem' := by
  induction ents generalizing mem o with
  | nil => unfold initModulePass2 at h; cases h; exact hwf
  | cons ent rest ih =>
    unfold initModulePass2 at h
    cases ent with
    | global gv =>
      dsimp only at h
      cases hinit : gv.initializer with
      | none => rw [hinit] at h; exact ih hwf h
      | some initExp =>
        rw [hinit] at h; dsimp only at h
        have ihe := execExp_sound dl cfg ∅ mem gv.ty initExp o
        cases he : execExp dl cfg ∅ mem gv.ty initExp o with
        | error e => rw [he] at h; cases h
        | ok p =>
          rw [he] at ihe h; obtain ⟨initVal, m1, o1⟩ := p; dsimp only at ihe h
          have hwf1 := EvalExp.preserves_wf hwf ihe
          have hwf2 : MemoryState.WellFormed (match m1.globalAddrs.get? gv.name with
              | some ptr => match ptr.prov with
                | .concrete aid => m1.writeObjectBytes aid 0 (valueToBytes dl cfg initVal gv.ty)
                | _ => m1
              | none => m1) := by
            cases m1.globalAddrs.get? gv.name with
            | none => exact hwf1
            | some ptr =>
              dsimp only
              cases ptr.prov with
              | concrete aid => exact MemoryState.writeObjectBytes_preserves_wf hwf1 _ _ _
              | _ => exact hwf1
          exact ih hwf2 h
    | _ => dsimp only at h; exact ih hwf h

theorem initModuleExec_wf {mod cfg dl oracle mem fns decls o'}
    (h : initModuleExec mod cfg dl oracle = .ok (mem, fns, decls, o')) :
    MemoryState.WellFormed mem := by
  unfold initModuleExec at h
  cases hres : mod.resolveTypes with
  | error msg => rw [hres] at h; cases h
  | ok rmod =>
    rw [hres] at h; dsimp only at h
    cases h1 : initModulePass1 dl cfg (collectAddrTaken rmod.entities).1 (collectAddrTaken rmod.entities).2 (functionsFirst rmod.entities) {} ∅ ∅ with
    | error e => rw [h1] at h; cases h
    | ok p1 =>
      rw [h1] at h; obtain ⟨m1, fns1, decls1⟩ := p1; dsimp only at h
      have hwf1 := initModulePass1_wf MemoryState.empty_wf h1
      cases h2 : initModulePass2 dl cfg rmod.entities m1 oracle with
      | error e => rw [h2] at h; cases h
      | ok p2 => rw [h2] at h; obtain ⟨m2, o2⟩ := p2; cases h; exact initModulePass2_wf hwf1 h2

/-- Execute a `Definition`, returning the full `(trace, finalConfig, finalOracle)`. -/
def runDefinitionWithTrace (defn : Definition) (args : List RegisterValue := [])
    (cfg : SemanticsConfig := .modern) (dl : DataLayout := .default64LE)
    (oracle : OracleState := default) (initMem : MemoryState := {}) :
    List TraceEvent × Config × OracleState :=
  let initCfg := initCallConfig cfg dl initMem ∅ ∅ defn args
  runSteps cfg.maxSteps oracle initCfg

/-- Execute a `Definition` and extract its `Except ExecError RegisterValue` result. -/
def runDefinition (defn : Definition) (args : List RegisterValue := [])
    (cfg : SemanticsConfig := .modern) (dl : DataLayout := .default64LE)
    (oracle : OracleState := default) : Except ExecError RegisterValue :=
  (runDefinitionWithTrace defn args cfg dl oracle).2.1.toExcept

/-- Execute a named function inside a `TopLevel` module, returning `(trace, finalConfig, finalOracle)`. -/
def runModuleFunctionWithTrace (mod : TopLevel) (fnName : FunctionId)
    (args : List RegisterValue := []) (cfg : SemanticsConfig := .modern)
    (dl : DataLayout := .default64LE) (oracle : OracleState := default) :
    Except ExecError (List TraceEvent × Config × OracleState) :=
  match initModuleExec mod cfg dl oracle with
  | .error e => .error e
  | .ok (mem, fns, decls, o1) =>
    match fns.get? fnName with
    | none => .error (.staticError s!"Function @{fnName} not found in module")
    | some defn =>
      let initCfg := initCallConfig cfg dl mem fns decls defn args
      .ok (runSteps cfg.maxSteps o1 initCfg)

/-- Execute a named function inside a `TopLevel` module and extract its return value. -/
def runModuleFunction (mod : TopLevel) (fnName : FunctionId)
    (args : List RegisterValue := []) (cfg : SemanticsConfig := .modern)
    (dl : DataLayout := .default64LE) (oracle : OracleState := default) :
    Except ExecError RegisterValue :=
  match runModuleFunctionWithTrace mod fnName args cfg dl oracle with
  | .error e => .error e
  | .ok (_, finalCfg, _) => finalCfg.toExcept

/-- Execute a straight-line `Code` snippet in a fresh frame, returning final registers and memory. -/
def runCode (code : Code) (cfg : SemanticsConfig := .modern)
    (dl : DataLayout := .default64LE) (oracle : OracleState := default) :
    Except ExecError (AssocMap Identifier RegisterValue × MemoryState) :=
  let dummyDef : Definition := {
    prototype := { name := .name "__code__", type := .function .void [] false }
    args := []
    blocks := [{ id := .name "entry", code := code, terminator := (.void 0, .retVoid) }]
  }
  let initFrame : CallFrame := {
    defn := dummyDef
    curBlock := .name "entry"
    remainingCode := code
    terminator := (.void 0, .retVoid)
  }
  let initCfg : Config := .running {
    frames := [initFrame]
    memory := {}
    config := cfg
    dataLayout := dl
  }
  let (_, finalCfg, _) := runSteps code.length oracle initCfg
  match finalCfg with
  | .running st =>
    match st.frames with
    | f :: _ => .ok (f.registers, st.memory)
    | [] => .error (.staticError "Empty frame stack after runCode")
  | .halted _ mem => .ok (∅, mem)
  | .ub msg => .error (.immediateUB msg)
  | .staticError msg => .error (.staticError msg)
  | .resourceError e => .error e

end LeanNanoLlvm.Semantics
