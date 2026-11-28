import LeanNanoLlvm.Util.Config
import LeanNanoLlvm.Util.AssocMap
import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.DataLayout
import LeanNanoLlvm.AST.Print
import LeanNanoLlvm.Semantics.Memory
import LeanNanoLlvm.Semantics.Operations

namespace LeanNanoLlvm.Semantics

open AST

/-! ### Observable Events & Trace Refinement -/

/-- Observable machine events emitted by small-step transitions (volatile I/O, external calls). -/
inductive TraceEvent : Type where
  | volatileLoad  (addrSpace : Nat) (addr : Nat) (bytes : Array MemByte)
  | volatileStore (addrSpace : Nat) (addr : Nat) (bytes : Array MemByte)
  | externalCall  (name : String) (args : List RegisterValue)
deriving DecidableEq

/-- Byte-array refinement under a `MemoryInjection` (equal length, pointwise `MemByte.IsRefinedBy`). -/
def ByteArrayIsRefinedBy (inj : MemoryInjection) (bsX bsY : Array MemByte) : Prop :=
  bsX.size = bsY.size ∧
  ∀ i < bsX.size, MemByte.IsRefinedBy inj (bsX.getD i MemByte.poison) (bsY.getD i MemByte.poison)

theorem ByteArrayIsRefinedBy.refl (bs : Array MemByte) : ByteArrayIsRefinedBy .id bs bs :=
  ⟨rfl, fun _ _ => MemByte.IsRefinedBy.refl _⟩

theorem ByteArrayIsRefinedBy.mono {f g : MemoryInjection} {b1 b2 : Array MemByte}
    (hext : f.Extends g) (h : ByteArrayIsRefinedBy f b1 b2) :
    ByteArrayIsRefinedBy g b1 b2 :=
  ⟨h.1, fun i hi => MemByte.IsRefinedBy.mono hext (h.2 i hi)⟩

theorem ByteArrayIsRefinedBy.trans {f g : MemoryInjection} {b1 b2 b3 : Array MemByte}
    (h12 : ByteArrayIsRefinedBy f b1 b2) (h23 : ByteArrayIsRefinedBy g b2 b3) :
    ByteArrayIsRefinedBy (f.comp g) b1 b3 :=
  ⟨h12.1.trans h23.1, fun i hi => MemByte.IsRefinedBy.trans (h12.2 i hi) (h23.2 i (by rw [← h12.1]; exact hi))⟩

/-- Observable event refinement under a `MemoryInjection`. -/
def TraceEvent.IsRefinedBy (inj : MemoryInjection) : TraceEvent → TraceEvent → Prop
  | .volatileLoad asX addrX bsX, .volatileLoad asY addrY bsY =>
      asX = asY ∧ addrX = addrY ∧ ByteArrayIsRefinedBy inj bsX bsY
  | .volatileStore asX addrX bsX, .volatileStore asY addrY bsY =>
      asX = asY ∧ addrX = addrY ∧ ByteArrayIsRefinedBy inj bsX bsY
  | .externalCall nX argsX, .externalCall nY argsY =>
      nX = nY ∧ RegisterValue.IsRefinedByList inj argsX argsY
  | _, _ => False

theorem TraceEvent.IsRefinedBy.refl : ∀ (e : TraceEvent), TraceEvent.IsRefinedBy .id e e
  | .volatileLoad _ _ bs => ⟨rfl, rfl, ByteArrayIsRefinedBy.refl bs⟩
  | .volatileStore _ _ bs => ⟨rfl, rfl, ByteArrayIsRefinedBy.refl bs⟩
  | .externalCall _ args => ⟨rfl, RegisterValue.IsRefinedByList.refl args⟩

theorem TraceEvent.IsRefinedBy.mono {f g : MemoryInjection} (hext : f.Extends g) :
    ∀ {e1 e2 : TraceEvent}, TraceEvent.IsRefinedBy f e1 e2 → TraceEvent.IsRefinedBy g e1 e2
  | .volatileLoad _ _ _, .volatileLoad _ _ _, h => ⟨h.1, h.2.1, ByteArrayIsRefinedBy.mono hext h.2.2⟩
  | .volatileStore _ _ _, .volatileStore _ _ _, h => ⟨h.1, h.2.1, ByteArrayIsRefinedBy.mono hext h.2.2⟩
  | .externalCall _ _, .externalCall _ _, h => ⟨h.1, RegisterValue.IsRefinedByList.mono hext h.2⟩
  | .volatileLoad .., .volatileStore .., h
  | .volatileLoad .., .externalCall .., h
  | .volatileStore .., .volatileLoad .., h
  | .volatileStore .., .externalCall .., h
  | .externalCall .., .volatileLoad .., h
  | .externalCall .., .volatileStore .., h => False.elim h

theorem TraceEvent.IsRefinedBy.trans {f g : MemoryInjection} :
    ∀ {e1 e2 e3 : TraceEvent},
      TraceEvent.IsRefinedBy f e1 e2 → TraceEvent.IsRefinedBy g e2 e3 →
      TraceEvent.IsRefinedBy (f.comp g) e1 e3
  | .volatileLoad _ _ _, .volatileLoad _ _ _, .volatileLoad _ _ _, h12, h23 =>
      ⟨h12.1.trans h23.1, h12.2.1.trans h23.2.1, ByteArrayIsRefinedBy.trans h12.2.2 h23.2.2⟩
  | .volatileStore _ _ _, .volatileStore _ _ _, .volatileStore _ _ _, h12, h23 =>
      ⟨h12.1.trans h23.1, h12.2.1.trans h23.2.1, ByteArrayIsRefinedBy.trans h12.2.2 h23.2.2⟩
  | .externalCall _ _, .externalCall _ _, .externalCall _ _, h12, h23 =>
      ⟨h12.1.trans h23.1, RegisterValue.IsRefinedByList.trans h12.2 h23.2⟩
  | .volatileLoad .., .volatileStore .., _, h12, _
  | .volatileLoad .., .externalCall .., _, h12, _
  | .volatileStore .., .volatileLoad .., _, h12, _
  | .volatileStore .., .externalCall .., _, h12, _
  | .externalCall .., .volatileLoad .., _, h12, _
  | .externalCall .., .volatileStore .., _, h12, _ => False.elim h12
  | .volatileLoad .., .volatileLoad .., .volatileStore .., _, h23
  | .volatileLoad .., .volatileLoad .., .externalCall .., _, h23
  | .volatileStore .., .volatileStore .., .volatileLoad .., _, h23
  | .volatileStore .., .volatileStore .., .externalCall .., _, h23
  | .externalCall .., .externalCall .., .volatileLoad .., _, h23
  | .externalCall .., .externalCall .., .volatileStore .., _, h23 => False.elim h23

/-- Trace (event-list) refinement under a `MemoryInjection`. -/
def Trace.IsRefinedBy (inj : MemoryInjection) : List TraceEvent → List TraceEvent → Prop
  | [], [] => True
  | eX :: restX, eY :: restY => TraceEvent.IsRefinedBy inj eX eY ∧ Trace.IsRefinedBy inj restX restY
  | _, _ => False

theorem Trace.IsRefinedBy.refl : ∀ (tr : List TraceEvent), Trace.IsRefinedBy .id tr tr
  | [] => trivial
  | e :: rest => ⟨TraceEvent.IsRefinedBy.refl e, Trace.IsRefinedBy.refl rest⟩

theorem Trace.IsRefinedBy.mono {f g : MemoryInjection} (hext : f.Extends g) :
    ∀ {t1 t2 : List TraceEvent}, Trace.IsRefinedBy f t1 t2 → Trace.IsRefinedBy g t1 t2
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => ⟨TraceEvent.IsRefinedBy.mono hext h.1, Trace.IsRefinedBy.mono hext h.2⟩
  | [], _ :: _, h | _ :: _, [], h => False.elim h

theorem Trace.IsRefinedBy.append {inj : MemoryInjection} :
    ∀ {a1 a2 b1 b2 : List TraceEvent},
      Trace.IsRefinedBy inj a1 a2 → Trace.IsRefinedBy inj b1 b2 →
      Trace.IsRefinedBy inj (a1 ++ b1) (a2 ++ b2)
  | [], [], _, _, _, hb => hb
  | _ :: _, _ :: _, _, _, ha, hb => ⟨ha.1, Trace.IsRefinedBy.append ha.2 hb⟩
  | [], _ :: _, _, _, ha, _ | _ :: _, [], _, _, ha, _ => False.elim ha

theorem Trace.IsRefinedBy.trans {f g : MemoryInjection} :
    ∀ {t1 t2 t3 : List TraceEvent},
      Trace.IsRefinedBy f t1 t2 → Trace.IsRefinedBy g t2 t3 → Trace.IsRefinedBy (f.comp g) t1 t3
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, h12, h23 =>
      ⟨TraceEvent.IsRefinedBy.trans h12.1 h23.1, Trace.IsRefinedBy.trans h12.2 h23.2⟩
  | [], _ :: _, _, h12, _ | _ :: _, [], _, h12, _ => False.elim h12
  | [], [], _ :: _, _, h23 | _ :: _, _ :: _, [], _, h23 => False.elim h23

/-! ### Explicit Small-Step Call Frame & Abstract Machine State -/

/-- Return continuation recorded in a caller's frame when awaiting a callee return. -/
structure ReturnDest : Type where
  destId     : InstructionId
  retTy      : LlvmRetType
  fmf        : FastMathFlags := {}
  retAttrs   : List ValueAttr := []
  isNoReturn : Bool := false
  specLoad?  : Option (RegisterValue × RegisterValue) := none
  /-- The caller's stack objects made inaccessible by a `tail` call (restored on return). -/
  hidden     : List AllocId := []

/-- Explicit activation record on the small-step call stack (mirrors `llubi::Frame`). -/
structure CallFrame : Type where
  defn          : Definition
  curBlock      : BlockId
  remainingCode : Code
  terminator    : InstructionId × Terminator
  registers     : AssocMap Identifier RegisterValue := ∅
  frameAllocas  : List AllocId := []
  returnDest?   : Option ReturnDest := none

namespace CallFrame

/-- Advance `remainingCode` after executing one instruction and optionally binding a register. -/
@[simp, simp_step]
def advance : CallFrame → Code → AssocMap Identifier RegisterValue → List AllocId → CallFrame
  | ⟨defn, curBlk, _, term, _, _, retDest?⟩, code', regs', allocas' =>
    ⟨defn, curBlk, code', term, regs', allocas', retDest?⟩

@[simp, simp_step]
def withRegisters : CallFrame → AssocMap Identifier RegisterValue → CallFrame
  | ⟨defn, curBlk, code, term, _, allocas, retDest?⟩, regs' =>
    ⟨defn, curBlk, code, term, regs', allocas, retDest?⟩

@[simp, simp_step]
def withReturnDest : CallFrame → Option ReturnDest → CallFrame
  | ⟨defn, curBlk, code, term, regs, allocas, _⟩, retDest? =>
    ⟨defn, curBlk, code, term, regs, allocas, retDest?⟩

@[simp, simp_step]
def jumpTo : CallFrame → BlockId → Code → (InstructionId × Terminator) →
    AssocMap Identifier RegisterValue → CallFrame
  | ⟨defn, _, _, _, _, allocas, retDest?⟩, nextBlk, code', term', regs' =>
    ⟨defn, nextBlk, code', term', regs', allocas, retDest?⟩

end CallFrame

/-- Pure small-step machine state (no `OracleState` or `fuel` — purely semantic). -/
structure MachineState : Type where
  frames       : List CallFrame
  memory       : MemoryState := {}
  config       : SemanticsConfig := .modern
  dataLayout   : DataLayout := .default64LE
  functions    : AssocMap FunctionId Definition := ∅
  declarations : AssocMap FunctionId Declaration := ∅

instance : Inhabited MachineState := ⟨{ frames := [] }⟩

namespace MachineState

@[simp, simp_step]
def withFrames : MachineState → List CallFrame → MachineState
  | ⟨_, mem, cfg, dl, fns, decls⟩, frames' =>
    ⟨frames', mem, cfg, dl, fns, decls⟩

/-- Whether a call to `fid` may be modelled as a C/C++ library call: `false` if the module defines
`fid` or declares it `nobuiltin`. -/
@[simp, simp_step]
def allowLibcallsFor (st : MachineState) (fid : FunctionId) : Bool :=
  -- A function the module defines is executed as defined, whatever its name (`malloc`,
  -- `calloc`, `_Znwm`, ...): only declarations are modelled as library calls (as in llubi).
  (st.functions.get? fid).isNone &&
  !(((st.declarations.get? fid).map (·.isNoBuiltin)).getD false)

@[simp, simp_step]
def withFramesAndMemory : MachineState → List CallFrame → MemoryState → MachineState
  | ⟨_, _, cfg, dl, fns, decls⟩, frames', mem' =>
    ⟨frames', mem', cfg, dl, fns, decls⟩

@[simp, simp_step]
def withMemory : MachineState → MemoryState → MachineState
  | ⟨frames, _, cfg, dl, fns, decls⟩, mem' =>
    ⟨frames, mem', cfg, dl, fns, decls⟩

end MachineState

/-- Small-step abstract machine configuration. -/
inductive Config : Type where
  | running       (st : MachineState)
  | halted        (retVal : RegisterValue) (finalMem : MemoryState)
  | ub            (msg : String)
  | staticError   (msg : String)
  | resourceError (err : ExecError)

namespace Config

@[simp, simp_step]
def ofError : ExecError → Config
  | .immediateUB msg => .ub msg
  | .staticError msg => .staticError msg
  | err => .resourceError err

def toExcept : Config → Except ExecError RegisterValue
  | .halted v _ => .ok v
  | .ub msg => .error (.immediateUB msg)
  | .staticError msg => .error (.staticError msg)
  | .resourceError e => .error e
  | .running _ => .error .outOfFuel

end Config

/-! ### Frame & Block Helpers (shared by `Step` and `Exec`) -/

/-- Partition leading `phi` instructions from the remaining body of a basic block. -/
@[simp_step]
def splitPhis : Code → Code × Code
  | [] => ([], [])
  | (iid, .phi ty fmf inc md) :: rest =>
    match splitPhis rest with
    | (phis, body) => ((iid, .phi ty fmf inc md) :: phis, body)
  | code => ([], code)

/-- Free all stack `alloca` allocations belonging to a departing call frame. -/
@[simp_step]
def freeAllocaList (mem : MemoryState) : List AllocId → MemoryState
  | [] => mem
  | aid :: rest => freeAllocaList (mem.freeObject aid) rest

theorem freeAllocaList_preserves_wf {mem : MemoryState} (hwf : MemoryState.WellFormed mem)
    (allocas : List AllocId) : MemoryState.WellFormed (freeAllocaList mem allocas) := by
  induction allocas generalizing mem with
  | nil => exact hwf
  | cons a rest ih => exact ih (MemoryState.freeObject_preserves_wf hwf a)

/-- Write an SSA register result for an instruction ID (void IDs are no-ops). -/
@[simp_step]
def writeFrameReg (regs : AssocMap Identifier RegisterValue) (id : InstructionId)
    (val : RegisterValue) : AssocMap Identifier RegisterValue :=
  match id with
  | .id rid => regs.insert (.local_id rid) val
  | .void _ => regs

/-- Structural check that a runtime `RegisterValue` matches an `LlvmType` (top-level shape & widths). -/
@[simp, simp_step]
def RegisterValue.matchesType : LlvmType → RegisterValue → Bool
  | .int wTy, .bv wVal _ => wTy == wVal
  | .byte wTy, .byte wVal _ => wTy == wVal
  | .float ft1, .float ft2 _ => ft1 == ft2
  | .ptr as1, .ptr as2 _ => as1 == as2
  | .vector n _, .vector _ elems => n == elems.length
  | .array n _, .array _ elems => n == elems.length
  | .struct p1 fs1, .struct p2 _ fs2 => p1 == p2 && fs1.length == fs2.length
  | _, _ => false

/-- A parameter's callee attributes together with its call-site attributes (`[]` at an entry
point, where there is no call site). -/
def withSiteAttrs (callee site : List ValueAttr) : List ValueAttr :=
  match site with
  | [] => callee
  | _ => callee ++ site

@[simp] theorem withSiteAttrs_nil (callee : List ValueAttr) : withSiteAttrs callee [] = callee := rfl

/-- The return attributes in effect when `frame` returns: its own, merged with the call site's
(llubi applies both sets together, `handleAttributes`); the call site's are applied again by
`finishCallerReturn`, which is idempotent. -/
def retAttrsAtReturn (frame : CallFrame) (callers : List CallFrame) : List ValueAttr :=
  match callers with
  | caller :: _ =>
    match caller.returnDest? with
    | some rd => withSiteAttrs frame.defn.prototype.retAttrs rd.retAttrs
    | none => frame.defn.prototype.retAttrs
  | [] => frame.defn.prototype.retAttrs

@[simp] theorem retAttrsAtReturn_nil (frame : CallFrame) :
    retAttrsAtReturn frame [] = frame.defn.prototype.retAttrs := rfl

/-- Bind formal parameters of a `Definition` to argument values, type-checking and applying callee parameter attributes. -/
def bindFrameArgs (dl : DataLayout) (mem : MemoryState)
    (argTys : List LlvmType) (isVarArg : Bool) (argAttrs : List (List ValueAttr))
    (argNames : List LocalId) (argVals : List RegisterValue)
    (siteAttrs : List (List ValueAttr) := []) :
    Except ExecError (AssocMap Identifier RegisterValue) :=
  let countBad :=
    argNames.length != argTys.length ||
    (if isVarArg then argVals.length < argNames.length else argVals.length != argNames.length)
  if countBad then
    .error (.staticError s!"Argument count mismatch: expected {argNames.length}, got {argVals.length}")
  else
    let rec go (i : Nat) : List LlvmType → List LocalId → List RegisterValue →
        AssocMap Identifier RegisterValue → Except ExecError (AssocMap Identifier RegisterValue)
      | ty :: ts, nm :: nms, v :: vs, acc =>
        if !v.matchesType ty then
          .error (.staticError s!"Unmatched argument type for %{nm}: expected [{ty.print}], got {v}")
        else
          -- Call-site and callee attributes of a parameter form one set (llubi
          -- `handleAttributes(Ty, V, AttrsAtCallSite, AttrsAtCallee)`), applied in phase order
          -- (`applyValueAttrsPure`). The call site's were also applied when the argument was
          -- evaluated; applying them again is idempotent.
          let attrs := byvalDeferredAttrs (withSiteAttrs (argAttrs.getD i []) (siteAttrs.getD i []))
          match applyValueAttrsPure dl mem ty v attrs with
          | .error e => .error e
          | .ok v' => go (i + 1) ts nms vs (acc.insert (.local_id nm) v')
      | _, _, _, acc => .ok acc
    go 0 argTys argNames argVals ∅

/-- Apply return-site FastMathFlags (non-input output flags) and return `ValueAttr`s. -/
@[simp_step]
def applyRetFMFAndAttrsPure (dl : DataLayout) (mem : MemoryState)
    (retTy : LlvmRetType) (fmf : FastMathFlags) (retAttrs : List ValueAttr)
    (retVal : RegisterValue) : Except ExecError RegisterValue :=
  match retTy with
  | .void => .ok .void
  | .ret rTy =>
    let v1Res := if fmf.any then
      liftUnaryPure rTy.scalarType retVal fun
        | .float ft (.value flt) => .ok (.float ft (handleFMF fmf false false flt))
        | other => .ok other
    else .ok retVal
    match v1Res with
    | .error e => .error e
    | .ok v1 => applyValueAttrsPure dl mem rTy v1 retAttrs

/-- Construct an initial `CallFrame` for entering `defn` with `argVals` (validating signature & param
attrs, merged with the call site's `siteAttrs`). -/
def mkEntryFrame (dl : DataLayout) (mem : MemoryState) (defn : Definition)
    (argVals : List RegisterValue) (siteAttrs : List (List ValueAttr) := []) : Except ExecError CallFrame :=
  match defn.prototype.type with
  | .function _ argTys isVarArg =>
    match defn.blocks with
    | [] => .error (.staticError s!"Function @{defn.prototype.name} has no basic blocks")
    | entryBlk :: _ =>
      match bindFrameArgs dl mem argTys isVarArg defn.prototype.argAttrs defn.args argVals siteAttrs with
      | .error e => .error e
      | .ok regs =>
        match splitPhis entryBlk.code with
        | (phis, body) =>
          if !phis.isEmpty then
            .error (.staticError s!"Entry block %{entryBlk.id} of @{defn.prototype.name} cannot contain phi nodes")
          else
            .ok {
              defn := defn
              curBlock := entryBlk.id
              remainingCode := body
              terminator := entryBlk.terminator
              registers := regs
              frameAllocas := []
              returnDest? := none
            }
  | ty => .error (.staticError s!"Expected function type for prototype, found [{ty.print}]")

/-- Copy any `byval(T)` pointer arguments into fresh stack objects (freed on `ret`), as `llubi`
does: the copy is allocated (aligned to the callee's `align`, else the call site's, else the ABI
alignment of `T`), then the source is checked with the larger of that and the call-site alignment,
then the bytes are copied. `siteAttrs` are the call site's parameter attributes. The copies are
made before a tail call hides the caller's stack objects, so the source is read with `visible`
(the objects hidden by this call) accessible. -/
def applyByValCopies (dl : DataLayout) (cfg : SemanticsConfig) (mem : MemoryState)
    (defn : Definition) (frame : CallFrame) (siteAttrs : List (List ValueAttr) := [])
    (visible : List AllocId := []) :
    Except ExecError (CallFrame × MemoryState) :=
  let rec go (i : Nat) (m : MemoryState) (regs : AssocMap Identifier RegisterValue)
      (allocas : List AllocId) : List LocalId → Except ExecError (CallFrame × MemoryState)
    | [] => .ok ({ frame with registers := regs, frameAllocas := allocas }, m)
    | nm :: rest =>
      let attrs := defn.prototype.argAttrs.getD i []
      match attrs.findSome? (fun | .byval ty => some ty | _ => none) with
      | none => go (i + 1) m regs allocas rest
      | some byvalTy =>
        let siteAlign := (siteAttrs.getD i []).findSome? (fun | .align a => some a | _ => none)
        let calleeAlign := attrs.findSome? (fun | .align a => some a | _ => none)
        let allocAlign := match calleeAlign with
          | some a => a
          | none => siteAlign.getD (dl.typeABIAlign byvalTy)
        match regs.get? (.local_id nm) with
        | some (.ptr as (.value p)) =>
          let allocSize := dl.typeAllocSize byvalTy
          match m.allocate dl cfg allocSize allocAlign nm.toString as .uninitialized .stack false with
          | .error err => .error err
          | .ok (newObj, m1) =>
            match (m1.unhide visible).verifyMemAccess p allocSize (max allocAlign (siteAlign.getD 1)) false with
            | .error err => .error err
            | .ok (srcObj, srcOff) =>
              let bytes := MemoryState.readObjectBytes srcObj srcOff allocSize
              let m2 := m1.writeObjectBytes newObj.allocId 0 bytes
              let newPtr := MemoryState.derivePointer dl newObj
              go (i + 1) m2 (regs.insert (.local_id nm) (.ptr as (.value newPtr)))
                (newObj.allocId :: allocas) rest
        | some (.ptr _ .poison) => .error (.immediateUB "Invalid poison byval pointer argument.")
        | _ => .error (.staticError s!"byval argument %{nm} must be a pointer")
  if defn.prototype.argAttrs.any (fun as => as.any (fun | .byval _ => true | _ => false)) then
    go 0 mem frame.registers frame.frameAllocas defn.args
  else
    .ok (frame, mem)

private theorem applyByValCopies_go_wf {dl cfg defn frame siteAttrs visible i m regs allocas nms frame' mem'}
    (hwf : MemoryState.WellFormed m)
    (h : applyByValCopies.go dl cfg defn frame siteAttrs visible i m regs allocas nms = .ok (frame', mem')) :
    MemoryState.WellFormed mem' := by
  induction nms generalizing i m regs allocas with
  | nil => unfold applyByValCopies.go at h; cases h; exact hwf
  | cons nm rest ih =>
    unfold applyByValCopies.go at h
    dsimp only at h
    split at h
    · exact ih hwf h
    · split at h
      · cases ha : m.allocate dl cfg (dl.typeAllocSize _) _ nm.toString _ .uninitialized .stack false with
        | error e => rw [ha] at h; cases h
        | ok p =>
          rw [ha] at h
          dsimp only at h
          split at h
          · cases h
          · exact ih (MemoryState.writeObjectBytes_preserves_wf (MemoryState.allocate_preserves_wf hwf ha) _ _ _) h
      · cases h
      · cases h

theorem applyByValCopies_preserves_wf {dl cfg mem defn frame siteAttrs visible frame' mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : applyByValCopies dl cfg mem defn frame siteAttrs visible = .ok (frame', mem')) :
    MemoryState.WellFormed mem' := by
  unfold applyByValCopies at h
  split at h
  · exact applyByValCopies_go_wf hwf h
  · cases h; exact hwf

/-- Construct entry `CallFrame` and perform any `byval(T)` stack copies. -/
def mkEntryFrameWithMem (dl : DataLayout) (cfg : SemanticsConfig) (mem : MemoryState)
    (defn : Definition) (argVals : List RegisterValue) (siteAttrs : List (List ValueAttr) := [])
    (visible : List AllocId := []) :
    Except ExecError (CallFrame × MemoryState) :=
  match mkEntryFrame dl mem defn argVals siteAttrs with
  | .error e => .error e
  | .ok frame => applyByValCopies dl cfg mem defn frame siteAttrs visible

theorem mkEntryFrameWithMem_preserves_wf {dl cfg mem defn argVals siteAttrs visible frame' mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : mkEntryFrameWithMem dl cfg mem defn argVals siteAttrs visible = .ok (frame', mem')) :
    MemoryState.WellFormed mem' := by
  unfold mkEntryFrameWithMem at h
  cases hmk : mkEntryFrame dl mem defn argVals siteAttrs with
  | error e => rw [hmk] at h; cases h
  | ok frame => rw [hmk] at h; exact applyByValCopies_preserves_wf hwf h

/-- The type of a value, as far as the value determines it (`none` for `void`). -/
def RegisterValue.inferType? : RegisterValue → Option LlvmType
  | .bv w _ => some (.int w)
  | .byte w _ => some (.byte w)
  | .float ft _ => some (.float ft)
  | .ptr as _ => some (.ptr as)
  | .vector et es => some (.vector es.length et)
  | .array et es => some (.array es.length et)
  | .struct p tys _ => some (.struct p tys)
  | .void => none

/-- Whether argument values fit a callee's parameter types (count, and each value's type,
including vector element types). -/
def callArgsFit (ps : List LlvmType) (isVarArg : Bool) (argVals : List RegisterValue) : Bool :=
  (if isVarArg then argVals.length ≥ ps.length else argVals.length == ps.length) &&
  (ps.zip argVals).all fun (t, v) =>
    v.matchesType t &&
      match t, v.inferType? with
      | .vector _ et, some (.vector _ et') => et.beq et'
      | _, _ => true

/-- `some msg` if a call with return type `retTy` and arguments `argVals` does not match the
callee's function type `calleeTy`: immediate UB (LangRef `call`: "If the function signature does
not match the function type of the call, the behavior is undefined"), reported with llubi's
message (the call's function type, then the callee's). -/
def callSignatureMismatch? (retTy : LlvmRetType) (calleeTy : LlvmType)
    (argVals : List RegisterValue) (callTy? : Option LlvmType := none) : Option String :=
  match callTy?, calleeTy with
  | some ct, .function _ _ _ =>
    -- the call's function type is known (parsed IR): it must equal the callee's, as in llubi
    if ct.beq calleeTy then none
    else some s!"Indirect call through a function pointer with mismatched signature. Expected: {ct.print}, Actual: {calleeTy.print}"
  | none, .function cRet ps va =>
    let argsOk := callArgsFit ps va argVals
    if cRet != retTy || !argsOk then
      let callTy : LlvmType :=
        if argsOk then .function retTy ps va
        else match argVals.mapM RegisterValue.inferType? with
          | some tys => .function retTy tys false
          | none => .function retTy ps va
      some s!"Indirect call through a function pointer with mismatched signature. Expected: {callTy.print}, Actual: {calleeTy.print}"
    else none
  | _, _ => none

/-- The parameter attributes of a declared callee, merged with the call site's, applied to the
arguments (llubi `handleAttributes`, before it finds that the function has no body). -/
def checkDeclArgAttrs (dl : DataLayout) (mem : MemoryState) (d : Declaration)
    (siteAttrs : List (List ValueAttr)) (argVals : List RegisterValue) : Except ExecError Unit :=
  match d.type with
  | .function _ ps _ =>
    let rec go (i : Nat) : List LlvmType → List RegisterValue → Except ExecError Unit
      | ty :: ts, v :: vs =>
        match applyValueAttrsPure dl mem ty v
            (byvalDeferredAttrs (withSiteAttrs (d.argAttrs.getD i []) (siteAttrs.getD i []))) with
        | .error e => .error e
        | .ok _ => go (i + 1) ts vs
      | _, _ => .ok ()
    go 0 ps argVals
  | _ => .ok ()

/-- A call to a function the module does not define: UB if its declaration's type does not
match the call or an argument violates the declaration's parameter attributes, otherwise outside
what we execute. -/
def externalCallConfig (st : MachineState) (fid : FunctionId) (retTy : LlvmRetType)
    (argVals : List RegisterValue) (callTy? : Option LlvmType := none) (mem : MemoryState := {})
    (siteAttrs : List (List ValueAttr) := []) : Config :=
  match st.declarations.get? fid with
  | some d =>
    match callSignatureMismatch? retTy d.type argVals callTy? with
    | some msg => .ub msg
    | none =>
      match checkDeclArgAttrs st.dataLayout mem d siteAttrs argVals with
      | .error (.immediateUB msg) => .ub msg
      | _ => .staticError s!"Call to undefined external function @{fid}"
  | none => .staticError s!"Call to undefined external function @{fid}"

/-- Check that a callsite's return type and `byval` attributes match the callee prototype. -/
def checkCallSignatureAndByVal (_dl : DataLayout) (retTy : LlvmRetType)
    (callArgAttrs : List (List ValueAttr)) (defn : Definition) (siteCC : String := "")
    (argVals : List RegisterValue := []) (callTy? : Option LlvmType := none) :
    Except ExecError Unit :=
  match defn.prototype.type with
  | .function _ _ _ =>
    match callSignatureMismatch? retTy defn.prototype.type argVals callTy? with
    | some msg => .error (.immediateUB msg)
    | none =>
    if defn.prototype.callingConv != siteCC then
      .error (.immediateUB "Mismatched calling convention between callee and callsite.")
    else
      let rec go (i : Nat) : List (List ValueAttr) → Except ExecError Unit
        | [] =>
          -- Check if callee has any remaining byval params past callArgAttrs
          if (defn.prototype.argAttrs.drop i).any (fun as => as.any (fun | .byval _ => true | _ => false)) then
            .error (.immediateUB "Mismatched byval attribute between callee and callsite")
          else .ok ()
        | cAttrs :: rest =>
          let pAttrs := defn.prototype.argAttrs.getD i []
          let cByVal := cAttrs.findSome? (fun | .byval ty => some ty | _ => none)
          let pByVal := pAttrs.findSome? (fun | .byval ty => some ty | _ => none)
          match cByVal, pByVal with
          | none, none => go (i + 1) rest
          | some t1, some t2 =>
            if t1 == t2 then go (i + 1) rest
            else .error (.immediateUB "Mismatched byval attribute between callee and callsite")
          | _, _ =>
            .error (.immediateUB "Mismatched byval attribute between callee and callsite")
      go 0 callArgAttrs
  | _ => .error (.staticError "Callee does not have function type")

/-- Construct a callee entry frame for a `call` instruction, checking signature & `byval` match. -/
def mkCallEntryFrameWithMem (dl : DataLayout) (cfg : SemanticsConfig) (mem : MemoryState)
    (retTy : LlvmRetType) (callArgAttrs : List (List ValueAttr))
    (defn : Definition) (argVals : List RegisterValue) (siteCC : String := "")
    (visible : List AllocId := []) (siteFnTy? : Option LlvmType := none) : Except ExecError (CallFrame × MemoryState) :=
  match checkCallSignatureAndByVal dl retTy callArgAttrs defn siteCC argVals siteFnTy? with
  | .error e => .error e
  | .ok () => mkEntryFrameWithMem dl cfg mem defn argVals callArgAttrs visible

theorem mkCallEntryFrameWithMem_preserves_wf {dl cfg mem retTy callArgAttrs defn argVals siteCC visible siteFnTy? frame' mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : mkCallEntryFrameWithMem dl cfg mem retTy callArgAttrs defn argVals siteCC visible siteFnTy? = .ok (frame', mem')) :
    MemoryState.WellFormed mem' := by
  unfold mkCallEntryFrameWithMem at h
  cases hc : checkCallSignatureAndByVal dl retTy callArgAttrs defn siteCC argVals siteFnTy? with
  | error e => rw [hc] at h; cases h
  | ok u => rw [hc] at h; exact mkEntryFrameWithMem_preserves_wf hwf h

/-- Construct the initial small-step `Config` for calling `defn` with `argVals` in `(cfg, dl, initMem)`. -/
def initCallConfig (cfg : SemanticsConfig) (dl : DataLayout) (initMem : MemoryState)
    (fns : AssocMap FunctionId Definition := ∅) (decls : AssocMap FunctionId Declaration := ∅)
    (defn : Definition) (argVals : List RegisterValue) : Config :=
  match mkEntryFrameWithMem dl cfg initMem defn argVals with
  | .ok (frame', mem') =>
    .running {
      frames := [frame']
      memory := mem'
      config := cfg
      dataLayout := dl
      functions := fns
      declarations := decls
    }
  | .error e => Config.ofError e

/-- Helper: extract the `LlvmRetType` from a `Definition`'s prototype. -/
@[simp, simp_step]
def _root_.LeanNanoLlvm.AST.Definition.retType? (defn : Definition) : Option LlvmRetType :=
  match defn.prototype.type with
  | .function retTy _ _ => some retTy
  | _ => none

attribute [simp_step] AssocMap.get?_insert AssocMap.get?_empty

end LeanNanoLlvm.Semantics
