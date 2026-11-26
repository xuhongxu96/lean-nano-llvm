import LeanNanoLlvm.Util.Config
import LeanNanoLlvm.Util.AssocMap
import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.DataLayout
import LeanNanoLlvm.AST.Print
import LeanNanoLlvm.Semantics.Memory
import LeanNanoLlvm.Semantics.Value

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
deriving Repr

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

/-- Returns `false` if `fid` is declared `nobuiltin`, disabling C/C++ library call interception. -/
@[simp, simp_step]
def allowLibcallsFor (st : MachineState) (fid : FunctionId) : Bool :=
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

/-- Bind formal parameters of a `Definition` to argument values, type-checking and applying callee parameter attributes. -/
def bindFrameArgs (dl : DataLayout) (mem : MemoryState)
    (argTys : List LlvmType) (isVarArg : Bool) (argAttrs : List (List ValueAttr))
    (argNames : List LocalId) (argVals : List RegisterValue) :
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
          let attrs := argAttrs.getD i []
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

/-- Construct an initial `CallFrame` for entering `defn` with `argVals` (validating signature & param attrs). -/
def mkEntryFrame (dl : DataLayout) (mem : MemoryState) (defn : Definition)
    (argVals : List RegisterValue) : Except ExecError CallFrame :=
  match defn.prototype.type with
  | .function _ argTys isVarArg =>
    match defn.blocks with
    | [] => .error (.staticError s!"Function @{defn.prototype.name} has no basic blocks")
    | entryBlk :: _ =>
      match bindFrameArgs dl mem argTys isVarArg defn.prototype.argAttrs defn.args argVals with
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

/-- Copy any `byval(T)` pointer arguments into fresh callee-owned stack objects (freed on `ret`). -/
def applyByValCopies (dl : DataLayout) (cfg : SemanticsConfig) (mem : MemoryState)
    (defn : Definition) (frame : CallFrame) : Except ExecError (CallFrame × MemoryState) :=
  let rec go (i : Nat) (m : MemoryState) (regs : AssocMap Identifier RegisterValue)
      (allocas : List AllocId) : List LocalId → Except ExecError (CallFrame × MemoryState)
    | [] => .ok ({ frame with registers := regs, frameAllocas := allocas }, m)
    | nm :: rest =>
      let attrs := defn.prototype.argAttrs.getD i []
      match attrs.findSome? (fun | .byval ty => some ty | _ => none) with
      | none => go (i + 1) m regs allocas rest
      | some byvalTy =>
        let effAlign := (attrs.findSome? (fun | .align a => some a | _ => none)).getD (dl.typeABIAlign byvalTy)
        match regs.get? (.local_id nm) with
        | some (.ptr as (.value p)) =>
          let storeSize := dl.typeStoreSize byvalTy
          let allocSize := dl.typeAllocSize byvalTy
          match m.verifyMemAccess p storeSize effAlign false with
          | .error err => .error err
          | .ok (srcObj, srcOff) =>
            let bytes := MemoryState.readObjectBytes srcObj srcOff storeSize
            match m.allocate dl cfg allocSize effAlign nm.ToString as .uninitialized .stack false with
            | .error err => .error err
            | .ok (newObj, m1) =>
              let m2 := m1.writeObjectBytes newObj.allocId 0 bytes
              let newPtr := MemoryState.derivePointer dl newObj
              go (i + 1) m2 (regs.insert (.local_id nm) (.ptr as (.value newPtr)))
                (newObj.allocId :: allocas) rest
        | some (.ptr _ .poison) => .error (.immediateUB s!"byval argument %{nm} is poison")
        | _ => .error (.staticError s!"byval argument %{nm} must be a pointer")
  if defn.prototype.argAttrs.any (fun as => as.any (fun | .byval _ => true | _ => false)) then
    go 0 mem frame.registers frame.frameAllocas defn.args
  else
    .ok (frame, mem)

private theorem applyByValCopies_go_wf {dl cfg defn frame i m regs allocas nms frame' mem'}
    (hwf : MemoryState.WellFormed m)
    (h : applyByValCopies.go dl cfg defn frame i m regs allocas nms = .ok (frame', mem')) :
    MemoryState.WellFormed mem' := by
  induction nms generalizing i m regs allocas with
  | nil => unfold applyByValCopies.go at h; cases h; exact hwf
  | cons nm rest ih =>
    unfold applyByValCopies.go at h
    dsimp only at h
    split at h
    · exact ih hwf h
    · split at h
      · split at h
        · cases h
        · cases ha : m.allocate dl cfg (dl.typeAllocSize _) _ nm.ToString _ .uninitialized .stack false with
          | error e => rw [ha] at h; cases h
          | ok p =>
            rw [ha] at h
            exact ih (MemoryState.writeObjectBytes_preserves_wf (MemoryState.allocate_preserves_wf hwf ha) _ _ _) h
      · cases h
      · cases h

theorem applyByValCopies_preserves_wf {dl cfg mem defn frame frame' mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : applyByValCopies dl cfg mem defn frame = .ok (frame', mem')) :
    MemoryState.WellFormed mem' := by
  unfold applyByValCopies at h
  split at h
  · exact applyByValCopies_go_wf hwf h
  · cases h; exact hwf

/-- Construct entry `CallFrame` and perform any `byval(T)` stack copies. -/
def mkEntryFrameWithMem (dl : DataLayout) (cfg : SemanticsConfig) (mem : MemoryState)
    (defn : Definition) (argVals : List RegisterValue) : Except ExecError (CallFrame × MemoryState) :=
  match mkEntryFrame dl mem defn argVals with
  | .error e => .error e
  | .ok frame => applyByValCopies dl cfg mem defn frame

theorem mkEntryFrameWithMem_preserves_wf {dl cfg mem defn argVals frame' mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : mkEntryFrameWithMem dl cfg mem defn argVals = .ok (frame', mem')) :
    MemoryState.WellFormed mem' := by
  unfold mkEntryFrameWithMem at h
  cases hmk : mkEntryFrame dl mem defn argVals with
  | error e => rw [hmk] at h; cases h
  | ok frame => rw [hmk] at h; exact applyByValCopies_preserves_wf hwf h

/-- Check that a callsite's return type and `byval` attributes match the callee prototype. -/
def checkCallSignatureAndByVal (_dl : DataLayout) (retTy : LlvmRetType)
    (callArgAttrs : List (List ValueAttr)) (defn : Definition) : Except ExecError Unit :=
  match defn.prototype.type with
  | .function calleeRetTy _ _ =>
    if calleeRetTy != retTy then
      .error (.immediateUB "Call through function pointer with mismatched return type")
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
            else .error (.immediateUB "Mismatched byval attribute type between callee and callsite")
          | _, _ =>
            .error (.immediateUB "Mismatched byval attribute between callee and callsite")
      go 0 callArgAttrs
  | _ => .error (.staticError "Callee does not have function type")

/-- Construct a callee entry frame for a `call` instruction, checking signature & `byval` match. -/
def mkCallEntryFrameWithMem (dl : DataLayout) (cfg : SemanticsConfig) (mem : MemoryState)
    (retTy : LlvmRetType) (callArgAttrs : List (List ValueAttr))
    (defn : Definition) (argVals : List RegisterValue) : Except ExecError (CallFrame × MemoryState) :=
  match checkCallSignatureAndByVal dl retTy callArgAttrs defn with
  | .error e => .error e
  | .ok () => mkEntryFrameWithMem dl cfg mem defn argVals

theorem mkCallEntryFrameWithMem_preserves_wf {dl cfg mem retTy callArgAttrs defn argVals frame' mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : mkCallEntryFrameWithMem dl cfg mem retTy callArgAttrs defn argVals = .ok (frame', mem')) :
    MemoryState.WellFormed mem' := by
  unfold mkCallEntryFrameWithMem at h
  cases hc : checkCallSignatureAndByVal dl retTy callArgAttrs defn with
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
