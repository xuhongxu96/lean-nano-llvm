import LeanNanoLlvm.Util.Config
import LeanNanoLlvm.Util.Oracle
import LeanNanoLlvm.Util.AssocMap
import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.DataLayout
import LeanNanoLlvm.AST.Print
import LeanNanoLlvm.Semantics.Value

/-!
# `getelementptr` address arithmetic

Mirrors `llubi::Context::computeGEP`: index canonicalization, the `inbounds`/`nusw`/`nuw`
overflow rules, and vector GEPs.
-/

namespace LeanNanoLlvm.Semantics

open AST

/-- Sign-extend or truncate GEP index to `idxWidth`, checking `nusw`/`nuw` truncation overflow. -/
def canonicalizeGEPIndex (idxWidth : Nat) (flags : GEPFlags) (idxVal : RegisterValue) :
    PoisonOr (BitVec idxWidth) :=
  match idxVal with
  | .bv w (.value bv) =>
    if h : w = idxWidth then .value (h ▸ bv)
    else if w > idxWidth then
      let tr := bv.truncate idxWidth
      if flags.hasNUSW && tr.signExtend w != bv then .poison
      else if flags.nuw && tr.zeroExtend w != bv then .poison
      else .value tr
    else
      .value (bv.signExtend idxWidth)
  | _ => .poison

/-- Compute one GEP pointer-add step `(ptr, offset, accumulatedOffset)` with `inbounds`/`nusw`/`nuw`. -/
def computePtrAddStep (mem : MemoryState) (flags : GEPFlags)
    (ptr : Pointer) {idxW : Nat} (offset : BitVec idxW) (accOff : PoisonOr (BitVec idxW)) :
    PoisonOr Pointer × PoisonOr (BitVec idxW) :=
  if offset == 0 then
    (.value ptr, accOff)
  else
    let oldIdx : BitVec idxW := ptr.addr.truncate idxW
    let newIdx := oldIdx + offset
    if flags.nuw && BitVec.uaddOverflow oldIdx offset then
      (.poison, .poison)
    else
      let nuswBad := flags.hasNUSW &&
        (if !offset.msb then newIdx < oldIdx else oldIdx < newIdx)
      if nuswBad then
        (.poison, .poison)
      else
        let highBits : Nat := (ptr.addr.toNat >>> idxW) <<< idxW
        let newAddrNat := highBits ||| newIdx.toNat
        let newAddr := BitVec.ofNat ptr.addrWidth newAddrNat
        let inboundsCheck : Bool × Provenance :=
          if !flags.inbounds then (true, ptr.prov)
          else match mem.resolveObject? ptr with
            | none => (false, ptr.prov)
            | some mo =>
              if mo.inBounds ptr.addr.toNat && mo.inBounds newAddr.toNat then
                let prov' := match ptr.prov with
                  | .wildcard g none wid => Provenance.wildcard g (some mo.allocId) wid
                  | p => p
                (true, prov')
              else (false, ptr.prov)
        match inboundsCheck with
        | (false, _) => (.poison, .poison)
        | (true, narrowedProv) =>
          let newAcc : PoisonOr (BitVec idxW) := match accOff with
            | .poison => .poison
            | .value a =>
              let s := a + offset
              if flags.hasNUSW && BitVec.saddOverflow a offset then .poison
              else if flags.nuw && BitVec.uaddOverflow a offset then .poison
              else .value s
          match newAcc with
          | .poison => (.poison, .poison)
          | .value _ =>
            (.value ⟨narrowedProv, ptr.addrWidth, newAddr⟩, newAcc)

/-- Compute scaled pointer add `ptr + idx * scale`. -/
def computeScaledPtrAdd (mem : MemoryState) (flags : GEPFlags)
    (ptrOpt : PoisonOr Pointer) {idxW : Nat} (idxOpt : PoisonOr (BitVec idxW))
    (scale : Nat) (accOff : PoisonOr (BitVec idxW)) :
    PoisonOr Pointer × PoisonOr (BitVec idxW) :=
  match ptrOpt, idxOpt with
  | .value ptr, .value idx =>
    if scale == 0 then (.value ptr, accOff)
    else if scale == 1 then computePtrAddStep mem flags ptr idx accOff
    else
      let scaleBV := BitVec.ofNat idxW scale
      let scaled := idx * scaleBV
      if flags.hasNUSW && BitVec.smulOverflow idx scaleBV then (.poison, .poison)
      else if flags.nuw && BitVec.umulOverflow idx scaleBV then (.poison, .poison)
      else computePtrAddStep mem flags ptr scaled accOff
  | _, _ => (.poison, .poison)

/-- Pure GEP evaluation over evaluated base pointer and index values. -/
def evalGEPValuesPure (dl : DataLayout) (mem : MemoryState) (flags : GEPFlags)
    (baseTy ptrTy : LlvmType) (basePtrVal : RegisterValue) (idxVals : List RegisterValue) :
    Except ExecError RegisterValue := do
  let addrSpace := match ptrTy.scalarType with
    | .ptr as => as
    | _ => 0
  let idxW := dl.getIndexSizeInBits addrSpace
  let initAcc : List (PoisonOr (BitVec idxW)) :=
    match basePtrVal with
    | .vector _ es => List.replicate es.length (.value (BitVec.ofNat idxW 0))
    | _ => [.value (BitVec.ofNat idxW 0)]

  let applyScaled (idxVal : RegisterValue) (scale : Nat)
      (res : RegisterValue) (acc : List (PoisonOr (BitVec idxW))) :
      Except ExecError (RegisterValue × List (PoisonOr (BitVec idxW))) := do
    match res, idxVal with
    | .vector _ ptrs, .vector _ idxs =>
      if ptrs.length != idxs.length then
        .error (.staticError "Mismatched vector lengths in getelementptr")
      let mut newPtrs : List RegisterValue := []
      let mut newAcc : List (PoisonOr (BitVec idxW)) := []
      for i in List.range ptrs.length do
        let pOpt := match ptrs.getD i (.ptr addrSpace .poison) with
          | .ptr _ po => po
          | _ => .poison
        let iOpt := canonicalizeGEPIndex idxW flags (idxs.getD i (.bv idxW .poison))
        let aOpt := acc.getD i .poison
        match computeScaledPtrAdd mem flags pOpt iOpt scale aOpt with
        | (p', a') =>
          newPtrs := newPtrs ++ [.ptr addrSpace p']
          newAcc := newAcc ++ [a']
      .ok (.vector (.ptr addrSpace) newPtrs, newAcc)
    | .vector _ ptrs, scalarIdx =>
      let iOpt := canonicalizeGEPIndex idxW flags scalarIdx
      let mut newPtrs : List RegisterValue := []
      let mut newAcc : List (PoisonOr (BitVec idxW)) := []
      for i in List.range ptrs.length do
        let pOpt := match ptrs.getD i (.ptr addrSpace .poison) with
          | .ptr _ po => po
          | _ => .poison
        let aOpt := acc.getD i .poison
        match computeScaledPtrAdd mem flags pOpt iOpt scale aOpt with
        | (p', a') =>
          newPtrs := newPtrs ++ [.ptr addrSpace p']
          newAcc := newAcc ++ [a']
      .ok (.vector (.ptr addrSpace) newPtrs, newAcc)
    | scalarPtr, .vector _ idxs =>
      let pOpt := match scalarPtr with
        | .ptr _ po => po
        | _ => .poison
      let a0 := acc.headD .poison
      let mut newPtrs : List RegisterValue := []
      let mut newAcc : List (PoisonOr (BitVec idxW)) := []
      for idx in idxs do
        let iOpt := canonicalizeGEPIndex idxW flags idx
        match computeScaledPtrAdd mem flags pOpt iOpt scale a0 with
        | (p', a') =>
          newPtrs := newPtrs ++ [.ptr addrSpace p']
          newAcc := newAcc ++ [a']
      .ok (.vector (.ptr addrSpace) newPtrs, newAcc)
    | scalarPtr, scalarIdx =>
      let pOpt := match scalarPtr with
        | .ptr _ po => po
        | _ => .poison
      let iOpt := canonicalizeGEPIndex idxW flags scalarIdx
      let a0 := acc.headD .poison
      match computeScaledPtrAdd mem flags pOpt iOpt scale a0 with
      | (p', a') => .ok (.ptr addrSpace p', [a'])

  let rec stepIdxs (isFirst : Bool) (curRes : RegisterValue)
      (accOff : List (PoisonOr (BitVec idxW))) (curTy : Option LlvmType) :
      List RegisterValue → Except ExecError RegisterValue
    | [] => .ok curRes
    | idxVal :: rest => do
      if isFirst then
        let stride := dl.typeAllocSize baseTy
        let (r', a') ← applyScaled idxVal stride curRes accOff
        stepIdxs false r' a' (some baseTy) rest
      else
        match curTy with
        | some (.struct packed fieldTys) =>
          let fieldIdx? : Option Nat := match idxVal with
            | .bv _ (.value bv) => some bv.toNat
            | .vector _ ((.bv _ (.value bv)) :: _) => some bv.toNat
            | _ => none
          match fieldIdx? with
          | none => .error (.staticError "Invalid struct index in getelementptr")
          | some fi =>
            match dl.structFieldOffset? packed fieldTys fi, fieldTys[fi]? with
            | some byteOff, some fTy =>
              let offScalar := RegisterValue.bv idxW (.value (BitVec.ofNat idxW byteOff))
              let offVal := match idxVal with
                | .vector _ es => RegisterValue.vector (.int idxW) (List.replicate es.length offScalar)
                | _ => offScalar
              let (r', a') ← applyScaled offVal 1 curRes accOff
              stepIdxs false r' a' (some fTy) rest
            | _, _ => .error (.staticError s!"Struct index {fi} out of bounds in getelementptr")
        | some (.array _ elemTy) =>
          let stride := dl.typeAllocSize elemTy
          let (r', a') ← applyScaled idxVal stride curRes accOff
          stepIdxs false r' a' (some elemTy) rest
        | some (.vector _ elemTy) =>
          let stride := dl.typeAllocSize elemTy
          let (r', a') ← applyScaled idxVal stride curRes accOff
          stepIdxs false r' a' (some elemTy) rest
        | some other =>
          .error (.staticError s!"Cannot index into non-aggregate type {other.print} in getelementptr")
        | none =>
          .error (.staticError "Internal error in getelementptr type traversal")
  stepIdxs true basePtrVal initAcc none idxVals

end LeanNanoLlvm.Semantics
