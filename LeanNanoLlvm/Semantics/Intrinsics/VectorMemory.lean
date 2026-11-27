import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.DataLayout
import LeanNanoLlvm.Semantics.Operations
import LeanNanoLlvm.Util.Text

/-!
# Vector memory intrinsics

Masked, gather/scatter, expand/compress, VP, strided, matrix, histogram and speculative loads
and stores, element by element as `llubi` performs them.
-/

namespace LeanNanoLlvm.Semantics

open AST
open RegisterValue (poisonOf)

/-- `llubi` diagnostic for `llvm.matrix.column.major.store` with a too-small stride. -/
@[irreducible] def matrixStrideMsg (stride rows : Nat) : String :=
  s!"llvm.matrix.column.major.store with stride {stride} less than the number of rows {rows}."



/-- Add a signed byte offset to a pointer, wrapping at the DataLayout index width. -/
private def ptrAddBytes (dl : DataLayout) (p : Pointer) (delta : Int) : Pointer :=
  let idxW := dl.getIndexSizeInBits 0
  let oldIdx : BitVec idxW := p.addr.truncate idxW
  let newIdx := oldIdx + BitVec.ofInt idxW delta
  let highBits : Nat := (p.addr.toNat >>> idxW) <<< idxW
  { p with addr := BitVec.ofNat p.addrWidth (highBits ||| newIdx.toNat) }

private def getArgAlign? (argAttrs : List (List ValueAttr)) (idx : Nat) : Option Nat :=
  (argAttrs.getD idx []).findSome? fun
    | .align a => some a
    | _ => none

/-- Load a single element of type `elemTy` from pointer `p` with alignment `align`. -/
private def loadElemFromPtr (dl : DataLayout) (cfg : SemanticsConfig) (mem : MemoryState)
    (p : Pointer) (elemTy : LlvmType) (align : Nat) (o : OracleState) :
    Except ExecError (RegisterValue × OracleState) :=
  let sz := dl.typeStoreSize elemTy
  match mem.verifyMemAccess p sz align false with
  | .error e => .error e
  | .ok (mo, off) =>
    let bytes := MemoryState.readObjectBytes mo off sz
    let (v, _, o') := bytesToValue dl cfg bytes elemTy o
    .ok (v, o')

/-- Store a single element of type `elemTy` to pointer `p` with alignment `align`. -/
private def storeElemToPtr (dl : DataLayout) (cfg : SemanticsConfig) (mem : MemoryState)
    (p : Pointer) (elemTy : LlvmType) (val : RegisterValue) (align : Nat) :
    Except ExecError MemoryState :=
  let sz := dl.typeStoreSize elemTy
  match mem.verifyMemAccess p sz align true with
  | .error e => .error e
  | .ok (mo, off) =>
    let bytes := valueToBytes dl cfg val elemTy
    .ok (mem.writeObjectBytes mo.allocId off bytes)

private theorem storeElemToPtr_preserves_wf {dl cfg mem p elemTy val align mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : storeElemToPtr dl cfg mem p elemTy val align = .ok mem') :
    MemoryState.WellFormed mem' := by
  unfold storeElemToPtr at h; dsimp only at h
  cases hv : mem.verifyMemAccess p (dl.typeStoreSize elemTy) align true with
  | error e => rw [hv] at h; cases h
  | ok pair => rw [hv] at h; cases h; exact MemoryState.writeObjectBytes_preserves_wf hwf _ _ _

/-- Sequentially execute a list of `(Pointer, RegisterValue)` element stores. -/
private def execStoreList (dl : DataLayout) (cfg : SemanticsConfig) (elemTy : LlvmType) (align : Nat)
    (mem : MemoryState) : List (Pointer × RegisterValue) → Except ExecError MemoryState
  | [] => .ok mem
  | (p, v) :: rest =>
    match storeElemToPtr dl cfg mem p elemTy v align with
    | .error e => .error e
    | .ok mem' => execStoreList dl cfg elemTy align mem' rest

private theorem execStoreList_preserves_wf {dl cfg elemTy align mem writes mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : execStoreList dl cfg elemTy align mem writes = .ok mem') :
    MemoryState.WellFormed mem' := by
  induction writes generalizing mem with
  | nil => unfold execStoreList at h; cases h; exact hwf
  | cons w rest ih =>
    unfold execStoreList at h
    cases hs : storeElemToPtr dl cfg mem w.1 elemTy w.2 align with
    | error e => rw [hs] at h; cases h
    | ok m1 => rw [hs] at h; exact ih (storeElemToPtr_preserves_wf hwf hs) h

/-- Helper: group pointers by `(prov, addr)` preserving first-seen order and counting multiplicities. -/
private def groupHistogramPtrs : List Pointer → List (Pointer × Nat)
  | [] => []
  | p :: rest =>
    let rec insertOne : List (Pointer × Nat) → List (Pointer × Nat)
      | [] => [(p, 1)]
      | (q, cnt) :: xs =>
        if q.addr.toNat == p.addr.toNat && q.prov == p.prov then (q, cnt + 1) :: xs
        else (q, cnt) :: insertOne xs
    let rec go (acc : List (Pointer × Nat)) : List Pointer → List (Pointer × Nat)
      | [] => acc
      | r :: rs =>
        let rec bump : List (Pointer × Nat) → List (Pointer × Nat)
          | [] => [(r, 1)]
          | (q, cnt) :: xs =>
            if q.addr.toNat == r.addr.toNat && q.prov == r.prov then (q, cnt + 1) :: xs
            else (q, cnt) :: bump xs
        go (bump acc) rs
    go [(p, 1)] rest

/-- Load all grouped histogram lanes from `mem` and compute their updated values before any stores. -/
private def prepareHistogramWrites (dl : DataLayout) (cfg : SemanticsConfig) (op : String)
    (w : Nat) (incVal : PoisonOr (BitVec w)) (mem : MemoryState) :
    List (Pointer × Nat) → Except ExecError (List (Pointer × RegisterValue))
  | [] => .ok []
  | (p, cnt) :: rest => do
    let elemTy := LlvmType.int w
    let (curVal, _) ← loadElemFromPtr dl cfg mem p elemTy 1 default
    let newVal : RegisterValue :=
      match curVal, incVal with
      | .bv w1 (.value x), .value inc =>
        if h : w1 = w then
          let x' : BitVec w := h ▸ x
          let r : BitVec w :=
            if op == "add" then x' + inc * BitVec.ofNat w cnt
            else if op == "uadd.sat" then
              let rec satLoop : Nat → BitVec w → BitVec w
                | 0, acc => acc
                | k + 1, acc => satLoop k (bvUAddSat acc inc)
              satLoop cnt x'
            else if op == "umax" then if x'.toNat ≥ inc.toNat then x' else inc
            else if x'.toNat ≤ inc.toNat then x' else inc
          .bv w (.value r)
        else .bv w .poison
      | _, _ => .bv w .poison
    let restWrites ← prepareHistogramWrites dl cfg op w incVal mem rest
    .ok ((p, newVal) :: restWrites)

/-- Execute active lanes of `llvm.experimental.vector.histogram.{add,uadd.sat,umax,umin}`:
    loads all unique lanes first, computes updates with lane multiplicities, then stores in order. -/
private def execHistogramLoop (dl : DataLayout) (cfg : SemanticsConfig) (op : String)
    (w : Nat) (incVal : PoisonOr (BitVec w)) (mem : MemoryState)
    (ptrs : List Pointer) : Except ExecError MemoryState :=
  match prepareHistogramWrites dl cfg op w incVal mem (groupHistogramPtrs ptrs) with
  | .error e => .error e
  | .ok writes => execStoreList dl cfg (.int w) 1 mem writes

private theorem execHistogramLoop_preserves_wf {dl cfg op w incVal mem ptrs mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : execHistogramLoop dl cfg op w incVal mem ptrs = .ok mem') :
    MemoryState.WellFormed mem' := by
  unfold execHistogramLoop at h
  cases hp : prepareHistogramWrites dl cfg op w incVal mem (groupHistogramPtrs ptrs) with
  | error e => rw [hp] at h; cases h
  | ok writes => rw [hp] at h; exact execStoreList_preserves_wf hwf h

/-- Read-only vector/masked/VP/speculative memory load intrinsics (never modify `mem`). -/
def evalVecMemRead? (dl : DataLayout) (cfg : SemanticsConfig) (mem : MemoryState)
    (name : String) (retTy : LlvmRetType) (argVals : List RegisterValue) (o : OracleState)
    (argAttrs : List (List ValueAttr) := []) :
    Option (Except ExecError (RegisterValue × OracleState)) :=
  if strHasPrefix name "llvm.masked.load" then
    some <| match argVals, retTy with
      | [ptrVal, .vector _ mask, .vector elemTy passthru], .ret (.vector len _) =>
        if dl.typeSizeInBits elemTy % 8 != 0 then
          .error (.staticError s!"{name} with element type {elemTy.print} is not supported.")
        else
          let stride : Int := Int.ofNat (dl.typeStoreSize elemTy)
          let rec goLoad (i : Nat) (o0 : OracleState) (acc : List RegisterValue) :
              Except ExecError (List RegisterValue × OracleState) :=
            if i ≥ len then .ok (acc.reverse, o0)
            else match mask.getD i (.bv 1 .poison) with
              | .bv 1 (.value b) =>
                if b == 1#1 then
                  match ptrVal with
                  | .ptr _ (.value p) =>
                    match loadElemFromPtr dl cfg mem (ptrAddBytes dl p (Int.ofNat i * stride)) elemTy 1 o0 with
                    | .error e => .error e
                    | .ok (v, o1) => goLoad (i + 1) o1 (v :: acc)
                  | _ => .error (.immediateUB "Invalid memory access with a poison pointer.")
                else goLoad (i + 1) o0 (passthru.getD i (poisonOf elemTy) :: acc)
              | _ => .error (.immediateUB "poison mask lane in llvm.masked.load")
          termination_by len - i
          (goLoad 0 o []).map fun (vs, o') => (.vector elemTy vs, o')
      | _, _ => .error (.staticError "llvm.masked.load expects (ptr, mask, passthru)")
  else if strHasPrefix name "llvm.masked.expandload" then
    some <| match argVals, retTy with
      | [ptrVal, .vector _ mask, .vector elemTy passthru], .ret (.vector len _) =>
        if dl.typeSizeInBits elemTy % 8 != 0 then
          .error (.staticError s!"{name} with element type {elemTy.print} is not supported.")
        else
          let stride : Int := Int.ofNat (dl.typeStoreSize elemTy)
          let rec goExpand (i memIdx : Nat) (o0 : OracleState) (acc : List RegisterValue) :
              Except ExecError (List RegisterValue × OracleState) :=
            if i ≥ len then .ok (acc.reverse, o0)
            else match mask.getD i (.bv 1 .poison) with
              | .bv 1 (.value b) =>
                if b == 1#1 then
                  match ptrVal with
                  | .ptr _ (.value p) =>
                    match loadElemFromPtr dl cfg mem (ptrAddBytes dl p (Int.ofNat memIdx * stride)) elemTy 1 o0 with
                    | .error e => .error e
                    | .ok (v, o1) => goExpand (i + 1) (memIdx + 1) o1 (v :: acc)
                  | _ => .error (.immediateUB "Invalid memory access with a poison pointer.")
                else goExpand (i + 1) memIdx o0 (passthru.getD i (poisonOf elemTy) :: acc)
              | _ => .error (.immediateUB "poison mask lane in llvm.masked.expandload")
          termination_by len - i
          (goExpand 0 0 o []).map fun (vs, o') => (.vector elemTy vs, o')
      | _, _ => .error (.staticError "llvm.masked.expandload expects (ptr, mask, passthru)")
  else if strHasPrefix name "llvm.masked.gather" then
    some <| match argVals, retTy with
      | [.vector _ ptrs, .vector _ mask, .vector elemTy passthru], .ret (.vector len _) =>
        let rec goGather (i : Nat) (o0 : OracleState) (acc : List RegisterValue) :
            Except ExecError (List RegisterValue × OracleState) :=
          if i ≥ len then .ok (acc.reverse, o0)
          else match mask.getD i (.bv 1 .poison) with
            | .bv 1 (.value b) =>
              if b == 1#1 then
                match ptrs.getD i (.ptr 0 .poison) with
                | .ptr _ (.value p) =>
                  match loadElemFromPtr dl cfg mem p elemTy 1 o0 with
                  | .error e => .error e
                  | .ok (v, o1) => goGather (i + 1) o1 (v :: acc)
                | _ => .error (.immediateUB "Invalid memory access with a poison pointer.")
              else goGather (i + 1) o0 (passthru.getD i (poisonOf elemTy) :: acc)
            | _ => .error (.immediateUB "poison mask lane in llvm.masked.gather")
        termination_by len - i
        (goGather 0 o []).map fun (vs, o') => (.vector elemTy vs, o')
      | _, _ => .error (.staticError "llvm.masked.gather expects (ptrs, mask, passthru)")
  else if strHasPrefix name "llvm.vp.load" then
    some <| match argVals, retTy with
      | [ptrVal, .vector _ mask, .bv _ (.value evlBV)], .ret (.vector len elemTy) =>
        let evl := evlBV.toNat
        if evl > len then .error (.immediateUB "evl exceeds vector length in llvm.vp.load")
        else
          let baseReqAlign := (getArgAlign? argAttrs 0).getD (dl.typeABIAlign (.vector len elemTy))
          let stride : Int := Int.ofNat (dl.typeStoreSize elemTy)
          let rec goVpLoad (i : Nat) (o0 : OracleState) (acc : List RegisterValue) :
              Except ExecError (List RegisterValue × OracleState) :=
            if i ≥ len then .ok (acc.reverse, o0)
            else if i ≥ evl then goVpLoad (i + 1) o0 (poisonOf elemTy :: acc)
            else match mask.getD i (.bv 1 .poison) with
              | .bv 1 (.value b) =>
                if b == 1#1 then
                  match ptrVal with
                  | .ptr _ (.value p) =>
                    if baseReqAlign > 1 && p.addr.toNat % baseReqAlign != 0 then
                      .error (.immediateUB "Invalid memory access with a poison pointer.")
                    else
                      match loadElemFromPtr dl cfg mem (ptrAddBytes dl p (Int.ofNat i * stride)) elemTy 1 o0 with
                      | .error e => .error e
                      | .ok (v, o1) => goVpLoad (i + 1) o1 (v :: acc)
                  | _ => .error (.immediateUB "Invalid memory access with a poison pointer.")
                else goVpLoad (i + 1) o0 (poisonOf elemTy :: acc)
              | _ => .error (.immediateUB "poison mask lane in llvm.vp.load")
          termination_by len - i
          (goVpLoad 0 o []).map fun (vs, o') => (.vector elemTy vs, o')
      | [_, _, .bv _ .poison], _ => .error (.immediateUB "poison evl in llvm.vp.load")
      | _, _ => .error (.staticError "llvm.vp.load expects (ptr, mask, evl)")
  else if strHasPrefix name "llvm.vp.gather" then
    some <| match argVals, retTy with
      | [.vector _ ptrs, .vector _ mask, .bv _ (.value evlBV)], .ret (.vector len elemTy) =>
        let evl := evlBV.toNat
        if evl > len then .error (.immediateUB "evl exceeds vector length in llvm.vp.gather")
        else
          let laneReqAlign := (getArgAlign? argAttrs 0).getD (dl.typeABIAlign elemTy)
          let rec goVpGather (i : Nat) (o0 : OracleState) (acc : List RegisterValue) :
              Except ExecError (List RegisterValue × OracleState) :=
            if i ≥ len then .ok (acc.reverse, o0)
            else if i ≥ evl then goVpGather (i + 1) o0 (poisonOf elemTy :: acc)
            else match mask.getD i (.bv 1 .poison) with
              | .bv 1 (.value b) =>
                if b == 1#1 then
                  match ptrs.getD i (.ptr 0 .poison) with
                  | .ptr _ (.value p) =>
                    match loadElemFromPtr dl cfg mem p elemTy laneReqAlign o0 with
                    | .error e => .error e
                    | .ok (v, o1) => goVpGather (i + 1) o1 (v :: acc)
                  | _ => .error (.immediateUB "Invalid memory access with a poison pointer.")
                else goVpGather (i + 1) o0 (poisonOf elemTy :: acc)
              | _ => .error (.immediateUB "poison mask lane in llvm.vp.gather")
          termination_by len - i
          (goVpGather 0 o []).map fun (vs, o') => (.vector elemTy vs, o')
      | [_, _, .bv _ .poison], _ => .error (.immediateUB "poison evl in llvm.vp.gather")
      | _, _ => .error (.staticError "llvm.vp.gather expects (ptrs, mask, evl)")
  else if strHasPrefix name "llvm.experimental.vp.strided.load" then
    some <| match argVals, retTy with
      | [ptrVal, strideVal, .vector _ mask, .bv _ (.value evlBV)], .ret (.vector len elemTy) =>
        let evl := evlBV.toNat
        if evl > len then .error (.immediateUB "evl exceeds vector length in llvm.experimental.vp.strided.load")
        else
          let baseReqAlign := (getArgAlign? argAttrs 0).getD (dl.typeABIAlign elemTy)
          let strideOpt : Option Int := match strideVal with
            | .bv _ (.value bv) => some bv.toInt
            | _ => none
          let rec goVpStrided (i : Nat) (o0 : OracleState) (acc : List RegisterValue) :
              Except ExecError (List RegisterValue × OracleState) :=
            if i ≥ len then .ok (acc.reverse, o0)
            else if i ≥ evl then goVpStrided (i + 1) o0 (poisonOf elemTy :: acc)
            else match mask.getD i (.bv 1 .poison) with
              | .bv 1 (.value b) =>
                if b == 1#1 then
                  match ptrVal with
                  | .ptr _ (.value p) =>
                    if baseReqAlign > 1 && p.addr.toNat % baseReqAlign != 0 then
                      .error (.immediateUB "Invalid memory access with a poison pointer.")
                    else
                      let lanePtr? : Except ExecError Pointer :=
                        if i == 0 then .ok p
                        else match strideOpt with
                          | some stride => .ok (ptrAddBytes dl p (Int.ofNat i * stride))
                          | none => .error (.immediateUB "poison stride in llvm.experimental.vp.strided.load")
                      match lanePtr? with
                      | .error e => .error e
                      | .ok lp =>
                        match loadElemFromPtr dl cfg mem lp elemTy 1 o0 with
                        | .error e => .error e
                        | .ok (v, o1) => goVpStrided (i + 1) o1 (v :: acc)
                  | _ => .error (.immediateUB "Invalid memory access with a poison pointer.")
                else goVpStrided (i + 1) o0 (poisonOf elemTy :: acc)
              | _ => .error (.immediateUB "poison mask lane in llvm.experimental.vp.strided.load")
          termination_by len - i
          (goVpStrided 0 o []).map fun (vs, o') => (.vector elemTy vs, o')
      | [_, _, _, .bv _ .poison], _ =>
        .error (.immediateUB "poison evl in llvm.experimental.vp.strided.load")
      | _, _ => .error (.staticError "llvm.experimental.vp.strided.load expects (ptr, stride, mask, evl)")
  else if strHasPrefix name "llvm.speculative.load" then
    some <| match argVals, retTy with
      | .ptr _ (.value p) :: .bv 1 (.value revBV) :: optBound, .ret ty =>
        let totalSz := dl.typeStoreSize ty
        let isRev := revBV == 1#1
        let boundRes : Except ExecError Nat := match optBound with
          | [] => .ok totalSz
          | .bv _ .poison :: _ => .error (.immediateUB "llvm.speculative.load with poison number of accessible bytes.")
          | .bv _ (.value bBV) :: _ =>
            if bBV.toNat > totalSz then
              .error (.immediateUB s!"llvm.speculative.load number of accessible bytes {bBV.toNat} exceeds the loaded size {totalSz}.")
            else .ok bBV.toNat
          | _ => .error (.immediateUB "invalid bound in llvm.speculative.load")
        match boundRes with
        | .error e => .error e
        | .ok bound =>
          if bound == 0 then
            let bytes := Array.replicate totalSz MemByte.poison
            let (v, _, o') := bytesToValue dl cfg bytes ty o
            .ok (v, o')
          else
            let startOff := if isRev then totalSz - bound else 0
            match mem.verifyMemAccess (ptrAddBytes dl p (Int.ofNat startOff)) bound 1 false with
            | .error e => .error e
            | .ok (mo, objOff) =>
              let liveBytes := MemoryState.readObjectBytes mo objOff bound
              let bytes := Array.ofFn (n := totalSz) fun i =>
                if isRev then
                  if i.val ≥ startOff then liveBytes.getD (i.val - startOff) MemByte.poison
                  else MemByte.poison
                else
                  if i.val < bound then liveBytes.getD i.val MemByte.poison
                  else MemByte.poison
              let (v, _, o') := bytesToValue dl cfg bytes ty o
              .ok (v, o')
      | .ptr _ .poison :: _, _ | _ :: .bv 1 .poison :: _, _ =>
        .error (.immediateUB "llvm.speculative.load with poison pointer.")
      | _, _ => .error (.staticError "llvm.speculative.load expects (ptr, i1, ...)")
  else
    none

theorem evalVecMemRead?_none_indep {dl cfg mem name retTy argVals o o' argAttrs}
    (h : evalVecMemRead? dl cfg mem name retTy argVals o argAttrs = none) :
    evalVecMemRead? dl cfg mem name retTy argVals o' argAttrs = none := by
  have ite_none : ∀ {α : Type} {c : Prop} [Decidable c] {a : α} {b : Option α},
      (if c then some a else b) = none → ¬ c ∧ b = none := by
    intro α c _ a b h0; by_cases hc : c
    · rw [if_pos hc] at h0; cases h0
    · rw [if_neg hc] at h0; exact ⟨hc, h0⟩
  unfold evalVecMemRead? at h ⊢
  repeat (obtain ⟨hc, h⟩ := ite_none h; rw [if_neg hc])

/-- Collect active `(Pointer, RegisterValue)` writes for masked/VP/strided/matrix stores. -/
private def collectMaskedWrites (dl : DataLayout) (elemTy : LlvmType) (ptrVal : RegisterValue)
    (vals mask : List RegisterValue) (evl : Nat) (stride : Int) (compress : Bool)
    (baseReqAlign : Nat := 1) :
    Except ExecError (List (Pointer × RegisterValue)) :=
  let rec go (i memIdx : Nat) (acc : List (Pointer × RegisterValue)) :
      Except ExecError (List (Pointer × RegisterValue)) :=
    if i ≥ evl then .ok acc.reverse
    else match mask.getD i (.bv 1 .poison) with
      | .bv 1 (.value b) =>
        if b == 1#1 then
          match ptrVal with
          | .ptr _ (.value p) =>
            if baseReqAlign > 1 && p.addr.toNat % baseReqAlign != 0 then
              .error (.immediateUB "Invalid memory access with a poison pointer.")
            else
              let idx := if compress then memIdx else i
              let p' := ptrAddBytes dl p (Int.ofNat idx * stride)
              go (i + 1) (memIdx + 1) ((p', vals.getD i (poisonOf elemTy)) :: acc)
          | _ => .error (.immediateUB "Invalid memory access with a poison pointer.")
        else go (i + 1) memIdx acc
      | _ => .error (.immediateUB "poison mask lane in masked/vp store")
  termination_by evl - i
  go 0 0 []

/-- Collect active `(Pointer, RegisterValue)` writes for masked/VP scatter. -/
private def collectScatterWrites (elemTy : LlvmType) (vals ptrs mask : List RegisterValue) (evl : Nat) :
    Except ExecError (List (Pointer × RegisterValue)) :=
  let rec go (i : Nat) (acc : List (Pointer × RegisterValue)) :
      Except ExecError (List (Pointer × RegisterValue)) :=
    if i ≥ evl then .ok acc.reverse
    else match mask.getD i (.bv 1 .poison) with
      | .bv 1 (.value b) =>
        if b == 1#1 then
          match ptrs.getD i (.ptr 0 .poison) with
          | .ptr _ (.value p) =>
            go (i + 1) ((p, vals.getD i (poisonOf elemTy)) :: acc)
          | _ => .error (.immediateUB "Invalid memory access with a poison pointer.")
        else go (i + 1) acc
      | _ => .error (.immediateUB "poison mask lane in masked/vp scatter")
  termination_by evl - i
  go 0 []

/-- Vector/masked/VP/matrix/histogram memory store intrinsics (oracle-independent). -/
def evalVecMemWrite? (dl : DataLayout) (cfg : SemanticsConfig) (mem : MemoryState)
    (name : String) (argVals : List RegisterValue)
    (argAttrs : List (List ValueAttr) := []) : Option (Except ExecError MemoryState) :=
  if strHasPrefix name "llvm.masked.store" || strHasPrefix name "llvm.masked.compressstore" then
    some <| match argVals with
      | [.vector elemTy vals, ptrVal, .vector _ mask] =>
        if dl.typeSizeInBits elemTy % 8 != 0 then
          .error (.staticError s!"{name} with element type {elemTy.print} is not supported.")
        else
          let compress := strHasPrefix name "llvm.masked.compressstore"
          let stride : Int := Int.ofNat (dl.typeStoreSize elemTy)
          match collectMaskedWrites dl elemTy ptrVal vals mask vals.length stride compress with
          | .error e => .error e
          | .ok ws => execStoreList dl cfg elemTy 1 mem ws
      | _ => .error (.staticError s!"{name} expects (val, ptr, mask)")
  else if strHasPrefix name "llvm.masked.scatter" then
    some <| match argVals with
      | [.vector elemTy vals, .vector _ ptrs, .vector _ mask] =>
        match collectScatterWrites elemTy vals ptrs mask vals.length with
        | .error e => .error e
        | .ok ws => execStoreList dl cfg elemTy 1 mem ws
      | _ => .error (.staticError "llvm.masked.scatter expects (val, ptrs, mask)")
  else if strHasPrefix name "llvm.vp.store" then
    some <| match argVals with
      | [.vector elemTy vals, ptrVal, .vector _ mask, .bv _ (.value evlBV)] =>
        let evl := evlBV.toNat
        if evl > vals.length then .error (.immediateUB "evl exceeds vector length in llvm.vp.store")
        else
          let baseReqAlign := (getArgAlign? argAttrs 1).getD (dl.typeABIAlign (.vector vals.length elemTy))
          let stride : Int := Int.ofNat (dl.typeStoreSize elemTy)
          match collectMaskedWrites dl elemTy ptrVal vals mask evl stride false baseReqAlign with
          | .error e => .error e
          | .ok ws => execStoreList dl cfg elemTy 1 mem ws
      | [_, _, _, .bv _ .poison] => .error (.immediateUB "poison evl in llvm.vp.store")
      | _ => .error (.staticError "llvm.vp.store expects (val, ptr, mask, evl)")
  else if strHasPrefix name "llvm.vp.scatter" then
    some <| match argVals with
      | [.vector elemTy vals, .vector _ ptrs, .vector _ mask, .bv _ (.value evlBV)] =>
        let evl := evlBV.toNat
        if evl > vals.length then .error (.immediateUB "evl exceeds vector length in llvm.vp.scatter")
        else
          let laneReqAlign := (getArgAlign? argAttrs 1).getD (dl.typeABIAlign elemTy)
          match collectScatterWrites elemTy vals ptrs mask evl with
          | .error e => .error e
          | .ok ws => execStoreList dl cfg elemTy laneReqAlign mem ws
      | [_, _, _, .bv _ .poison] => .error (.immediateUB "poison evl in llvm.vp.scatter")
      | _ => .error (.staticError "llvm.vp.scatter expects (val, ptrs, mask, evl)")
  else if strHasPrefix name "llvm.experimental.vp.strided.store" then
    some <| match argVals with
      | [.vector elemTy vals, ptrVal, strideVal, .vector _ mask, .bv _ (.value evlBV)] =>
        let evl := evlBV.toNat
        if evl > vals.length then .error (.immediateUB "evl exceeds vector length in llvm.experimental.vp.strided.store")
        else
          let baseReqAlign := (getArgAlign? argAttrs 1).getD (dl.typeABIAlign elemTy)
          let strideOpt : Option Int := match strideVal with
            | .bv _ (.value bv) => some bv.toInt
            | _ => none
          let rec collectStrided (i : Nat) (acc : List (Pointer × RegisterValue)) :
              Except ExecError (List (Pointer × RegisterValue)) :=
            if i ≥ evl then .ok acc.reverse
            else match mask.getD i (.bv 1 .poison) with
              | .bv 1 (.value b) =>
                if b == 1#1 then
                  match ptrVal with
                  | .ptr _ (.value p) =>
                    if baseReqAlign > 1 && p.addr.toNat % baseReqAlign != 0 then
                      .error (.immediateUB "Invalid memory access with a poison pointer.")
                    else
                      let lanePtr? : Except ExecError Pointer :=
                        if i == 0 then .ok p
                        else match strideOpt with
                          | some stride => .ok (ptrAddBytes dl p (Int.ofNat i * stride))
                          | none => .error (.immediateUB "poison stride in llvm.experimental.vp.strided.store")
                      match lanePtr? with
                      | .error e => .error e
                      | .ok lp => collectStrided (i + 1) ((lp, vals.getD i (poisonOf elemTy)) :: acc)
                  | _ => .error (.immediateUB "Invalid memory access with a poison pointer.")
                else collectStrided (i + 1) acc
              | _ => .error (.immediateUB "poison mask lane in llvm.experimental.vp.strided.store")
          termination_by evl - i
          match collectStrided 0 [] with
          | .error e => .error e
          | .ok ws => execStoreList dl cfg elemTy 1 mem ws
      | [_, _, _, _, .bv _ .poison] =>
        .error (.immediateUB "poison evl in llvm.experimental.vp.strided.store")
      | _ => .error (.staticError "llvm.experimental.vp.strided.store expects (val, ptr, stride, mask, evl)")
  else if strHasPrefix name "llvm.matrix.column.major.store" then
    some <| match argVals with
      | [.vector elemTy vals, ptrVal, .bv _ (.value strideBV), .bv 1 (.value _), .bv _ (.value rowsBV), .bv _ (.value colsBV)] =>
        let rows := rowsBV.toNat
        let cols := colsBV.toNat
        let stride := strideBV.toNat
        if stride < rows then .error (.immediateUB (matrixStrideMsg stride rows))
        else if rows * cols == 0 then .ok mem
        else match ptrVal with
          | .ptr _ (.value p) =>
            let idxW := dl.getIndexSizeInBits 0
            let idxLimit := 1 <<< idxW
            let strideIdx := stride % idxLimit
            let elemSz := dl.typeAllocSize elemTy
            let overflowed := (List.range cols).any fun c =>
              let colByteOff := c * strideIdx * elemSz
              c > 0 && (colByteOff ≥ idxLimit || (p.addr.truncate idxW).toNat + colByteOff ≥ idxLimit)
            if overflowed then
              .error (.immediateUB "Invalid memory access with a poison pointer.")
            else
              let colTy := LlvmType.vector rows elemTy
              let ws := (List.range cols).map fun c =>
                let colVals := (List.range rows).map fun r =>
                  vals.getD (c * rows + r) (poisonOf elemTy)
                (ptrAddBytes dl p (Int.ofNat (c * strideIdx * elemSz)),
                 RegisterValue.vector elemTy colVals)
              execStoreList dl cfg colTy 1 mem ws
          | _ => .error (.immediateUB "Invalid memory access with a poison pointer.")
      | [_, _, .bv _ .poison, _, _, _] | [_, _, _, .bv 1 .poison, _, _] =>
        .error (.immediateUB "poison stride/volatile in llvm.matrix.column.major.store")
      | _ => .error (.staticError "llvm.matrix.column.major.store expects 6 arguments")
  else if strHasPrefix name "llvm.experimental.vector.histogram." then
    some <| match argVals with
      | [.vector _ ptrs, .bv w incVal, .vector _ mask] =>
        let op :=
          if strHasPrefix name "llvm.experimental.vector.histogram.add" then "add"
          else if strHasPrefix name "llvm.experimental.vector.histogram.uadd.sat" then "uadd.sat"
          else if strHasPrefix name "llvm.experimental.vector.histogram.umax" then "umax"
          else "umin"
        let rec collectPtrs (i : Nat) (acc : List Pointer) : Except ExecError (List Pointer) :=
          if i ≥ ptrs.length then .ok acc.reverse
          else match mask.getD i (.bv 1 .poison) with
            | .bv 1 (.value b) =>
              if b == 1#1 then
                match ptrs.getD i (.ptr 0 .poison) with
                | .ptr _ (.value p) => collectPtrs (i + 1) (p :: acc)
                | _ => .error (.immediateUB "Invalid memory access with a poison pointer.")
              else collectPtrs (i + 1) acc
            | _ => .error (.immediateUB "poison mask lane in vector.histogram")
        termination_by ptrs.length - i
        match collectPtrs 0 [] with
        | .error e => .error e
        | .ok activePtrs => execHistogramLoop dl cfg op w incVal mem activePtrs
      | _ => .error (.staticError s!"{name} expects (ptrs, inc, mask)")
  else
    none

theorem evalVecMemWrite?_preserves_wf {dl cfg mem name argVals argAttrs mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : evalVecMemWrite? dl cfg mem name argVals argAttrs = some (.ok mem')) :
    MemoryState.WellFormed mem' := by
  unfold evalVecMemWrite? at h
  split at h
  · injection h with h; split at h
    · dsimp only at h; split at h
      · cases h
      · cases hc : collectMaskedWrites dl _ _ _ _ _ _ _ _ with
        | error e => rw [hc] at h; cases h
        | ok ws => rw [hc] at h; exact execStoreList_preserves_wf hwf h
    · cases h
  · split at h
    · injection h with h; split at h
      · cases hc : collectScatterWrites _ _ _ _ _ with
        | error e => rw [hc] at h; cases h
        | ok ws => rw [hc] at h; exact execStoreList_preserves_wf hwf h
      · cases h
    · split at h
      · injection h with h; split at h
        · dsimp only at h; split at h
          · cases h
          · cases hc : collectMaskedWrites dl _ _ _ _ _ _ _ _ with
            | error e => rw [hc] at h; cases h
            | ok ws => rw [hc] at h; exact execStoreList_preserves_wf hwf h
        · cases h
        · cases h
      · split at h
        · injection h with h; split at h
          · dsimp only at h; split at h
            · cases h
            · cases hc : collectScatterWrites _ _ _ _ _ with
              | error e => rw [hc] at h; cases h
              | ok ws => rw [hc] at h; exact execStoreList_preserves_wf hwf h
          · cases h
          · cases h
        · split at h
          · injection h with h; split at h
            · dsimp only at h; split at h
              · cases h
              · split at h
                · cases h
                · exact execStoreList_preserves_wf hwf h
            · cases h
            · cases h
          · split at h
            · injection h with h; split at h
              · dsimp only at h; split at h
                · cases h
                · split at h
                  · cases h; exact hwf
                  · split at h
                    · split at h
                      · cases h
                      · exact execStoreList_preserves_wf hwf h
                    · cases h
              · cases h
              · cases h
              · cases h
            · split at h
              · injection h with h; split at h
                · dsimp only at h
                  cases hc : evalVecMemWrite?.collectPtrs _ _ _ _ with
                  | error e => rw [hc] at h; cases h
                  | ok ps => rw [hc] at h; exact execHistogramLoop_preserves_wf hwf h
                · cases h
              · cases h

end LeanNanoLlvm.Semantics
