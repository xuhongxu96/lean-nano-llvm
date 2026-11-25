import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.DataLayout
import LeanNanoLlvm.Semantics.IntOps
import LeanNanoLlvm.Semantics.FloatOps
import LeanNanoLlvm.Semantics.Memory
import LeanNanoLlvm.Semantics.Value

namespace LeanNanoLlvm.Semantics

open AST

/-- Kernel-reducible string prefix check (avoids extern `ByteArray`-backed `String.startsWith`). -/
def strHasPrefix (s p : String) : Bool :=
  let rec go : List Char → List Char → Bool
    | _, [] => true
    | [], _ :: _ => false
    | c1 :: cs1, c2 :: cs2 => if c1 == c2 then go cs1 cs2 else false
  go s.toList p.toList

/-- Verified memory transfer (`memcpy` / `memmove`). -/
def execMemTransferPure (mem : MemoryState) (destVal srcVal lenVal : RegisterValue)
    (isMemMove isLibCall : Bool) : Except ExecError MemoryState :=
  match lenVal with
  | .bv _ .poison => .error (.immediateUB "memcpy/memmove with poison length")
  | .bv _ (.value bv) =>
    let len := bv.toNat
    if len == 0 then .ok mem
    else match destVal with
      | .ptr _ .poison => .error (.immediateUB "memcpy/memmove with poison destination pointer")
      | .ptr _ (.value dstPtr) =>
        match srcVal with
        | .ptr _ .poison => .error (.immediateUB "memcpy/memmove with poison source pointer")
        | .ptr _ (.value srcPtr) =>
          match mem.verifyMemAccess srcPtr len 1 false with
          | .error e => .error e
          | .ok (srcMO, srcOff) =>
            match mem.verifyMemAccess dstPtr len 1 true with
            | .error e => .error e
            | .ok (dstMO, dstOff) =>
              if !isMemMove && srcMO.allocId == dstMO.allocId &&
                 srcOff < dstOff + len && dstOff < srcOff + len &&
                 (isLibCall || srcOff != dstOff) then
                .error (.immediateUB "memcpy with overlapping source and destination")
              else
                let copied := MemoryState.readObjectBytes srcMO srcOff len
                .ok (mem.writeObjectBytes dstMO.allocId dstOff copied)
        | _ => .error (.staticError "Expected source pointer in memcpy/memmove")
      | _ => .error (.staticError "Expected destination pointer in memcpy/memmove")
  | _ => .error (.staticError "Expected integer length in memcpy/memmove")

theorem execMemTransferPure_preserves_wf {mem dst src len isMove isLib mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : execMemTransferPure mem dst src len isMove isLib = .ok mem') :
    MemoryState.WellFormed mem' := by
  unfold execMemTransferPure at h
  cases len with
  | bv w lv =>
    cases lv using PoisonOr.casesOn' with
    | poison => cases h
    | value lbv =>
      dsimp only at h
      by_cases hz : (lbv.toNat == 0) = true
      · rw [if_pos hz] at h; cases h; exact hwf
      · rw [if_neg hz] at h
        cases dst with
        | ptr _ dp =>
          cases dp using PoisonOr.casesOn' with
          | poison => cases h
          | value dstP =>
            cases src with
            | ptr _ sp =>
              cases sp using PoisonOr.casesOn' with
              | poison => cases h
              | value srcP =>
                dsimp only at h
                cases h1 : mem.verifyMemAccess srcP lbv.toNat 1 false with
                | error e => rw [h1] at h; cases h
                | ok p1 =>
                  rw [h1] at h; dsimp only at h
                  cases h2 : mem.verifyMemAccess dstP lbv.toNat 1 true with
                  | error e => rw [h2] at h; cases h
                  | ok p2 =>
                    rw [h2] at h; dsimp only at h
                    split at h
                    · cases h
                    · cases h; exact MemoryState.writeObjectBytes_preserves_wf hwf _ _ _
            | _ => cases h
        | _ => cases h
  | _ => cases h

/-- Verified `memset`. -/
def execMemSetPure (mem : MemoryState) (destVal fillVal lenVal : RegisterValue) :
    Except ExecError MemoryState :=
  match lenVal with
  | .bv _ .poison => .error (.immediateUB "memset with poison length")
  | .bv _ (.value bv) =>
    let len := bv.toNat
    if len == 0 then .ok mem
    else match destVal with
      | .ptr _ .poison => .error (.immediateUB "memset with poison destination pointer")
      | .ptr _ (.value dstPtr) =>
        match mem.verifyMemAccess dstPtr len 1 true with
        | .error e => .error e
        | .ok (dstMO, dstOff) =>
          let fillByte := match fillVal with
            | .bv _ .poison => MemByte.poison
            | .bv _ (.value fbv) => MemByte.concrete (UInt8.ofNat (fbv.toNat &&& 0xFF))
            | _ => MemByte.poison
          let filled := Array.replicate len fillByte
          .ok (mem.writeObjectBytes dstMO.allocId dstOff filled)
      | _ => .error (.staticError "Expected destination pointer in memset")
  | _ => .error (.staticError "Expected integer length in memset")

theorem execMemSetPure_preserves_wf {mem dst fill len mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : execMemSetPure mem dst fill len = .ok mem') :
    MemoryState.WellFormed mem' := by
  unfold execMemSetPure at h
  cases len with
  | bv w lv =>
    cases lv using PoisonOr.casesOn' with
    | poison => cases h
    | value lbv =>
      dsimp only at h
      by_cases hz : (lbv.toNat == 0) = true
      · rw [if_pos hz] at h; cases h; exact hwf
      · rw [if_neg hz] at h
        cases dst with
        | ptr _ dp =>
          cases dp using PoisonOr.casesOn' with
          | poison => cases h
          | value dstP =>
            dsimp only at h
            cases h1 : mem.verifyMemAccess dstP lbv.toNat 1 true with
            | error e => rw [h1] at h; cases h
            | ok p1 =>
              rw [h1] at h; cases h
              exact MemoryState.writeObjectBytes_preserves_wf hwf _ _ _
        | _ => cases h
  | _ => cases h

/-- Predicate identifying heap-allocating C library calls handled relationally via `AllocSpec`. -/
def isAllocLibcall (name : String) : Bool :=
  name == "malloc" || name == "calloc"

/-- Extract return pointer address space for `malloc`/`calloc` (defaults to 0). -/
@[simp]
def retAddrSpace : LlvmRetType → Nat
  | .ret (.ptr a) => a
  | _ => 0

/-- Heap allocation alignment (`16` when ABI pointer alignment ≥ 8, else `8`). -/
@[simp]
def heapAllocAlign (dl : DataLayout) (as : Nat) : Nat :=
  if dl.getPointerABIAlign as ≥ 8 then 16 else 8

/--
Relational specification for `malloc` and `calloc` (used in the primary `Step` relation).
Permits any valid aligned disjoint address via `MemoryState.AllocSpec`, or returning `null` on OOM/overflow.
-/
inductive AllocLibcallSpec (dl : DataLayout) (cfg : SemanticsConfig) (mem : MemoryState) :
    String → LlvmRetType → List RegisterValue → Except ExecError (RegisterValue × MemoryState) → Prop where
  | malloc_poison (retTy : LlvmRetType) (w : Nat) :
      AllocLibcallSpec dl cfg mem "malloc" retTy [.bv w .poison]
        (.error (.immediateUB "malloc called with poison size"))
  | malloc_ok (retTy : LlvmRetType) (w : Nat) (sz : BitVec w) (obj : MemoryObject) (mem' : MemoryState) :
      MemoryState.AllocSpec mem dl cfg sz.toNat (heapAllocAlign dl (retAddrSpace retTy))
        "malloc" (retAddrSpace retTy) .uninitialized .heap false obj mem' →
      AllocLibcallSpec dl cfg mem "malloc" retTy [.bv w (.value sz)]
        (.ok (.ptr (retAddrSpace retTy) (.value (MemoryState.derivePointer dl obj)), mem'))
  | malloc_oom (retTy : LlvmRetType) (w : Nat) (sz : BitVec w) :
      AllocLibcallSpec dl cfg mem "malloc" retTy [.bv w (.value sz)]
        (.ok (.ptr (retAddrSpace retTy) (.value (Pointer.null dl (retAddrSpace retTy))), mem))
  | malloc_bad_size (retTy : LlvmRetType) (w : Nat) (sz : BitVec w) (msg : String) :
      MemoryState.exceedsMaxObjectSize dl sz.toNat (retAddrSpace retTy) = true →
      AllocLibcallSpec dl cfg mem "malloc" retTy [.bv w (.value sz)]
        (.error (.immediateUB msg))
  | malloc_bad_args (retTy : LlvmRetType) (args : List RegisterValue) :
      (∀ w v, args ≠ [.bv w v]) →
      AllocLibcallSpec dl cfg mem "malloc" retTy args
        (.error (.staticError "malloc expects 1 integer argument"))
  | calloc_ok (retTy : LlvmRetType) (w1 w2 : Nat) (cnt : BitVec w1) (sz : BitVec w2)
      (obj : MemoryObject) (mem' : MemoryState) :
      cnt.toNat * sz.toNat < (1 <<< max w1 w2) →
      MemoryState.AllocSpec mem dl cfg (cnt.toNat * sz.toNat) (heapAllocAlign dl (retAddrSpace retTy))
        "calloc" (retAddrSpace retTy) .zeroed .heap false obj mem' →
      AllocLibcallSpec dl cfg mem "calloc" retTy [.bv w1 (.value cnt), .bv w2 (.value sz)]
        (.ok (.ptr (retAddrSpace retTy) (.value (MemoryState.derivePointer dl obj)), mem'))
  | calloc_null (retTy : LlvmRetType) (w1 w2 : Nat) (cnt : BitVec w1) (sz : BitVec w2) :
      AllocLibcallSpec dl cfg mem "calloc" retTy [.bv w1 (.value cnt), .bv w2 (.value sz)]
        (.ok (.ptr (retAddrSpace retTy) (.value (Pointer.null dl (retAddrSpace retTy))), mem))
  | calloc_bad_size (retTy : LlvmRetType) (w1 w2 : Nat) (cnt : BitVec w1) (sz : BitVec w2) (msg : String) :
      cnt.toNat * sz.toNat < (1 <<< max w1 w2) →
      MemoryState.exceedsMaxObjectSize dl (cnt.toNat * sz.toNat) (retAddrSpace retTy) = true →
      AllocLibcallSpec dl cfg mem "calloc" retTy [.bv w1 (.value cnt), .bv w2 (.value sz)]
        (.error (.immediateUB msg))
  | calloc_bad_args (retTy : LlvmRetType) (args : List RegisterValue) :
      (∀ w1 w2 c s, args ≠ [.bv w1 (.value c), .bv w2 (.value s)]) →
      AllocLibcallSpec dl cfg mem "calloc" retTy args
        (.error (.immediateUB "calloc called with poison/invalid arguments"))

/-- Executable `malloc` / `calloc` implementation using deterministic bump allocation. -/
def execAllocLibcall (dl : DataLayout) (cfg : SemanticsConfig) (mem : MemoryState)
    (name : String) (retTy : LlvmRetType) (argVals : List RegisterValue) :
    Option (Except ExecError (RegisterValue × MemoryState)) :=
  if name == "malloc" then
    some <| match argVals with
      | [a] => match a with
        | .bv _ .poison => .error (.immediateUB "malloc called with poison size")
        | .bv _ (.value sz) =>
          let as := retAddrSpace retTy
          let maxAlign := heapAllocAlign dl as
          match mem.allocate dl cfg sz.toNat maxAlign "malloc" as .uninitialized .heap false with
          | .ok (obj, mem') => .ok (.ptr as (.value (MemoryState.derivePointer dl obj)), mem')
          | .error .outOfMemory => .ok (.ptr as (.value (Pointer.null dl as)), mem)
          | .error e => .error e
        | _ => .error (.staticError "malloc expects 1 integer argument")
      | _ => .error (.staticError "malloc expects 1 integer argument")
  else if name == "calloc" then
    some <| match argVals with
      | [a1, a2] => match a1, a2 with
        | .bv w1 (.value cnt), .bv w2 (.value sz) =>
          let as := retAddrSpace retTy
          let maxAlign := heapAllocAlign dl as
          let total := cnt.toNat * sz.toNat
          if total ≥ (1 <<< max w1 w2) then
            .ok (.ptr as (.value (Pointer.null dl as)), mem)
          else
            match mem.allocate dl cfg total maxAlign "calloc" as .zeroed .heap false with
            | .ok (obj, mem') => .ok (.ptr as (.value (MemoryState.derivePointer dl obj)), mem')
            | .error .outOfMemory => .ok (.ptr as (.value (Pointer.null dl as)), mem)
            | .error e => .error e
        | _, _ => .error (.immediateUB "calloc called with poison/invalid arguments")
      | _ => .error (.immediateUB "calloc called with poison/invalid arguments")
  else
    none

private theorem allocate_error_cases {mem : MemoryState} {dl : DataLayout} {cfg : SemanticsConfig}
    {size align : Nat} {name : String} {as : Nat} {initK : MemInitKind} {allocK : MemAllocKind}
    {isC : Bool} {e : ExecError}
    (h : mem.allocate dl cfg size align name as initK allocK isC = .error e) :
    e = .outOfMemory ∨
    (∃ msg, e = .immediateUB msg ∧ MemoryState.exceedsMaxObjectSize dl size as = true) := by
  cases mem
  unfold MemoryState.allocate at h
  dsimp only at h
  by_cases hsz : MemoryState.exceedsMaxObjectSize dl size as = true
  · rw [if_pos hsz] at h; cases h; exact Or.inr ⟨_, rfl, hsz⟩
  · rw [if_neg hsz] at h
    split at h
    · cases h; exact Or.inl rfl
    · split at h
      · cases h; exact Or.inl rfl
      · cases h

theorem execAllocLibcall_sound {dl cfg mem name retTy argVals res}
    (hwf : MemoryState.WellFormed mem)
    (h : execAllocLibcall dl cfg mem name retTy argVals = some res) :
    AllocLibcallSpec dl cfg mem name retTy argVals res := by
  unfold execAllocLibcall at h
  by_cases hm : (name == "malloc") = true
  · have hnm : name = "malloc" := eq_of_beq hm
    subst hnm
    simp only [hm, ↓reduceIte, Option.some.injEq] at h
    subst h
    cases argVals with
    | cons a rest =>
      cases rest with
      | nil =>
        cases a with
        | bv w v =>
          cases v using PoisonOr.casesOn' with
          | poison => exact AllocLibcallSpec.malloc_poison retTy w
          | value sz =>
            dsimp only
            cases halloc : mem.allocate dl cfg sz.toNat (heapAllocAlign dl (retAddrSpace retTy))
                "malloc" (retAddrSpace retTy) .uninitialized .heap false with
            | ok p =>
              exact AllocLibcallSpec.malloc_ok retTy w sz p.1 p.2
                (MemoryState.allocate_satisfies_AllocSpec hwf halloc)
            | error e =>
              rcases allocate_error_cases halloc with rfl | ⟨msg, rfl, hsz⟩
              · exact AllocLibcallSpec.malloc_oom retTy w sz
              · exact AllocLibcallSpec.malloc_bad_size retTy w sz msg hsz
        | _ => exact AllocLibcallSpec.malloc_bad_args retTy _ (by intro w v heq; simp at heq)
      | cons b bs => exact AllocLibcallSpec.malloc_bad_args retTy (a :: b :: bs) (by intro w v heq; cases heq)
    | nil => exact AllocLibcallSpec.malloc_bad_args retTy [] (by intro w v heq; cases heq)
  · have hmf : (name == "malloc") = false := Bool.eq_false_iff.mpr hm
    simp only [hmf, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hc : (name == "calloc") = true
    · have hnm : name = "calloc" := eq_of_beq hc
      subst hnm
      simp only [hc, ↓reduceIte, Option.some.injEq] at h
      subst h
      cases argVals with
      | cons a1 r1 =>
        cases r1 with
        | cons a2 r2 =>
          cases r2 with
          | nil =>
            cases a1 with
            | bv w1 v1 =>
              cases v1 using PoisonOr.casesOn' with
              | value cnt =>
                cases a2 with
                | bv w2 v2 =>
                  cases v2 using PoisonOr.casesOn' with
                  | value sz =>
                    dsimp only
                    by_cases hov : cnt.toNat * sz.toNat ≥ 1 <<< max w1 w2
                    · rw [if_pos hov]
                      exact AllocLibcallSpec.calloc_null retTy w1 w2 cnt sz
                    · rw [if_neg hov]
                      have hlt : cnt.toNat * sz.toNat < 1 <<< max w1 w2 := by omega
                      cases halloc : mem.allocate dl cfg (cnt.toNat * sz.toNat)
                          (heapAllocAlign dl (retAddrSpace retTy))
                          "calloc" (retAddrSpace retTy) .zeroed .heap false with
                      | ok p =>
                        exact AllocLibcallSpec.calloc_ok retTy w1 w2 cnt sz p.1 p.2 hlt
                          (MemoryState.allocate_satisfies_AllocSpec hwf halloc)
                      | error e =>
                        rcases allocate_error_cases halloc with rfl | ⟨msg, rfl, hsz⟩
                        · exact AllocLibcallSpec.calloc_null retTy w1 w2 cnt sz
                        · exact AllocLibcallSpec.calloc_bad_size retTy w1 w2 cnt sz msg hlt hsz
                  | poison =>
                    exact AllocLibcallSpec.calloc_bad_args retTy _ (by
                      intro _ _ _ _ heq
                      simp only [List.cons.injEq, RegisterValue.bv.injEq, and_true] at heq
                      obtain ⟨_, rfl, hp⟩ := heq
                      exact PoisonOr.poison_ne_value _ (eq_of_heq hp))
                | _ => exact AllocLibcallSpec.calloc_bad_args retTy _ (by intro _ _ _ _ heq; simp at heq)
              | poison =>
                exact AllocLibcallSpec.calloc_bad_args retTy _ (by
                  intro _ _ _ _ heq
                  simp only [List.cons.injEq, RegisterValue.bv.injEq, and_true] at heq
                  obtain ⟨⟨rfl, hp⟩, _⟩ := heq
                  exact PoisonOr.poison_ne_value _ (eq_of_heq hp))
            | _ => exact AllocLibcallSpec.calloc_bad_args retTy _ (by intro _ _ _ _ heq; simp at heq)
          | cons a3 r3 =>
            exact AllocLibcallSpec.calloc_bad_args retTy (a1 :: a2 :: a3 :: r3) (by intro _ _ _ _ heq; cases heq)
        | nil => exact AllocLibcallSpec.calloc_bad_args retTy [a1] (by intro _ _ _ _ heq; cases heq)
      | nil => exact AllocLibcallSpec.calloc_bad_args retTy [] (by intro _ _ _ _ heq; cases heq)
    · have hcf : (name == "calloc") = false := Bool.eq_false_iff.mpr hc
      simp only [hcf, Bool.false_eq_true, ↓reduceIte] at h
      cases h

theorem AllocLibcallSpec.preserves_wf {dl cfg mem name retTy argVals retVal mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : AllocLibcallSpec dl cfg mem name retTy argVals (.ok (retVal, mem'))) :
    MemoryState.WellFormed mem' := by
  cases h with
  | malloc_ok _ _ _ _ _ hspec => exact hspec.preserves_wf hwf
  | malloc_oom _ _ _ => exact hwf
  | calloc_ok _ _ _ _ _ _ _ _ hspec => exact hspec.preserves_wf hwf
  | calloc_null _ _ _ _ _ => exact hwf

/-- Pure non-memory LLVM intrinsics (integer, bit-manipulation, saturating, overflow, FP, assume). -/
def evalPureIntrinsicExec? (cfg : SemanticsConfig) (name : String) (retTy : LlvmRetType)
    (fmf : FastMathFlags) (argVals : List RegisterValue) (o : OracleState) :
    Option (Except ExecError (RegisterValue × OracleState)) :=
  if name == "llvm.assume" then
    some <| match argVals with
      | [.bv 1 (.value b)] =>
        if b == 0 then .error (.immediateUB "llvm.assume(false) violated") else .ok (.void, o)
      | [.bv 1 .poison] => .error (.immediateUB "llvm.assume(poison) violated")
      | _ => .error (.staticError "llvm.assume expects i1 argument")
  else if name == "llvm.donothing" then
    some (.ok (.void, o))
  else if strHasPrefix name "llvm.ssa.copy" || strHasPrefix name "llvm.expect" then
    some <| match argVals with
      | v :: _ => .ok (v, o)
      | [] => .error (.staticError s!"{name} requires at least 1 argument")
  else if strHasPrefix name "llvm.abs" then
    some <| match argVals with
      | [v, .bv 1 (.value isIntMinPoison)] =>
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
        (liftUnaryPure resElemTy v fun
          | .bv w .poison => .ok (.bv w .poison)
          | .bv w (.value x) =>
            if isIntMinPoison != 0 && x == BitVec.intMin w then .ok (.bv w .poison)
            else .ok (.bv w (.value (if x.msb then -x else x)))
          | other => .error (.staticError s!"Expected int in llvm.abs, got {other}")).map (·, o)
      | _ => .error (.staticError "llvm.abs expects (int, i1)")
  else if strHasPrefix name "llvm.smax" || strHasPrefix name "llvm.smin" ||
          strHasPrefix name "llvm.umax" || strHasPrefix name "llvm.umin" then
    some <| match argVals with
      | [v1, v2] =>
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
        (liftBinaryPure resElemTy v1 v2 fun a b =>
          match a, b with
          | .bv w1 (.value x), .bv w2 (.value y) =>
            if h : w1 = w2 then
              let x' : BitVec w2 := h ▸ x
              let pickX :=
                if strHasPrefix name "llvm.smax" then BitVec.sle y x'
                else if strHasPrefix name "llvm.smin" then BitVec.sle x' y
                else if strHasPrefix name "llvm.umax" then y ≤ x'
                else x' ≤ y
              .ok (.bv w2 (.value (if pickX then x' else y)))
            else .error (.staticError "width mismatch in min/max intrinsic")
          | .bv w _, _ => .ok (.bv w .poison)
          | _, _ => .error (.staticError "Expected int in min/max intrinsic")).map (·, o)
      | _ => .error (.staticError s!"{name} expects 2 arguments")
  else if strHasPrefix name "llvm.ctlz" || strHasPrefix name "llvm.cttz" then
    some <| match argVals with
      | [v, .bv 1 (.value isZeroPoison)] =>
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
        let isLeading := strHasPrefix name "llvm.ctlz"
        (liftUnaryPure resElemTy v fun
          | .bv w .poison => .ok (.bv w .poison)
          | .bv w (.value x) =>
            if isZeroPoison != 0 && x == 0 then .ok (.bv w .poison)
            else .ok (.bv w (.value (if isLeading then bvCtlz x else bvCttz x)))
          | other => .error (.staticError s!"Expected int in ctlz/cttz, got {other}")).map (·, o)
      | _ => .error (.staticError s!"{name} expects (int, i1)")
  else if strHasPrefix name "llvm.ctpop" || strHasPrefix name "llvm.bitreverse" || strHasPrefix name "llvm.bswap" then
    some <| match argVals with
      | [v] =>
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
        (liftUnaryPure resElemTy v fun
          | .bv w .poison => .ok (.bv w .poison)
          | .bv w (.value x) =>
            let res :=
              if strHasPrefix name "llvm.ctpop" then bvCtpop x
              else if strHasPrefix name "llvm.bitreverse" then bvBitReverse x
              else bvBSwap x
            .ok (.bv w (.value res))
          | other => .error (.staticError s!"Expected int in {name}, got {other}")).map (·, o)
      | _ => .error (.staticError s!"{name} expects 1 argument")
  else if strHasPrefix name "llvm.fshl" || strHasPrefix name "llvm.fshr" then
    some <| match argVals with
      | [.bv w1 (.value a), .bv w2 (.value b), .bv w3 (.value amt)] =>
        if h1 : w1 = w3 then
          if h2 : w2 = w3 then
            let r := if strHasPrefix name "llvm.fshl"
              then bvFshl (h1 ▸ a) (h2 ▸ b) amt
              else bvFshr (h1 ▸ a) (h2 ▸ b) amt
            .ok (.bv w3 (.value r), o)
          else .error (.staticError "width mismatch in fshl/fshr")
        else .error (.staticError "width mismatch in fshl/fshr")
      | [.bv w _, _, _] => .ok (.bv w .poison, o)
      | _ => .error (.staticError s!"{name} expects 3 integer arguments")
  else if strHasPrefix name "llvm.sadd.sat" || strHasPrefix name "llvm.uadd.sat" ||
          strHasPrefix name "llvm.ssub.sat" || strHasPrefix name "llvm.usub.sat" then
    some <| match argVals with
      | [v1, v2] =>
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
        (liftBinaryPure resElemTy v1 v2 fun a b =>
          match a, b with
          | .bv w1 (.value x), .bv w2 (.value y) =>
            if h : w1 = w2 then
              let x' : BitVec w2 := h ▸ x
              let res :=
                if strHasPrefix name "llvm.sadd.sat" then bvSAddSat x' y
                else if strHasPrefix name "llvm.uadd.sat" then bvUAddSat x' y
                else if strHasPrefix name "llvm.ssub.sat" then bvSSubSat x' y
                else bvUSubSat x' y
              .ok (.bv w2 (.value res))
            else .error (.staticError "width mismatch in saturating intrinsic")
          | .bv w _, _ => .ok (.bv w .poison)
          | _, _ => .error (.staticError "Expected int in saturating intrinsic")).map (·, o)
      | _ => .error (.staticError s!"{name} expects 2 arguments")
  else if strHasPrefix name "llvm.sadd.with.overflow" || strHasPrefix name "llvm.uadd.with.overflow" ||
          strHasPrefix name "llvm.ssub.with.overflow" || strHasPrefix name "llvm.usub.with.overflow" ||
          strHasPrefix name "llvm.smul.with.overflow" || strHasPrefix name "llvm.umul.with.overflow" then
    some <| match argVals with
      | [.bv w1 (.value x), .bv w2 (.value y)] =>
        if h : w1 = w2 then
          let x' : BitVec w2 := h ▸ x
          let (res, ov) :=
            if strHasPrefix name "llvm.sadd" then (x' + y, BitVec.saddOverflow x' y)
            else if strHasPrefix name "llvm.uadd" then (x' + y, BitVec.uaddOverflow x' y)
            else if strHasPrefix name "llvm.ssub" then (x' - y, BitVec.ssubOverflow x' y)
            else if strHasPrefix name "llvm.usub" then (x' - y, BitVec.usubOverflow x' y)
            else if strHasPrefix name "llvm.smul" then (x' * y, BitVec.smulOverflow x' y)
            else (x' * y, BitVec.umulOverflow x' y)
          .ok (.struct false [.int w2, .int 1]
            [.bv w2 (.value res), .bv 1 (.value (BitVec.ofBool ov))], o)
        else .error (.staticError "width mismatch in with.overflow intrinsic")
      | [.bv w _, _] =>
        .ok (.struct false [.int w, .int 1] [.bv w .poison, .bv 1 .poison], o)
      | _ => .error (.staticError s!"{name} expects 2 integer arguments")
  else if strHasPrefix name "llvm.fabs" then
    some <| match argVals with
      | [v] =>
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .f32
        let goElem (e : RegisterValue) (o0 : OracleState) : Except ExecError (RegisterValue × OracleState) :=
          match e with
          | .float ft .poison => .ok (.float ft .poison, o0)
          | .float ft (.value flt) =>
            match o0.nextBool with
            | (flipZ, o1) =>
              match handleFMF fmf true flipZ flt with
              | .poison => .ok (.float ft .poison, o1)
              | .value f' => .ok (.float ft (handleFMF fmf false false f'.abs), o1)
          | other => .error (.staticError s!"Expected float in llvm.fabs, got {other}")
        match v with
        | .vector _ elems =>
          let rec goL : List RegisterValue → OracleState → Except ExecError (List RegisterValue × OracleState)
            | [], o0 => .ok ([], o0)
            | e :: es, o0 => do
              let (r, o1) ← goElem e o0
              let (rs, o2) ← goL es o1
              .ok (r :: rs, o2)
          match goL elems o with
          | .ok (rs, o') => .ok (.vector resElemTy rs, o')
          | .error e => .error e
        | _ => goElem v o
      | _ => .error (.staticError "llvm.fabs expects 1 argument")
  else if strHasPrefix name "llvm.copysign" then
    some <| match argVals with
      | [v1, v2] =>
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .f32
        (liftBinaryPure resElemTy v1 v2 fun a b =>
          match a, b with
          | .float ft1 (.value m), .float ft2 (.value s) =>
            if h : ft1 = ft2 then .ok (.float ft2 (.value ((h ▸ m).copySign s)))
            else .error (.staticError "Mismatched float types in llvm.copysign")
          | .float ft _, _ => .ok (.float ft .poison)
          | _, _ => .error (.staticError "Expected floats in llvm.copysign")).map (·, o)
      | _ => .error (.staticError "llvm.copysign expects 2 arguments")
  else if strHasPrefix name "llvm.fma" || strHasPrefix name "llvm.fmuladd" then
    some <| match argVals with
      | [.float ft1 (.value a), .float ft2 (.value b), .float ft3 (.value c)] =>
        if h1 : ft1 = ft3 then
          if h2 : ft2 = ft3 then
            let res := IEEEFloat.fma cfg.roundingMode (h1 ▸ a) (h2 ▸ b) c
            let (nanSign, o1) := o.nextBool
            let (nanPick, o2) := o1.nextNat
            let final := applyNaNPropagation cfg.nanMode res [h1 ▸ a, h2 ▸ b, c] nanSign nanPick
            .ok (.float ft3 (handleFMF fmf false false final), o2)
          else .error (.staticError "Mismatched float types in llvm.fma")
        else .error (.staticError "Mismatched float types in llvm.fma")
      | [.float ft _, _, _] => .ok (.float ft .poison, o)
      | _ => .error (.staticError s!"{name} expects 3 float arguments")
  else if strHasPrefix name "llvm.minimum" || strHasPrefix name "llvm.maximum" ||
          strHasPrefix name "llvm.minnum" || strHasPrefix name "llvm.maxnum" then
    some <| match argVals with
      | [v1, v2] =>
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .f32
        let goElem (a b : RegisterValue) (o0 : OracleState) : Except ExecError (RegisterValue × OracleState) :=
          match a, b with
          | .float ft1 (.value x), .float ft2 (.value y) =>
            if h : ft1 = ft2 then
              let x' : IEEEFloat ft2.format := h ▸ x
              let res :=
                if strHasPrefix name "llvm.minimumnum" || strHasPrefix name "llvm.minnum" then IEEEFloat.minimumnum x' y
                else if strHasPrefix name "llvm.maximumnum" || strHasPrefix name "llvm.maxnum" then IEEEFloat.maximumnum x' y
                else if strHasPrefix name "llvm.minimum" then IEEEFloat.minimum x' y
                else IEEEFloat.maximum x' y
              let (nanSign, o1) := o0.nextBool
              let (nanPick, o2) := o1.nextNat
              let final := applyNaNPropagation cfg.nanMode res [x', y] nanSign nanPick
              .ok (.float ft2 (handleFMF fmf false false final), o2)
            else .error (.staticError "Mismatched float types in FP min/max")
          | .float ft _, _ => .ok (.float ft .poison, o0)
          | _, _ => .error (.staticError "Expected floats in FP min/max")
        match v1, v2 with
        | .vector _ es1, .vector _ es2 =>
          if es1.length != es2.length then .error (.staticError "Vector length mismatch in FP min/max")
          else
            let rec goMinMax : List RegisterValue → List RegisterValue → OracleState →
                Except ExecError (List RegisterValue × OracleState)
              | x :: xs, y :: ys, o0 => do
                let (r, o1) ← goElem x y o0
                let (rs, o2) ← goMinMax xs ys o1
                .ok (r :: rs, o2)
              | _, _, o0 => .ok ([], o0)
            match goMinMax es1 es2 o with
            | .ok (rs, o') => .ok (.vector resElemTy rs, o')
            | .error e => .error e
        | _, _ => goElem v1 v2 o
      | _ => .error (.staticError s!"{name} expects 2 arguments")
  else if strHasPrefix name "llvm.is.fpclass" then
    some <| match argVals with
      | [v, .bv _ (.value mask)] =>
        (liftUnaryPure .i1 v fun
          | .float _ .poison => .ok (.bv 1 .poison)
          | .float _ (.value flt) =>
            .ok (.bv 1 (.value (BitVec.ofBool ((flt.fpClassBit &&& mask.toNat) != 0))))
          | other => .error (.staticError s!"Expected float in llvm.is.fpclass, got {other}")).map (·, o)
      | _ => .error (.staticError "llvm.is.fpclass expects (float, i32)")
  else if strHasPrefix name "llvm.fptosi.sat" || strHasPrefix name "llvm.fptoui.sat" then
    some <| match argVals with
      | [v] =>
        let isSigned := strHasPrefix name "llvm.fptosi.sat"
        match retTy with
        | .ret rTy =>
          match rTy.scalarType with
          | .int dstW =>
            (liftUnaryPure (.int dstW) v fun
              | .float _ .poison => .ok (.bv dstW .poison)
              | .float _ (.value flt) =>
                let bv := if isSigned then flt.toSignedBitVecSat dstW else flt.toUnsignedBitVecSat dstW
                .ok (.bv dstW (.value bv))
              | other => .error (.staticError s!"Expected float in fpto[su]i.sat, got {other}")).map (·, o)
          | _ => .error (.staticError "Expected integer return type for fpto[su]i.sat")
        | .void => .error (.staticError "fpto[su]i.sat cannot return void")
      | _ => .error (.staticError s!"{name} expects 1 argument")
  else
    none

/-- Non-allocating memory & pure intrinsics/libcalls (shared between `Step` and `Exec`). -/
def evalNonAllocIntrinsicExec? (dl : DataLayout) (cfg : SemanticsConfig) (mem : MemoryState)
    (name : String) (retTy : LlvmRetType) (fmf : FastMathFlags) (argVals : List RegisterValue)
    (o : OracleState) : Option (Except ExecError (RegisterValue × MemoryState × OracleState)) :=
  if strHasPrefix name "llvm.lifetime.start" then
    let mem' := match argVals.getLast? with
      | some (.ptr _ (.value p)) => mem.lifetimeStart cfg p
      | _ => mem
    some (.ok (.void, mem', o))
  else if strHasPrefix name "llvm.lifetime.end" then
    let mem' := match argVals.getLast? with
      | some (.ptr _ (.value p)) => mem.lifetimeEnd p
      | _ => mem
    some (.ok (.void, mem', o))
  else if strHasPrefix name "llvm.memcpy" then
    some <| match argVals with
      | dst :: src :: len :: _ => (execMemTransferPure mem dst src len false false).map (fun m' => (.void, m', o))
      | _ => .error (.staticError "llvm.memcpy requires at least 3 arguments")
  else if strHasPrefix name "llvm.memmove" then
    some <| match argVals with
      | dst :: src :: len :: _ => (execMemTransferPure mem dst src len true false).map (fun m' => (.void, m', o))
      | _ => .error (.staticError "llvm.memmove requires at least 3 arguments")
  else if strHasPrefix name "llvm.memset" then
    some <| match argVals with
      | dst :: val :: len :: _ => (execMemSetPure mem dst val len).map (fun m' => (.void, m', o))
      | _ => .error (.staticError "llvm.memset requires at least 3 arguments")
  else if name == "free" then
    some <| match argVals with
      | [.ptr _ .poison] => .error (.immediateUB "free called with poison pointer")
      | [.ptr as (.value p)] =>
        if p.isNull dl as then .ok (.void, mem, o)
        else match mem.resolveObject? p with
          | none => .error (.immediateUB "freeing pointer with invalid/nullary provenance")
          | some mo =>
            if p.addr.toNat != mo.baseAddr then
              .error (.immediateUB s!"freeing non-base pointer {p} (base=0x{String.ofList (Nat.toDigits 16 mo.baseAddr)})")
            else if mo.state == .freed then
              .error (.immediateUB s!"double-free of allocation '{mo.name}'")
            else if !mo.isHeap then
              .error (.immediateUB s!"freeing non-heap allocation '{mo.name}'")
            else
              .ok (.void, mem.freeObject mo.allocId, o)
      | _ => .error (.staticError "free expects 1 pointer argument")
  else if name == "memcpy" then
    some <| match argVals with
      | [dst, src, len] => (execMemTransferPure mem dst src len false true).map (fun m' => (dst, m', o))
      | _ => .error (.staticError "memcpy expects 3 arguments")
  else if name == "memmove" then
    some <| match argVals with
      | [dst, src, len] => (execMemTransferPure mem dst src len true true).map (fun m' => (dst, m', o))
      | _ => .error (.staticError "memmove expects 3 arguments")
  else if name == "memset" then
    some <| match argVals with
      | [dst, val, len] => (execMemSetPure mem dst val len).map (fun m' => (dst, m', o))
      | _ => .error (.staticError "memset expects 3 arguments")
  else
    (evalPureIntrinsicExec? cfg name retTy fmf argVals o).map fun r =>
      r.map fun (v, o') => (v, mem, o')

theorem evalNonAllocIntrinsicExec?_preserves_wf {dl cfg mem name retTy fmf argVals o res mem' o'}
    (hwf : MemoryState.WellFormed mem)
    (h : evalNonAllocIntrinsicExec? dl cfg mem name retTy fmf argVals o = some (.ok (res, mem', o'))) :
    MemoryState.WellFormed mem' := by
  unfold evalNonAllocIntrinsicExec? at h
  by_cases h1 : strHasPrefix name "llvm.lifetime.start" = true
  · rw [if_pos h1] at h
    cases h
    cases argVals.getLast? with
    | none => exact hwf
    | some v =>
      cases v with
      | ptr _ pv =>
        cases pv using PoisonOr.casesOn' with
        | poison => exact hwf
        | value p => exact MemoryState.lifetimeStart_preserves_wf hwf cfg p
      | _ => exact hwf
  · rw [if_neg h1] at h
    by_cases h2 : strHasPrefix name "llvm.lifetime.end" = true
    · rw [if_pos h2] at h
      cases h
      cases argVals.getLast? with
      | none => exact hwf
      | some v =>
        cases v with
        | ptr _ pv =>
          cases pv using PoisonOr.casesOn' with
          | poison => exact hwf
          | value p => exact MemoryState.lifetimeEnd_preserves_wf hwf p
        | _ => exact hwf
    · rw [if_neg h2] at h
      by_cases h3 : strHasPrefix name "llvm.memcpy" = true
      · rw [if_pos h3] at h
        match argVals, h with
        | dst :: src :: len :: _, h =>
          dsimp only at h
          cases ht : execMemTransferPure mem dst src len false false with
          | error e => rw [ht] at h; cases h
          | ok m1 => rw [ht] at h; cases h; exact execMemTransferPure_preserves_wf hwf ht
      · rw [if_neg h3] at h
        by_cases h4 : strHasPrefix name "llvm.memmove" = true
        · rw [if_pos h4] at h
          match argVals, h with
          | dst :: src :: len :: _, h =>
            dsimp only at h
            cases ht : execMemTransferPure mem dst src len true false with
            | error e => rw [ht] at h; cases h
            | ok m1 => rw [ht] at h; cases h; exact execMemTransferPure_preserves_wf hwf ht
        · rw [if_neg h4] at h
          by_cases h5 : strHasPrefix name "llvm.memset" = true
          · rw [if_pos h5] at h
            match argVals, h with
            | dst :: val :: len :: _, h =>
              dsimp only at h
              cases ht : execMemSetPure mem dst val len with
              | error e => rw [ht] at h; cases h
              | ok m1 => rw [ht] at h; cases h; exact execMemSetPure_preserves_wf hwf ht
          · rw [if_neg h5] at h
            by_cases h6 : (name == "free") = true
            · rw [if_pos h6] at h
              match argVals, h with
              | [.ptr _ .poison], h => cases h
              | [.ptr as (.value p)], h =>
                dsimp only at h
                by_cases hnull : p.isNull dl as = true
                · rw [if_pos hnull] at h; cases h; exact hwf
                · rw [if_neg hnull] at h
                  cases hres : mem.resolveObject? p with
                  | none => rw [hres] at h; cases h
                  | some mo =>
                    rw [hres] at h; dsimp only at h
                    by_cases ha : (p.addr.toNat != mo.baseAddr) = true
                    · rw [if_pos ha] at h; cases h
                    · rw [if_neg ha] at h
                      by_cases hf : (mo.state == .freed) = true
                      · rw [if_pos hf] at h; cases h
                      · rw [if_neg hf] at h
                        by_cases hh : (!mo.isHeap) = true
                        · rw [if_pos hh] at h; cases h
                        · rw [if_neg hh] at h; cases h
                          exact MemoryState.freeObject_preserves_wf hwf mo.allocId
            · rw [if_neg h6] at h
              by_cases h7 : (name == "memcpy") = true
              · rw [if_pos h7] at h
                match argVals, h with
                | [dst, src, len], h =>
                  dsimp only at h
                  cases ht : execMemTransferPure mem dst src len false true with
                  | error e => rw [ht] at h; cases h
                  | ok m1 => rw [ht] at h; cases h; exact execMemTransferPure_preserves_wf hwf ht
              · rw [if_neg h7] at h
                by_cases h8 : (name == "memmove") = true
                · rw [if_pos h8] at h
                  match argVals, h with
                  | [dst, src, len], h =>
                    dsimp only at h
                    cases ht : execMemTransferPure mem dst src len true true with
                    | error e => rw [ht] at h; cases h
                    | ok m1 => rw [ht] at h; cases h; exact execMemTransferPure_preserves_wf hwf ht
                · rw [if_neg h8] at h
                  by_cases h9 : (name == "memset") = true
                  · rw [if_pos h9] at h
                    match argVals, h with
                    | [dst, val, len], h =>
                      dsimp only at h
                      cases ht : execMemSetPure mem dst val len with
                      | error e => rw [ht] at h; cases h
                      | ok m1 => rw [ht] at h; cases h; exact execMemSetPure_preserves_wf hwf ht
                  · rw [if_neg h9] at h
                    cases hp : evalPureIntrinsicExec? cfg name retTy fmf argVals o with
                    | none => rw [hp] at h; cases h
                    | some r =>
                      rw [hp] at h
                      dsimp only at h
                      cases r with
                      | error e => cases h
                      | ok p => cases h; exact hwf

private theorem ite_some_eq_none {α : Type} {c : Prop} [Decidable c] {a : α} {b : Option α}
    (h : (if c then some a else b) = none) : ¬ c ∧ b = none := by
  by_cases hc : c
  · rw [if_pos hc] at h; cases h
  · rw [if_neg hc] at h; exact ⟨hc, h⟩

/-- Whether `evalPureIntrinsicExec?` recognizes an intrinsic name is independent of the oracle. -/
theorem evalPureIntrinsicExec?_none_indep {cfg name retTy fmf argVals o o'}
    (h : evalPureIntrinsicExec? cfg name retTy fmf argVals o = none) :
    evalPureIntrinsicExec? cfg name retTy fmf argVals o' = none := by
  unfold evalPureIntrinsicExec? at h ⊢
  repeat (obtain ⟨hc, h⟩ := ite_some_eq_none h; rw [if_neg hc])

/-- Whether `evalNonAllocIntrinsicExec?` recognizes a name is independent of the oracle. -/
theorem evalNonAllocIntrinsicExec?_none_indep {dl cfg mem name retTy fmf argVals o o'}
    (h : evalNonAllocIntrinsicExec? dl cfg mem name retTy fmf argVals o = none) :
    evalNonAllocIntrinsicExec? dl cfg mem name retTy fmf argVals o' = none := by
  unfold evalNonAllocIntrinsicExec? at h ⊢
  repeat (obtain ⟨hc, h⟩ := ite_some_eq_none h; rw [if_neg hc])
  cases hp : evalPureIntrinsicExec? cfg name retTy fmf argVals o with
  | some r => rw [hp] at h; cases h
  | none =>
    rw [evalPureIntrinsicExec?_none_indep (o' := o') hp]
    rfl

end LeanNanoLlvm.Semantics
