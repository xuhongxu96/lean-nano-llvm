import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.DataLayout
import LeanNanoLlvm.Semantics.IntOps
import LeanNanoLlvm.Semantics.FloatOps
import LeanNanoLlvm.Semantics.Memory
import LeanNanoLlvm.Semantics.Value

namespace LeanNanoLlvm.Semantics

open AST
open RegisterValue (poisonOf)

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

/-- Predicate identifying C++ `operator new` / `operator new[]` mangled names. -/
def isCxxNew (name : String) : Bool :=
  name == "_Znwm" || name == "_Znam" || name == "_Znwj" || name == "_Znaj"

/-- Predicate identifying heap-allocating C/C++ library calls handled relationally via `AllocSpec`. -/
def isAllocLibcall (name : String) : Bool :=
  name == "malloc" || name == "calloc" || isCxxNew name

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
Relational specification for `malloc`, `calloc`, and C++ `operator new` (used in the primary `Step` relation).
Permits any valid aligned disjoint address via `MemoryState.AllocSpec`, or returning `null` / OOM.
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
  | cxxNew_poison (name : String) (retTy : LlvmRetType) (w : Nat) :
      isCxxNew name = true →
      AllocLibcallSpec dl cfg mem name retTy [.bv w .poison]
        (.error (.immediateUB "operator new called with poison size"))
  | cxxNew_ok (name : String) (retTy : LlvmRetType) (w : Nat) (sz : BitVec w) (obj : MemoryObject) (mem' : MemoryState) :
      isCxxNew name = true →
      MemoryState.AllocSpec mem dl cfg sz.toNat (heapAllocAlign dl (retAddrSpace retTy))
        "new" (retAddrSpace retTy) .uninitialized .heap false obj mem' →
      AllocLibcallSpec dl cfg mem name retTy [.bv w (.value sz)]
        (.ok (.ptr (retAddrSpace retTy) (.value (MemoryState.derivePointer dl obj)), mem'))
  | cxxNew_oom (name : String) (retTy : LlvmRetType) (w : Nat) (sz : BitVec w) :
      isCxxNew name = true →
      AllocLibcallSpec dl cfg mem name retTy [.bv w (.value sz)]
        (.error .outOfMemory)
  | cxxNew_bad_args (name : String) (retTy : LlvmRetType) (args : List RegisterValue) :
      isCxxNew name = true →
      (∀ w v, args ≠ [.bv w v]) →
      AllocLibcallSpec dl cfg mem name retTy args
        (.error (.staticError "operator new expects 1 integer argument"))

/-- Executable `malloc` / `calloc` / `operator new` implementation using deterministic bump allocation. -/
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
          | .error _ => .ok (.ptr as (.value (Pointer.null dl as)), mem)
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
            | .error _ => .ok (.ptr as (.value (Pointer.null dl as)), mem)
        | _, _ => .error (.immediateUB "calloc called with poison/invalid arguments")
      | _ => .error (.immediateUB "calloc called with poison/invalid arguments")
  else if isCxxNew name then
    some <| match argVals with
      | [a] => match a with
        | .bv _ .poison => .error (.immediateUB "operator new called with poison size")
        | .bv _ (.value sz) =>
          let as := retAddrSpace retTy
          let maxAlign := heapAllocAlign dl as
          match mem.allocate dl cfg sz.toNat maxAlign "new" as .uninitialized .heap false with
          | .ok (obj, mem') => .ok (.ptr as (.value (MemoryState.derivePointer dl obj)), mem')
          | .error _ => .error .outOfMemory
        | _ => .error (.staticError "operator new expects 1 integer argument")
      | _ => .error (.staticError "operator new expects 1 integer argument")
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
            | error _ =>
              exact AllocLibcallSpec.malloc_oom retTy w sz
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
                      | error _ =>
                        exact AllocLibcallSpec.calloc_null retTy w1 w2 cnt sz
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
      by_cases hn : isCxxNew name = true
      · simp only [hn, ↓reduceIte, Option.some.injEq] at h
        subst h
        cases argVals with
        | cons a rest =>
          cases rest with
          | nil =>
            cases a with
            | bv w v =>
              cases v using PoisonOr.casesOn' with
              | poison => exact AllocLibcallSpec.cxxNew_poison name retTy w hn
              | value sz =>
                dsimp only
                cases halloc : mem.allocate dl cfg sz.toNat (heapAllocAlign dl (retAddrSpace retTy))
                    "new" (retAddrSpace retTy) .uninitialized .heap false with
                | ok p =>
                  exact AllocLibcallSpec.cxxNew_ok name retTy w sz p.1 p.2 hn
                    (MemoryState.allocate_satisfies_AllocSpec hwf halloc)
                | error _ =>
                  exact AllocLibcallSpec.cxxNew_oom name retTy w sz hn
            | _ => exact AllocLibcallSpec.cxxNew_bad_args name retTy _ hn (by intro w v heq; simp at heq)
          | cons b bs => exact AllocLibcallSpec.cxxNew_bad_args name retTy (a :: b :: bs) hn (by intro w v heq; cases heq)
        | nil => exact AllocLibcallSpec.cxxNew_bad_args name retTy [] hn (by intro w v heq; cases heq)
      · have hnf : isCxxNew name = false := Bool.eq_false_iff.mpr hn
        simp only [hnf, Bool.false_eq_true, ↓reduceIte] at h
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
  | cxxNew_ok _ _ _ _ _ _ _ hspec => exact hspec.preserves_wf hwf

/-- Pure deterministic (oracle-independent) LLVM intrinsics: saturating shifts, scmp/ucmp,
    smulh/umulh, clmul, pdep/pext, vscale, stepvector, vector reverse/extract/insert/interleave/
    deinterleave/splice, active lane mask, mask.beforefirst, vp.merge, matrix.transpose, and
    experimental vector intrinsics. -/
def evalPureDetIntrinsic? (cfg : SemanticsConfig) (name : String) (retTy : LlvmRetType)
    (_fmf : FastMathFlags) (argVals : List RegisterValue) :
    Option (Except ExecError RegisterValue) :=
  if strHasPrefix name "llvm.sshl.sat" || strHasPrefix name "llvm.ushl.sat" then
    some <| match argVals with
      | [v1, v2] =>
        let isSigned := strHasPrefix name "llvm.sshl.sat"
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
        liftBinaryPure resElemTy v1 v2 fun a b =>
          match a, b with
          | .bv w1 (.value x), .bv w2 (.value amt) =>
            if h : w1 = w2 then
              let x' : BitVec w2 := h ▸ x
              if amt.toNat ≥ w2 then .ok (.bv w2 .poison)
              else if !isSigned then
                let shifted := x'.toNat <<< amt.toNat
                let res := if shifted ≥ (1 <<< w2) then BitVec.allOnes w2 else BitVec.ofNat w2 shifted
                .ok (.bv w2 (.value res))
              else
                let shifted : Int := x'.toInt * Int.ofNat (1 <<< amt.toNat)
                let hi : Int := Int.ofNat (1 <<< (w2 - 1)) - 1
                let lo : Int := -(Int.ofNat (1 <<< (w2 - 1)))
                let clamped := if shifted > hi then hi else if shifted < lo then lo else shifted
                .ok (.bv w2 (.value (BitVec.ofInt w2 clamped)))
            else .error (.staticError "width mismatch in sshl.sat/ushl.sat")
          | .bv w _, _ => .ok (.bv w .poison)
          | _, _ => .error (.staticError s!"{name} expects integer arguments")
      | _ => .error (.staticError s!"{name} expects 2 arguments")
  else if strHasPrefix name "llvm.scmp" || strHasPrefix name "llvm.ucmp" then
    some <| match argVals with
      | [v1, v2] =>
        let isSigned := strHasPrefix name "llvm.scmp"
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i8
        let rw := match resElemTy with | .int w => w | _ => 8
        liftBinaryPure resElemTy v1 v2 fun a b =>
          match a, b with
          | .bv w1 (.value x), .bv w2 (.value y) =>
            if h : w1 = w2 then
              let x' : BitVec w2 := h ▸ x
              let cmp : Int :=
                if isSigned then
                  if x'.toInt < y.toInt then -1 else if x'.toInt > y.toInt then 1 else 0
                else
                  if x'.toNat < y.toNat then -1 else if x'.toNat > y.toNat then 1 else 0
              .ok (.bv rw (.value (BitVec.ofInt rw cmp)))
            else .error (.staticError "width mismatch in scmp/ucmp")
          | .bv _ _, _ => .ok (.bv rw .poison)
          | _, _ => .error (.staticError s!"{name} expects integer arguments")
      | _ => .error (.staticError s!"{name} expects 2 arguments")
  else if strHasPrefix name "llvm.smulh" || strHasPrefix name "llvm.umulh" then
    some <| match argVals with
      | [v1, v2] =>
        let isSigned := strHasPrefix name "llvm.smulh"
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
        liftBinaryPure resElemTy v1 v2 fun a b =>
          match a, b with
          | .bv w1 (.value x), .bv w2 (.value y) =>
            if h : w1 = w2 then
              let x' : BitVec w2 := h ▸ x
              if !isSigned then
                .ok (.bv w2 (.value (BitVec.ofNat w2 ((x'.toNat * y.toNat) >>> w2))))
              else
                let prod : Int := x'.toInt * y.toInt
                let q : Int := Int.fdiv prod (Int.ofNat (1 <<< w2))
                .ok (.bv w2 (.value (BitVec.ofInt w2 q)))
            else .error (.staticError "width mismatch in smulh/umulh")
          | .bv w _, _ => .ok (.bv w .poison)
          | _, _ => .error (.staticError s!"{name} expects integer arguments")
      | _ => .error (.staticError s!"{name} expects 2 arguments")
  else if strHasPrefix name "llvm.clmul" then
    some <| match argVals with
      | [v1, v2] =>
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
        liftBinaryPure resElemTy v1 v2 fun a b =>
          match a, b with
          | .bv w1 (.value x), .bv w2 (.value y) =>
            if h : w1 = w2 then
              let x' : BitVec w2 := h ▸ x
              let acc := (List.range w2).foldl (init := 0) fun acc i =>
                if ((y.toNat >>> i) &&& 1) == 1 then acc ^^^ (x'.toNat <<< i) else acc
              .ok (.bv w2 (.value (BitVec.ofNat w2 acc)))
            else .error (.staticError "width mismatch in clmul")
          | .bv w _, _ => .ok (.bv w .poison)
          | _, _ => .error (.staticError "llvm.clmul expects integer arguments")
      | _ => .error (.staticError "llvm.clmul expects 2 arguments")
  else if strHasPrefix name "llvm.pdep" || strHasPrefix name "llvm.pext" then
    some <| match argVals with
      | [v1, v2] =>
        let isDep := strHasPrefix name "llvm.pdep"
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
        liftBinaryPure resElemTy v1 v2 fun a b =>
          match a, b with
          | .bv w1 (.value src), .bv w2 (.value mask) =>
            if h : w1 = w2 then
              let src' : BitVec w2 := h ▸ src
              let (res, _) := (List.range w2).foldl (init := (0, 0)) fun (acc, k) i =>
                if ((mask.toNat >>> i) &&& 1) == 1 then
                  if isDep then
                    let bit := (src'.toNat >>> k) &&& 1
                    (acc ||| (bit <<< i), k + 1)
                  else
                    let bit := (src'.toNat >>> i) &&& 1
                    (acc ||| (bit <<< k), k + 1)
                else (acc, k)
              .ok (.bv w2 (.value (BitVec.ofNat w2 res)))
            else .error (.staticError "width mismatch in pdep/pext")
          | .bv w _, _ => .ok (.bv w .poison)
          | _, _ => .error (.staticError s!"{name} expects integer arguments")
      | _ => .error (.staticError s!"{name} expects 2 arguments")
  else if strHasPrefix name "llvm.vscale" then
    some <| match retTy with
      | .ret (.int w) =>
        if cfg.vscale >= (1 <<< w) then .ok (.bv w .poison)
        else .ok (.bv w (.value (BitVec.ofNat w cfg.vscale)))
      | _ => .error (.staticError "llvm.vscale expects integer return type")
  else if strHasPrefix name "llvm.stepvector" then
    some <| match retTy with
      | .ret (.vector n (.int w)) =>
        let elems := (List.range n).map fun i => RegisterValue.bv w (.value (BitVec.ofNat w i))
        .ok (.vector (.int w) elems)
      | _ => .error (.staticError "llvm.stepvector expects integer vector return type")
  else if strHasPrefix name "llvm.vector.reverse" then
    some <| match argVals with
      | [.vector elemTy elems] => .ok (.vector elemTy elems.reverse)
      | _ => .error (.staticError "llvm.vector.reverse expects 1 vector argument")
  else if strHasPrefix name "llvm.vector.extract" then
    some <| match argVals, retTy with
      | [.vector elemTy elems, .bv _ (.value idxBV)], .ret (.vector subLen _) =>
        let idx := idxBV.toNat
        if idx + subLen > elems.length then
          .ok (.vector elemTy (List.replicate subLen (poisonOf elemTy)))
        else
          .ok (.vector elemTy ((elems.drop idx).take subLen))
      | [.vector elemTy _, .bv _ .poison], .ret (.vector subLen _) =>
        .ok (.vector elemTy (List.replicate subLen (poisonOf elemTy)))
      | _, _ => .error (.staticError "llvm.vector.extract expects (vector, int)")
  else if strHasPrefix name "llvm.vector.insert" then
    some <| match argVals with
      | [.vector elemTy dst, .vector _ src, .bv _ (.value idxBV)] =>
        let idx := idxBV.toNat
        if idx + src.length > dst.length then
          .ok (.vector elemTy (List.replicate dst.length (poisonOf elemTy)))
        else
          .ok (.vector elemTy ((dst.take idx) ++ src ++ (dst.drop (idx + src.length))))
      | [.vector elemTy dst, .vector _ _, .bv _ .poison] =>
        .ok (.vector elemTy (List.replicate dst.length (poisonOf elemTy)))
      | _ => .error (.staticError "llvm.vector.insert expects (vector, vector, int)")
  else if strHasPrefix name "llvm.vector.interleave" then
    some <| match argVals with
      | .vector elemTy first :: rest =>
        let vecs := first :: rest.map (fun | .vector _ es => es | _ => [])
        let n := first.length
        let out := (List.range n).flatMap fun i =>
          vecs.map fun v => v.getD i (poisonOf elemTy)
        .ok (.vector elemTy out)
      | _ => .error (.staticError s!"{name} expects vector arguments")
  else if strHasPrefix name "llvm.vector.deinterleave" then
    some <| match argVals, retTy with
      | [.vector elemTy elems], .ret (.struct packed fieldTys) =>
        let k := fieldTys.length
        if k == 0 then .error (.staticError s!"{name}: empty struct return")
        else
          let n := elems.length / k
          let fields := (List.range k).map fun j =>
            RegisterValue.vector elemTy ((List.range n).map fun i => elems.getD (i * k + j) (poisonOf elemTy))
          .ok (.struct packed fieldTys fields)
      | _, _ => .error (.staticError s!"{name} expects 1 vector argument and struct return")
  else if strHasPrefix name "llvm.vector.splice.left" || strHasPrefix name "llvm.vector.splice.right" then
    some <| match argVals with
      | [.vector elemTy v1, .vector _ v2, .bv _ (.value idxBV)] =>
        let len := v1.length
        let idx := idxBV.toNat
        if idx > len then
          .ok (.vector elemTy (List.replicate len (poisonOf elemTy)))
        else if strHasPrefix name "llvm.vector.splice.left" then
          .ok (.vector elemTy ((v1.drop idx) ++ (v2.take idx)))
        else
          let off := len - idx
          .ok (.vector elemTy ((v1.drop off) ++ (v2.take off)))
      | [.vector elemTy v1, .vector _ _, .bv _ .poison] =>
        .ok (.vector elemTy (List.replicate v1.length (poisonOf elemTy)))
      | _ => .error (.staticError s!"{name} expects (vector, vector, int)")
  else if strHasPrefix name "llvm.get.active.lane.mask" then
    some <| match argVals, retTy with
      | [.bv _ (.value baseBV), .bv _ (.value nBV)], .ret (.vector len .i1) =>
        let base := baseBV.toNat
        let n := nBV.toNat
        let elems := (List.range len).map fun i =>
          let active := base < n && i < n - base
          RegisterValue.bv 1 (.value (BitVec.ofBool active))
        .ok (.vector .i1 elems)
      | [.bv _ _, .bv _ _], .ret (.vector len .i1) =>
        .ok (.vector .i1 (List.replicate len (.bv 1 .poison)))
      | _, _ => .error (.staticError "llvm.get.active.lane.mask expects 2 integers and <N x i1> return")
  else if strHasPrefix name "llvm.mask.beforefirst" then
    some <| match argVals with
      | [.vector .i1 elems] =>
        if elems.any RegisterValue.isScalarPoison then
          .ok (.vector .i1 (List.replicate elems.length (.bv 1 .poison)))
        else
          let rec go (seenTrue : Bool) : List RegisterValue → List RegisterValue
            | [] => []
            | e :: es =>
              if seenTrue then .bv 1 (.value 0#1) :: go true es
              else match e with
                | .bv 1 (.value b) =>
                  if b == 1#1 then .bv 1 (.value 0#1) :: go true es
                  else .bv 1 (.value 1#1) :: go false es
                | _ => .bv 1 .poison :: go false es
          .ok (.vector .i1 (go false elems))
      | _ => .error (.staticError "llvm.mask.beforefirst expects <N x i1>")
  else if strHasPrefix name "llvm.vp.merge" then
    some <| match argVals with
      | [.vector _ mask, .vector elemTy onTrue, .vector _ onFalse, .bv _ (.value evlBV)] =>
        let len := onTrue.length
        let evl := evlBV.toNat
        if evl > len then
          .ok (.vector elemTy (List.replicate len (poisonOf elemTy)))
        else
          let out := (List.range len).map fun i =>
            if i ≥ evl then onFalse.getD i (poisonOf elemTy)
            else match mask.getD i (.bv 1 .poison) with
              | .bv 1 (.value b) =>
                if b == 1#1 then onTrue.getD i (poisonOf elemTy)
                else onFalse.getD i (poisonOf elemTy)
              | _ => poisonOf elemTy
          .ok (.vector elemTy out)
      | [.vector _ _, .vector elemTy onTrue, .vector _ _, .bv _ .poison] =>
        .ok (.vector elemTy (List.replicate onTrue.length (poisonOf elemTy)))
      | _ => .error (.staticError "llvm.vp.merge expects (mask, onTrue, onFalse, evl)")
  else if strHasPrefix name "llvm.matrix.transpose" then
    some <| match argVals with
      | [.vector elemTy elems, .bv _ (.value rBV), .bv _ (.value cBV)] =>
        let rows := rBV.toNat
        let cols := cBV.toNat
        let out := (List.range rows).flatMap fun r =>
          (List.range cols).map fun c =>
            elems.getD (c * rows + r) (poisonOf elemTy)
        .ok (.vector elemTy out)
      | _ => .error (.staticError "llvm.matrix.transpose expects (vector, rows, cols)")
  else if strHasPrefix name "llvm.experimental.cttz.elts" then
    some <| match argVals, retTy with
      | [.vector _ elems, .bv 1 (.value zpBV)], .ret (.int rw) =>
        if elems.any RegisterValue.isScalarPoison then .ok (.bv rw .poison)
        else
          let isZeroPoison := zpBV == 1#1
          let rec goCttz (idx : Nat) : List RegisterValue → RegisterValue
            | [] => if isZeroPoison then .bv rw .poison else .bv rw (.value (BitVec.ofNat rw elems.length))
            | e :: es =>
              match e with
              | .bv _ (.value b) => if b.toNat != 0 then .bv rw (.value (BitVec.ofNat rw idx)) else goCttz (idx + 1) es
              | _ => .bv rw .poison
          .ok (goCttz 0 elems)
      | [_, _], .ret (.int rw) => .ok (.bv rw .poison)
      | _, _ => .error (.staticError "llvm.experimental.cttz.elts expects (vector, i1)")
  else if strHasPrefix name "llvm.experimental.get.vector.length" then
    some <| match argVals, retTy with
      | [.bv _ (.value cntBV), .bv _ (.value vfBV), .bv 1 (.value scBV)], .ret (.int rw) =>
        let mult := if scBV == 1#1 then cfg.vscale else 1
        let maxLanes := vfBV.toNat * mult
        .ok (.bv rw (.value (BitVec.ofNat rw (min cntBV.toNat maxLanes))))
      | [_, _, _], .ret (.int rw) => .ok (.bv rw .poison)
      | _, _ => .error (.staticError "llvm.experimental.get.vector.length expects (cnt, vf, scalable)")
  else if strHasPrefix name "llvm.experimental.vector.compress" then
    some <| match argVals with
      | [.vector elemTy vec, .vector _ mask, .vector _ passthru] =>
        let hasPoisonMask := mask.any fun | .bv 1 (.value _) => false | _ => true
        if hasPoisonMask then
          .ok (.vector elemTy (List.replicate vec.length (poisonOf elemTy)))
        else
          let active := (List.range vec.length).filterMap fun i =>
            match mask.getD i (.bv 1 (.value 0#1)) with
            | .bv 1 (.value b) => if b == 1#1 then some (vec.getD i (poisonOf elemTy)) else none
            | _ => none
          let out := active ++ (passthru.drop active.length)
          .ok (.vector elemTy (out.take vec.length))
      | _ => .error (.staticError "llvm.experimental.vector.compress expects (vec, mask, passthru)")
  else if strHasPrefix name "llvm.experimental.vector.extract.last.active" then
    some <| match argVals with
      | [.vector elemTy vec, .vector _ mask, passthru] =>
        let rec findLast : List (RegisterValue × RegisterValue) → RegisterValue
          | [] => passthru
          | (v, m) :: rest =>
            match m with
            | .bv 1 (.value b) => if b == 1#1 then v else findLast rest
            | _ => poisonOf elemTy
        .ok (findLast (vec.zip mask).reverse)
      | _ => .error (.staticError "llvm.experimental.vector.extract.last.active expects (vec, mask, passthru)")
  else if strHasPrefix name "llvm.experimental.vector.match" then
    some <| match argVals with
      | [.vector _ vec, .vector _ setElems, .vector _ mask] =>
        let hasPoisonSet := setElems.any (·.containsPoison)
        let out := (vec.zip mask).map fun (x, m) =>
          match m with
          | .bv 1 (.value b) =>
            if b == 0#1 then RegisterValue.bv 1 (.value 0#1)
            else if x.containsPoison || hasPoisonSet then RegisterValue.bv 1 .poison
            else if setElems.any (fun s => !s.containsPoison && s == x) then RegisterValue.bv 1 (.value 1#1)
            else RegisterValue.bv 1 (.value 0#1)
          | _ => RegisterValue.bv 1 .poison
        .ok (.vector .i1 out)
      | [.vector _ vec, .vector _ setElems] =>
        let hasPoisonSet := setElems.any (·.containsPoison)
        let out := vec.map fun x =>
          if x.containsPoison then RegisterValue.bv 1 .poison
          else if setElems.any (fun s => !s.containsPoison && s == x) then RegisterValue.bv 1 (.value 1#1)
          else if hasPoisonSet then RegisterValue.bv 1 .poison
          else RegisterValue.bv 1 (.value 0#1)
        .ok (.vector .i1 out)
      | _ => .error (.staticError "llvm.experimental.vector.match expects (vec, set[, mask])")
  else if strHasPrefix name "llvm.vector.reduce.add" || strHasPrefix name "llvm.vector.reduce.mul" ||
          strHasPrefix name "llvm.vector.reduce.and" || strHasPrefix name "llvm.vector.reduce.or" ||
          strHasPrefix name "llvm.vector.reduce.xor" || strHasPrefix name "llvm.vector.reduce.smax" ||
          strHasPrefix name "llvm.vector.reduce.smin" || strHasPrefix name "llvm.vector.reduce.umax" ||
          strHasPrefix name "llvm.vector.reduce.umin" then
    some <| match argVals with
      | [.vector _ (first :: rest)] =>
        let combine {w : Nat} (a b : BitVec w) : BitVec w :=
          if strHasPrefix name "llvm.vector.reduce.add" then a + b
          else if strHasPrefix name "llvm.vector.reduce.mul" then a * b
          else if strHasPrefix name "llvm.vector.reduce.and" then a &&& b
          else if strHasPrefix name "llvm.vector.reduce.or" then a ||| b
          else if strHasPrefix name "llvm.vector.reduce.xor" then a ^^^ b
          else if strHasPrefix name "llvm.vector.reduce.smax" then if a.toInt ≥ b.toInt then a else b
          else if strHasPrefix name "llvm.vector.reduce.smin" then if a.toInt ≤ b.toInt then a else b
          else if strHasPrefix name "llvm.vector.reduce.umax" then if a.toNat ≥ b.toNat then a else b
          else if a.toNat ≤ b.toNat then a else b
        let rec goIntRed (acc : RegisterValue) : List RegisterValue → Except ExecError RegisterValue
          | [] => .ok acc
          | e :: es =>
            match acc, e with
            | .bv w1 (.value a), .bv w2 (.value b) =>
              if h : w1 = w2 then goIntRed (.bv w2 (.value (combine (h ▸ a) b))) es
              else .error (.staticError s!"width mismatch in {name}")
            | .bv w _, .bv _ _ => goIntRed (.bv w .poison) es
            | _, _ => .error (.staticError s!"expected integer elements in {name}")
        goIntRed first rest
      | _ => .error (.staticError s!"{name} expects a non-empty integer vector")
  else
    none

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
  else if name == "llvm.donothing" || name == "llvm.experimental.noalias.scope.decl" ||
          name == "llvm.inlineasm.noop" then
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
      | [v1, v2, v3] =>
        let isLeft := strHasPrefix name "llvm.fshl"
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
        let doScalar (a b c : RegisterValue) : Except ExecError RegisterValue :=
          match a, b, c with
          | .bv w1 (.value x), .bv w2 (.value y), .bv w3 (.value amt) =>
            if h1 : w1 = w3 then
              if h2 : w2 = w3 then
                let r := if isLeft then bvFshl (h1 ▸ x) (h2 ▸ y) amt else bvFshr (h1 ▸ x) (h2 ▸ y) amt
                .ok (.bv w3 (.value r))
              else .error (.staticError "width mismatch in fshl/fshr")
            else .error (.staticError "width mismatch in fshl/fshr")
          | .bv w _, _, _ => .ok (.bv w .poison)
          | _, _, _ => .error (.staticError s!"{name} expects 3 integer arguments")
        match v1, v2, v3 with
        | .vector _ xs, .vector _ ys, .vector _ zs =>
          let rec go : List RegisterValue → List RegisterValue → List RegisterValue → Except ExecError (List RegisterValue)
            | [], [], [] => .ok []
            | a :: as, b :: bs, c :: cs => do
              let r ← doScalar a b c
              let rs ← go as bs cs
              .ok (r :: rs)
            | _, _, _ => .error (.staticError "mismatched vector lengths in fshl/fshr")
          (go xs ys zs).map fun rs => (.vector resElemTy rs, o)
        | _, _, _ => (doScalar v1 v2 v3).map (·, o)
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
      | [v1, v2] =>
        let doScalar (a b : RegisterValue) : Except ExecError (RegisterValue × RegisterValue) :=
          match a, b with
          | .bv w1 (.value x), .bv w2 (.value y) =>
            if h : w1 = w2 then
              let x' : BitVec w2 := h ▸ x
              let (res, ov) :=
                if strHasPrefix name "llvm.sadd" then (x' + y, BitVec.saddOverflow x' y)
                else if strHasPrefix name "llvm.uadd" then (x' + y, BitVec.uaddOverflow x' y)
                else if strHasPrefix name "llvm.ssub" then (x' - y, BitVec.ssubOverflow x' y)
                else if strHasPrefix name "llvm.usub" then (x' - y, BitVec.usubOverflow x' y)
                else if strHasPrefix name "llvm.smul" then (x' * y, BitVec.smulOverflow x' y)
                else (x' * y, BitVec.umulOverflow x' y)
              .ok (.bv w2 (.value res), .bv 1 (.value (BitVec.ofBool ov)))
            else .error (.staticError "width mismatch in with.overflow intrinsic")
          | .bv w _, _ => .ok (.bv w .poison, .bv 1 .poison)
          | _, _ => .error (.staticError s!"{name} expects 2 integer arguments")
        match v1, v2 with
        | .vector elemTy xs, .vector _ ys =>
          let rec goOv : List RegisterValue → List RegisterValue → Except ExecError (List RegisterValue × List RegisterValue)
            | [], [] => .ok ([], [])
            | a :: as, b :: bs => do
              let (r, ov) ← doScalar a b
              let (rs, ovs) ← goOv as bs
              .ok (r :: rs, ov :: ovs)
            | _, _ => .error (.staticError "mismatched vector lengths in with.overflow intrinsic")
          (goOv xs ys).map fun (rs, ovs) =>
            let n := xs.length
            (.struct false [.vector n elemTy, .vector n .i1] [.vector elemTy rs, .vector .i1 ovs], o)
        | .bv w _, _ =>
          (doScalar v1 v2).map fun (r, ov) => (.struct false [.int w, .int 1] [r, ov], o)
        | _, _ => .error (.staticError s!"{name} expects 2 integer arguments")
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
      | [v1, v2, v3] =>
        let useFma := strHasPrefix name "llvm.fma" || cfg.fuseFMulAdd
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .f32
        let doScalar (ea eb ec : RegisterValue) (o0 : OracleState) : Except ExecError (RegisterValue × OracleState) :=
          match ea, eb, ec with
          | .float ft1 (.value a), .float ft2 (.value b), .float ft3 (.value c) =>
            if h1 : ft1 = ft3 then
              if h2 : ft2 = ft3 then
                let a' := h1 ▸ a
                let b' := h2 ▸ b
                let res :=
                  if useFma then IEEEFloat.fma cfg.roundingMode a' b' c
                  else IEEEFloat.add cfg.roundingMode (IEEEFloat.mul cfg.roundingMode a' b') c
                let (nanSign, o1) := o0.nextBool
                let (nanPick, o2) := o1.nextNat
                let final := applyNaNPropagation cfg.nanMode res [a', b', c] nanSign nanPick
                .ok (.float ft3 (handleFMF fmf false false final), o2)
              else .error (.staticError "Mismatched float types in llvm.fma")
            else .error (.staticError "Mismatched float types in llvm.fma")
          | .float ft _, _, _ => .ok (.float ft .poison, o0)
          | _, _, _ => .error (.staticError s!"{name} expects 3 float arguments")
        match v1, v2, v3 with
        | .vector _ xs, .vector _ ys, .vector _ zs =>
          let rec goFma : List RegisterValue → List RegisterValue → List RegisterValue → OracleState →
              Except ExecError (List RegisterValue × OracleState)
            | [], [], [], o0 => .ok ([], o0)
            | a :: as, b :: bs, c :: cs, o0 => do
              let (r, o1) ← doScalar a b c o0
              let (rs, o2) ← goFma as bs cs o1
              .ok (r :: rs, o2)
            | _, _, _, _ => .error (.staticError "Mismatched vector lengths in llvm.fma")
          (goFma xs ys zs o).map fun (rs, o') => (.vector resElemTy rs, o')
        | _, _, _ => doScalar v1 v2 v3 o
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
  else if strHasPrefix name "llvm.ceil" || strHasPrefix name "llvm.floor" ||
          strHasPrefix name "llvm.trunc" || strHasPrefix name "llvm.roundeven" ||
          strHasPrefix name "llvm.round" || strHasPrefix name "llvm.rint" ||
          strHasPrefix name "llvm.nearbyint" || strHasPrefix name "llvm.canonicalize" ||
          strHasPrefix name "llvm.sqrt" then
    some <| match argVals with
      | [v] =>
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .f32
        let applyUnaryOp {fmt : FloatFormat} (x : IEEEFloat fmt) : IEEEFloat fmt :=
          if strHasPrefix name "llvm.ceil" then x.ceil
          else if strHasPrefix name "llvm.floor" then x.floor
          else if strHasPrefix name "llvm.trunc" then x.trunc
          else if strHasPrefix name "llvm.roundeven" then x.roundeven
          else if strHasPrefix name "llvm.round" then x.round
          else if strHasPrefix name "llvm.rint" || strHasPrefix name "llvm.nearbyint" then
            x.roundToIntegral cfg.roundingMode
          else if strHasPrefix name "llvm.canonicalize" then x.canonicalize
          else x.sqrt cfg.roundingMode
        let goElem (e : RegisterValue) (o0 : OracleState) : Except ExecError (RegisterValue × OracleState) :=
          match e with
          | .float ft .poison => .ok (.float ft .poison, o0)
          | .float ft (.value flt) =>
            let (flipZ, o1) := o0.nextBool
            match handleFMF fmf true flipZ flt with
            | .poison => .ok (.float ft .poison, o1)
            | .value f' =>
              let raw := applyUnaryOp f'
              let (nanSign, o2) := o1.nextBool
              let (nanPick, o3) := o2.nextNat
              let final := applyNaNPropagation cfg.nanMode raw [f'] nanSign nanPick
              .ok (.float ft (handleFMF fmf false false final), o3)
          | other => .error (.staticError s!"Expected float in {name}, got {other}")
        match v with
        | .vector _ elems =>
          let rec goFPUnary : List RegisterValue → OracleState → Except ExecError (List RegisterValue × OracleState)
            | [], o0 => .ok ([], o0)
            | e :: es, o0 => do
              let (r, o1) ← goElem e o0
              let (rs, o2) ← goFPUnary es o1
              .ok (r :: rs, o2)
          match goFPUnary elems o with
          | .ok (rs, o') => .ok (.vector resElemTy rs, o')
          | .error e => .error e
        | _ => goElem v o
      | _ => .error (.staticError s!"{name} expects 1 argument")
  else if strHasPrefix name "llvm.ldexp" then
    some <| match argVals with
      | [v1, v2] =>
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .f32
        let goElem (a b : RegisterValue) (o0 : OracleState) : Except ExecError (RegisterValue × OracleState) :=
          match a, b with
          | .float ft (.value flt), .bv _ (.value expBv) =>
            let (flipZ, o1) := o0.nextBool
            match handleFMF fmf true flipZ flt with
            | .poison => .ok (.float ft .poison, o1)
            | .value f' =>
              let raw := f'.ldexp cfg.roundingMode expBv.toInt
              let (nanSign, o2) := o1.nextBool
              let (nanPick, o3) := o2.nextNat
              let final := applyNaNPropagation cfg.nanMode raw [f'] nanSign nanPick
              .ok (.float ft (handleFMF fmf false false final), o3)
          | .float ft _, .bv _ _ => .ok (.float ft .poison, o0)
          | _, _ => .error (.staticError "Expected (float, int) in llvm.ldexp")
        match v1, v2 with
        | .vector _ es1, .vector _ es2 =>
          if es1.length != es2.length then .error (.staticError "Vector length mismatch in llvm.ldexp")
          else
            let rec goLdexp : List RegisterValue → List RegisterValue → OracleState →
                Except ExecError (List RegisterValue × OracleState)
              | x :: xs, y :: ys, o0 => do
                let (r, o1) ← goElem x y o0
                let (rs, o2) ← goLdexp xs ys o1
                .ok (r :: rs, o2)
              | _, _, o0 => .ok ([], o0)
            match goLdexp es1 es2 o with
            | .ok (rs, o') => .ok (.vector resElemTy rs, o')
            | .error e => .error e
        | _, _ => goElem v1 v2 o
      | _ => .error (.staticError "llvm.ldexp expects 2 arguments")
  else if strHasPrefix name "llvm.vector.reduce.fadd" || strHasPrefix name "llvm.vector.reduce.fmul" then
    some <| match argVals with
      | [startV, .vector _ elems] =>
        let isAdd := strHasPrefix name "llvm.vector.reduce.fadd"
        let rec goFold (acc : RegisterValue) (es : List RegisterValue) (o0 : OracleState) :
            Except ExecError (RegisterValue × OracleState) :=
          match es with
          | [] => .ok (acc, o0)
          | e :: rest =>
            match acc, e with
            | .float ft1 (.value a), .float ft2 (.value b) =>
              if h : ft1 = ft2 then
                let a' : IEEEFloat ft2.format := h ▸ a
                let (flipL, o1) := o0.nextBool
                let (flipR, o2) := o1.nextBool
                match handleFMF fmf true flipL a', handleFMF fmf true flipR b with
                | .value fa, .value fb =>
                  let raw := if isAdd then IEEEFloat.add cfg.roundingMode fa fb
                             else IEEEFloat.mul cfg.roundingMode fa fb
                  let (nanSign, o3) := o2.nextBool
                  let (nanPick, o4) := o3.nextNat
                  let final := applyNaNPropagation cfg.nanMode raw [fa, fb] nanSign nanPick
                  goFold (.float ft2 (handleFMF fmf false false final)) rest o4
                | _, _ => goFold (.float ft2 .poison) rest o2
              else .error (.staticError s!"Mismatched float types in {name}")
            | .float ft _, .float _ _ => goFold (.float ft .poison) rest o0
            | _, _ => .error (.staticError s!"Expected float elements in {name}")
        goFold startV elems o
      | _ => .error (.staticError s!"{name} expects (float, vector) arguments")
  else if strHasPrefix name "llvm.vector.reduce.fmaximumnum" || strHasPrefix name "llvm.vector.reduce.fminimumnum" ||
          strHasPrefix name "llvm.vector.reduce.fmaximum" || strHasPrefix name "llvm.vector.reduce.fminimum" ||
          strHasPrefix name "llvm.vector.reduce.fmax" || strHasPrefix name "llvm.vector.reduce.fmin" then
    some <| match argVals with
      | [.vector _ (first :: rest)] =>
        let combine {fmt : FloatFormat} (x y : IEEEFloat fmt) : IEEEFloat fmt :=
          if strHasPrefix name "llvm.vector.reduce.fminimumnum" || strHasPrefix name "llvm.vector.reduce.fmin" then
            IEEEFloat.minimumnum x y
          else if strHasPrefix name "llvm.vector.reduce.fmaximumnum" || strHasPrefix name "llvm.vector.reduce.fmax" then
            IEEEFloat.maximumnum x y
          else if strHasPrefix name "llvm.vector.reduce.fminimum" then
            IEEEFloat.minimum x y
          else
            IEEEFloat.maximum x y
        let rec goRed (acc : RegisterValue) (es : List RegisterValue) (o0 : OracleState) :
            Except ExecError (RegisterValue × OracleState) :=
          match es with
          | [] => .ok (acc, o0)
          | e :: tl =>
            match acc, e with
            | .float ft1 (.value a), .float ft2 (.value b) =>
              if h : ft1 = ft2 then
                let a' : IEEEFloat ft2.format := h ▸ a
                let raw := combine a' b
                let (nanSign, o1) := o0.nextBool
                let (nanPick, o2) := o1.nextNat
                let final := applyNaNPropagation cfg.nanMode raw [a', b] nanSign nanPick
                goRed (.float ft2 (handleFMF fmf false false final)) tl o2
              else .error (.staticError s!"Mismatched float types in {name}")
            | .float ft _, .float _ _ => goRed (.float ft .poison) tl o0
            | _, _ => .error (.staticError s!"Expected float elements in {name}")
        goRed first rest o
      | _ => .error (.staticError s!"{name} expects a non-empty float vector argument")
  else
    (evalPureDetIntrinsic? cfg name retTy fmf argVals).map fun r => r.map (·, o)

/-- Decode a concrete `MemByte` into a `Nat` in `0..255`, returning `none` if any bit is poison/undef. -/
private def memByteToConcreteNat? (mb : MemByte) : Option Nat :=
  match mb.b0, mb.b1, mb.b2, mb.b3, mb.b4, mb.b5, mb.b6, mb.b7 with
  | .concrete k0 _, .concrete k1 _, .concrete k2 _, .concrete k3 _,
    .concrete k4 _, .concrete k5 _, .concrete k6 _, .concrete k7 _ =>
    let b (k : Bool) (sh : Nat) : Nat := if k then (1 <<< sh) else 0
    some (b k0 0 + b k1 1 + b k2 2 + b k3 3 + b k4 4 + b k5 5 + b k6 6 + b k7 7)
  | _, _, _, _, _, _, _, _ => none

/-- Read a null-terminated C string from memory, raising Immediate UB on invalid/OOB/uninit/poison reads. -/
def readCStringPure (mem : MemoryState) (p : Pointer) : Except ExecError String :=
  match mem.resolveObject? p with
  | none => .error (.immediateUB "Invalid memory access via a pointer with nullary provenance")
  | some mo =>
    if mo.state == .freed || mo.state == .dead then
      .error (.immediateUB s!"Use-after-free while reading C-string from '{mo.name}'")
    else if p.addr.toNat < mo.baseAddr || p.addr.toNat ≥ mo.baseAddr + mo.size then
      .error (.immediateUB s!"Out-of-bounds read while parsing C-string in '{mo.name}'")
    else
      let startOff := p.addr.toNat - mo.baseAddr
      let maxFuel := mo.size - startOff
      let rec go (off : Nat) (fuel : Nat) (acc : List Char) : Except ExecError String :=
        match fuel with
        | 0 => .error (.immediateUB "Out-of-bounds read while parsing C-string (missing null terminator)")
        | fuel' + 1 =>
          match memByteToConcreteNat? (mo.bytes.getD off MemByte.poison) with
          | none => .error (.immediateUB s!"Read uninitialized or poison memory while parsing C-string at offset {off - startOff}")
          | some 0 => .ok (String.ofList acc.reverse)
          | some byte => go (off + 1) fuel' (Char.ofNat byte :: acc)
      go startOff maxFuel []

private def padLeft (s : String) (width : Nat) (padChar : Char) : String :=
  if s.length ≥ width then s
  else String.ofList (List.replicate (width - s.length) padChar) ++ s

private def formatNatBase (n : Nat) (base : Nat) (upper : Bool) : String :=
  let digits := Nat.toDigits base n
  String.ofList (digits.map fun c => if upper && 'a' ≤ c && c ≤ 'z' then Char.ofNat (c.toNat - 32) else c)

private def formatSignedDec (x : Int) (width : Nat) (zeroPad : Bool) : String :=
  if x < 0 then
    let mag := toString (-x).toNat
    if zeroPad && width > 1 then "-" ++ padLeft mag (width - 1) '0'
    else padLeft ("-" ++ mag) width ' '
  else
    let mag := toString x.toNat
    padLeft mag width (if zeroPad then '0' else ' ')

private def formatPrintfFloat (flt : IEEEFloat ft) (spec : Char) : String :=
  let upper := spec == 'F' || spec == 'E' || spec == 'G' || spec == 'A'
  if flt.isNaN then
    let s := if upper then "NAN" else "nan"
    if flt.sign then "-" ++ s else s
  else if flt.isInf then
    let s := if upper then "INF" else "inf"
    if flt.sign then "-" ++ s else s
  else
    -- Standard C `%f`/`%e`/`%g` default 6-digit formatting (exact length for `printf` return value)
    -- Convert to Lean `Float` for finite display when double/float, using exact IEEE bits.
    let f64 : Float := (IEEEFloat.convert FloatFormat.double .RNE flt).toLeanFloat
    let isNeg := flt.sign
    let absF := if isNeg then -f64 else f64
    let pfx := if isNeg then "-" else ""
    if spec == 'g' || spec == 'G' then
      let s := toString absF
      let s' :=
        if s.contains '.' then
          let trimmed := s.toList.reverse.dropWhile (· == '0')
          let trimmed := match trimmed with | '.' :: rest => rest | other => other
          String.ofList trimmed.reverse
        else s
      pfx ++ s'
    else if spec == 'e' || spec == 'E' then
      -- Scientific notation `d.ddddddE±dd` (always 12 chars for 2-digit exp, plus optional `-`)
      let eChar := if upper then "E" else "e"
      if absF == 0.0 then pfx ++ s!"0.000000{eChar}+00"
      else
        let rec norm (v : Float) (e : Int) (fuel : Nat) : Float × Int :=
          match fuel with
          | 0 => (v, e)
          | fuel' + 1 =>
            if v ≥ 10.0 then norm (v / 10.0) (e + 1) fuel'
            else if v < 1.0 then norm (v * 10.0) (e - 1) fuel'
            else (v, e)
        let (m, exp) := norm absF 0 400
        let scaled : Nat := (m * 1000000.0 + 0.5).toUInt64.toNat
        let intPart := scaled / 1000000
        let fracPart := padLeft (toString (scaled % 1000000)) 6 '0'
        let expSign := if exp < 0 then "-" else "+"
        let expStr := padLeft (toString exp.natAbs) 2 '0'
        pfx ++ s!"{intPart}.{fracPart}{eChar}{expSign}{expStr}"
    else
      -- Fixed `%f`/`%F` with 6 decimal places
      let scaled : Nat := (absF * 1000000.0 + 0.5).toUInt64.toNat
      let intPart := scaled / 1000000
      let fracPart := padLeft (toString (scaled % 1000000)) 6 '0'
      pfx ++ s!"{intPart}.{fracPart}"

/-- Parse and handle a single `%...` format specifier in `printf`, returning
    `(remainingChars, remainingArgs, optionalWritePatch, newWritten)`. -/
private def evalPrintfSpec (dl : DataLayout) (rest : List Char) (args : List RegisterValue)
    (mem : MemoryState) (written : Nat) :
    Except ExecError (List Char × List RegisterValue × Option (AllocId × Nat × Array MemByte) × Nat) :=
  let rec skipFlags (zeroPad : Bool) : List Char → Bool × List Char
    | '-' :: cs => skipFlags zeroPad cs
    | '+' :: cs => skipFlags zeroPad cs
    | ' ' :: cs => skipFlags zeroPad cs
    | '#' :: cs => skipFlags zeroPad cs
    | '0' :: cs => skipFlags true cs
    | cs => (zeroPad, cs)
  let (zeroPad, cs1) := skipFlags false rest
  let rec parseWidth (acc : Nat) : List Char → Nat × List Char
    | c :: cs => if '0' ≤ c && c ≤ '9' then parseWidth (acc * 10 + (c.toNat - '0'.toNat)) cs else (acc, c :: cs)
    | [] => (acc, [])
  let (width, cs2) := parseWidth 0 cs1
  let cs3 := match cs2 with
    | '.' :: afterDot => (parseWidth 0 afterDot).2
    | other => other
  let (lenMod, cs4) := match cs3 with
    | 'h' :: 'h' :: cs => ("hh", cs)
    | 'h' :: cs => ("h", cs)
    | 'l' :: 'l' :: cs => ("ll", cs)
    | 'l' :: cs => ("l", cs)
    | 'j' :: cs => ("j", cs)
    | 'z' :: cs => ("z", cs)
    | 't' :: cs => ("t", cs)
    | 'L' :: cs => ("L", cs)
    | cs => ("", cs)
  match cs4 with
  | [] => .error (.immediateUB "Incomplete format specifier in printf")
  | spec :: tail =>
    match spec with
    | 'd' | 'i' | 'u' | 'o' | 'x' | 'X' | 'c' =>
      match args with
      | [] => .error (.immediateUB s!"Not enough arguments provided for the format string. Required argument for '{spec}'.")
      | arg :: restArgs =>
        match arg with
        | .bv _ .poison => .error (.immediateUB "Poison argument passed to printf")
        | .bv w (.value bv) =>
          let validW := if lenMod == "h" || lenMod == "hh" then w ≥ 8 && w ≤ 64 else w ≥ 32 && w ≤ 64
          if !validW then
            .error (.immediateUB s!"Argument type mismatch in printf for format specifier '{spec}'")
          else
            let formatted :=
              if spec == 'd' || spec == 'i' then formatSignedDec bv.toInt width zeroPad
              else if spec == 'u' then padLeft (toString bv.toNat) width (if zeroPad then '0' else ' ')
              else if spec == 'o' then padLeft (formatNatBase bv.toNat 8 false) width (if zeroPad then '0' else ' ')
              else if spec == 'x' then padLeft (formatNatBase bv.toNat 16 false) width (if zeroPad then '0' else ' ')
              else if spec == 'X' then padLeft (formatNatBase bv.toNat 16 true) width (if zeroPad then '0' else ' ')
              else String.singleton (Char.ofNat (bv.toNat % 256))
            .ok (tail, restArgs, none, written + formatted.length)
        | _ => .error (.immediateUB s!"Argument type mismatch in printf for format specifier '{spec}'")
    | 'f' | 'F' | 'e' | 'E' | 'g' | 'G' | 'a' | 'A' =>
      match args with
      | [] => .error (.immediateUB s!"Not enough arguments provided for the format string. Required argument for '{spec}'.")
      | arg :: restArgs =>
        match arg with
        | .float _ .poison => .error (.immediateUB "Poison argument passed to printf")
        | .float .double (.value flt) =>
          let formatted := formatPrintfFloat flt spec
          .ok (tail, restArgs, none, written + formatted.length)
        | _ => .error (.immediateUB s!"Argument type mismatch in printf for format specifier '{spec}'")
    | 'p' =>
      match args with
      | [] => .error (.immediateUB "Not enough arguments provided for the format string. Required argument for 'p'.")
      | arg :: restArgs =>
        match arg with
        | .ptr _ .poison => .error (.immediateUB "Poison argument passed to printf")
        | .ptr _ (.value p) =>
          if p.addrWidth > 64 then
            .error (.immediateUB "Argument type mismatch in printf for format specifier 'p' (pointer too wide)")
          else
            let formatted := if p.addr.toNat == 0 then "(nil)" else "0x" ++ formatNatBase p.addr.toNat 16 false
            .ok (tail, restArgs, none, written + formatted.length)
        | _ => .error (.immediateUB "Argument type mismatch in printf for format specifier 'p'")
    | 's' =>
      match args with
      | [] => .error (.immediateUB "Not enough arguments provided for the format string. Required argument for 's'.")
      | arg :: restArgs =>
        match arg with
        | .ptr _ .poison => .error (.immediateUB "Poison argument passed to printf")
        | .ptr _ (.value p) =>
          if p.addrWidth > 64 then
            .error (.immediateUB "Argument type mismatch in printf for format specifier 's' (pointer too wide)")
          else
            match readCStringPure mem p with
            | .error e => .error e
            | .ok s => .ok (tail, restArgs, none, written + s.length)
        | _ => .error (.immediateUB "Argument type mismatch in printf for format specifier 's'")
    | 'n' =>
      match args with
      | [] => .error (.immediateUB "Not enough arguments provided for the format string. Required argument for 'n'.")
      | arg :: restArgs =>
        match arg with
        | .ptr _ .poison => .error (.immediateUB "Poison argument passed to printf")
        | .ptr _ (.value p) =>
          match mem.verifyMemAccess p 4 1 true with
          | .error e => .error e
          | .ok (mo, off) =>
            let bytes := valueToBytes dl .modern (.bv 32 (.value (BitVec.ofNat 32 written))) (.int 32)
            .ok (tail, restArgs, some (mo.allocId, off, bytes), written)
        | _ => .error (.immediateUB "Argument type mismatch in printf for format specifier 'n'")
    | _ => .error (.immediateUB s!"Unknown or unsupported format specifier '{spec}' in printf")

/-- Format-string interpreter for C `printf` (fuel-bounded over format length). -/
def evalPrintfLoop (dl : DataLayout) :
    Nat → List Char → List RegisterValue → MemoryState → Nat → Except ExecError (Nat × MemoryState)
  | 0, _, _, mem, written => .ok (written, mem)
  | _ + 1, [], _, mem, written => .ok (written, mem)
  | fuel + 1, '%' :: '%' :: rest, args, mem, written =>
    evalPrintfLoop dl fuel rest args mem (written + 1)
  | fuel + 1, '%' :: rest, args, mem, written =>
    match evalPrintfSpec dl rest args mem written with
    | .error e => .error e
    | .ok (tail, restArgs, patch?, written') =>
      let mem' := match patch? with
        | none => mem
        | some (aid, off, bytes) => mem.writeObjectBytes aid off bytes
      evalPrintfLoop dl fuel tail restArgs mem' written'
  | fuel + 1, _ :: rest, args, mem, written =>
    evalPrintfLoop dl fuel rest args mem (written + 1)

theorem evalPrintfLoop_preserves_wf {dl fuel cs args mem written n mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : evalPrintfLoop dl fuel cs args mem written = .ok (n, mem')) :
    MemoryState.WellFormed mem' := by
  induction fuel generalizing cs args mem written with
  | zero => unfold evalPrintfLoop at h; cases h; exact hwf
  | succ fuel ih =>
    unfold evalPrintfLoop at h
    split at h
    · cases h; exact hwf
    · cases h; exact hwf
    · rename_i _ _ _ _ _ _ _ _ _ heq; cases heq; exact ih hwf h
    · rename_i _ _ _ _ _ _ _ _ _ heq; cases heq
      cases hs : evalPrintfSpec dl _ _ _ _ with
      | error e => rw [hs] at h; cases h
      | ok p =>
        rw [hs] at h; obtain ⟨t, ra, patch?, w1⟩ := p; dsimp only at h
        cases patch? with
        | none => exact ih hwf h
        | some w => exact ih (MemoryState.writeObjectBytes_preserves_wf hwf w.1 w.2.1 w.2.2) h
    · rename_i _ _ _ _ _ _ _ _ _ _ _ _ heq; cases heq; exact ih hwf h

/-- Non-allocating C/C++ standard library calls (`free`, `_ZdlPv`, `memcpy`, `memmove`, `memset`, `puts`, `putchar`, `printf`, `exit`, `abort`, `_ZSt9terminatev`). -/
def evalNonAllocLibcall? (dl : DataLayout) (mem : MemoryState)
    (name : String) (argVals : List RegisterValue) :
    Option (Except ExecError (RegisterValue × MemoryState)) :=
  if name == "free" || name == "_ZdlPv" || name == "_ZdaPv" || name == "_ZdlPvm" || name == "_ZdaPvm" then
    some <| match argVals with
      | .ptr _ .poison :: _ => .error (.immediateUB "free/delete called with poison pointer")
      | .ptr as (.value p) :: _ =>
        if p.isNull dl as then .ok (.void, mem)
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
              .ok (.void, mem.freeObject mo.allocId)
      | _ => .error (.staticError "free/delete expects pointer argument")
  else if name == "memcpy" then
    some <| match argVals with
      | [dst, src, len] => (execMemTransferPure mem dst src len false true).map (fun m' => (dst, m'))
      | _ => .error (.staticError "memcpy expects 3 arguments")
  else if name == "memmove" then
    some <| match argVals with
      | [dst, src, len] => (execMemTransferPure mem dst src len true true).map (fun m' => (dst, m'))
      | _ => .error (.staticError "memmove expects 3 arguments")
  else if name == "memset" then
    some <| match argVals with
      | [dst, val, len] => (execMemSetPure mem dst val len).map (fun m' => (dst, m'))
      | _ => .error (.staticError "memset expects 3 arguments")
  else if name == "puts" then
    some <| match argVals with
      | [.ptr _ .poison] => .error (.immediateUB "Poison argument passed to a library call at argument index 0")
      | [.ptr _ (.value p)] =>
        match readCStringPure mem p with
        | .error e => .error e
        | .ok _ => .ok (.bv 32 (.value (BitVec.ofNat 32 1)), mem)
      | _ => .error (.staticError "puts expects 1 pointer argument")
  else if name == "putchar" then
    some <| match argVals with
      | [.bv _ .poison] => .error (.immediateUB "Poison argument passed to putchar")
      | [.bv _ (.value bv)] => .ok (.bv 32 (.value (BitVec.ofNat 32 (bv.toNat % 256))), mem)
      | _ => .error (.staticError "putchar expects 1 integer argument")
  else if name == "printf" then
    some <| match argVals with
      | .ptr _ .poison :: _ => .error (.immediateUB "Poison argument passed to a library call at argument index 0")
      | .ptr _ (.value fmtPtr) :: restArgs =>
        match readCStringPure mem fmtPtr with
        | .error e => .error e
        | .ok fmtStr =>
          match evalPrintfLoop dl fmtStr.length fmtStr.toList restArgs mem 0 with
          | .error e => .error e
          | .ok (written, mem') => .ok (.bv 32 (.value (BitVec.ofNat 32 written)), mem')
      | _ => .error (.staticError "printf expects at least 1 pointer argument")
  else if name == "exit" then
    some <| match argVals with
      | [.bv _ .poison] => .error (.immediateUB "Poison argument passed to exit")
      | [.bv _ (.value bv)] => .error (.staticError s!"Program exited with code {bv.toInt}")
      | _ => .error (.staticError "exit expects 1 integer argument")
  else if name == "abort" then
    some (.error (.staticError "Program aborted."))
  else if name == "_ZSt9terminatev" then
    some (.error (.staticError "Program terminated."))
  else
    none

theorem evalNonAllocLibcall?_preserves_wf {dl mem name argVals res mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : evalNonAllocLibcall? dl mem name argVals = some (.ok (res, mem'))) :
    MemoryState.WellFormed mem' := by
  unfold evalNonAllocLibcall? at h
  split at h
  · match argVals, h with
    | .ptr _ .poison :: _, h => cases h
    | .ptr as (.value p) :: _, h =>
      dsimp only at h
      split at h
      · cases h; exact hwf
      · cases hres : mem.resolveObject? p with
        | none => rw [hres] at h; cases h
        | some mo =>
          rw [hres] at h; dsimp only at h
          split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · cases h; exact MemoryState.freeObject_preserves_wf hwf mo.allocId
  · split at h
    · match argVals, h with
      | [dst, src, len], h =>
        dsimp only at h
        cases ht : execMemTransferPure mem dst src len false true with
        | error e => rw [ht] at h; cases h
        | ok m1 => rw [ht] at h; cases h; exact execMemTransferPure_preserves_wf hwf ht
    · split at h
      · match argVals, h with
        | [dst, src, len], h =>
          dsimp only at h
          cases ht : execMemTransferPure mem dst src len true true with
          | error e => rw [ht] at h; cases h
          | ok m1 => rw [ht] at h; cases h; exact execMemTransferPure_preserves_wf hwf ht
      · split at h
        · match argVals, h with
          | [dst, val, len], h =>
            dsimp only at h
            cases ht : execMemSetPure mem dst val len with
            | error e => rw [ht] at h; cases h
            | ok m1 => rw [ht] at h; cases h; exact execMemSetPure_preserves_wf hwf ht
        · split at h
          · split at h
            · cases h
            · cases hr : readCStringPure mem _ with
              | error e => rw [hr] at h; cases h
              | ok s => rw [hr] at h; cases h; exact hwf
            · cases h
          · split at h
            · split at h
              · cases h
              · cases h; exact hwf
              · cases h
            · split at h
              · split at h
                · cases h
                · cases hr : readCStringPure mem _ with
                  | error e => rw [hr] at h; cases h
                  | ok fmtStr =>
                    rw [hr] at h; dsimp only at h
                    cases hp : evalPrintfLoop dl fmtStr.length fmtStr.toList _ mem 0 with
                    | error e => rw [hp] at h; cases h
                    | ok p =>
                      rw [hp] at h; cases h
                      exact evalPrintfLoop_preserves_wf hwf hp
                · cases h
              · split at h
                · split at h <;> cases h
                · split at h
                  · cases h
                  · split at h
                    · cases h
                    · cases h

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

/-- Sequentially execute active lanes of `llvm.experimental.vector.histogram.{add,uadd.sat,umax,umin}`. -/
private def execHistogramLoop (dl : DataLayout) (cfg : SemanticsConfig) (op : String)
    (w : Nat) (incVal : PoisonOr (BitVec w)) (mem : MemoryState) :
    List Pointer → Except ExecError MemoryState
  | [] => .ok mem
  | p :: rest =>
    let elemTy := LlvmType.int w
    match loadElemFromPtr dl cfg mem p elemTy 1 default with
    | .error e => .error e
    | .ok (curVal, _) =>
      let newVal : RegisterValue :=
        match curVal, incVal with
        | .bv w1 (.value x), .value inc =>
          if h : w1 = w then
            let x' : BitVec w := h ▸ x
            let r : BitVec w :=
              if op == "add" then x' + inc
              else if op == "uadd.sat" then bvUAddSat x' inc
              else if op == "umax" then if x'.toNat ≥ inc.toNat then x' else inc
              else if x'.toNat ≤ inc.toNat then x' else inc
            .bv w (.value r)
          else .bv w .poison
        | _, _ => .bv w .poison
      match storeElemToPtr dl cfg mem p elemTy newVal 1 with
      | .error e => .error e
      | .ok mem' => execHistogramLoop dl cfg op w incVal mem' rest

private theorem execHistogramLoop_preserves_wf {dl cfg op w incVal mem ptrs mem'}
    (hwf : MemoryState.WellFormed mem)
    (h : execHistogramLoop dl cfg op w incVal mem ptrs = .ok mem') :
    MemoryState.WellFormed mem' := by
  induction ptrs generalizing mem with
  | nil => unfold execHistogramLoop at h; cases h; exact hwf
  | cons p rest ih =>
    unfold execHistogramLoop at h; dsimp only at h
    cases hl : loadElemFromPtr dl cfg mem p (.int w) 1 default with
    | error e => rw [hl] at h; cases h
    | ok pair =>
      rw [hl] at h; dsimp only at h
      cases hs : storeElemToPtr dl cfg mem p (.int w) _ 1 with
      | error e => rw [hs] at h; cases h
      | ok m1 => rw [hs] at h; exact ih (storeElemToPtr_preserves_wf hwf hs) h

/-- Read-only vector/masked/VP/speculative memory load intrinsics (never modify `mem`). -/
def evalVecMemRead? (dl : DataLayout) (cfg : SemanticsConfig) (mem : MemoryState)
    (name : String) (retTy : LlvmRetType) (argVals : List RegisterValue) (o : OracleState)
    (argAttrs : List (List ValueAttr) := []) :
    Option (Except ExecError (RegisterValue × OracleState)) :=
  if strHasPrefix name "llvm.masked.load" then
    some <| match argVals, retTy with
      | [ptrVal, .vector _ mask, .vector elemTy passthru], .ret (.vector len _) =>
        if dl.typeSizeInBits elemTy % 8 != 0 then
          .error (.staticError s!"{name} with non-byte-sized element type is not supported")
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
                  | _ => .error (.immediateUB "poison/invalid pointer in llvm.masked.load")
                else goLoad (i + 1) o0 (passthru.getD i (poisonOf elemTy) :: acc)
              | _ => .error (.immediateUB "poison mask lane in llvm.masked.load")
          termination_by len - i
          (goLoad 0 o []).map fun (vs, o') => (.vector elemTy vs, o')
      | _, _ => .error (.staticError "llvm.masked.load expects (ptr, mask, passthru)")
  else if strHasPrefix name "llvm.masked.expandload" then
    some <| match argVals, retTy with
      | [ptrVal, .vector _ mask, .vector elemTy passthru], .ret (.vector len _) =>
        if dl.typeSizeInBits elemTy % 8 != 0 then
          .error (.staticError s!"{name} with non-byte-sized element type is not supported")
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
                  | _ => .error (.immediateUB "poison/invalid pointer in llvm.masked.expandload")
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
                | _ => .error (.immediateUB "poison/invalid pointer in llvm.masked.gather")
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
                      .error (.immediateUB "Misaligned pointer in llvm.vp.load")
                    else
                      match loadElemFromPtr dl cfg mem (ptrAddBytes dl p (Int.ofNat i * stride)) elemTy 1 o0 with
                      | .error e => .error e
                      | .ok (v, o1) => goVpLoad (i + 1) o1 (v :: acc)
                  | _ => .error (.immediateUB "poison/invalid pointer in llvm.vp.load")
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
                  | _ => .error (.immediateUB "poison/invalid pointer in llvm.vp.gather")
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
                      .error (.immediateUB "Misaligned pointer in llvm.experimental.vp.strided.load")
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
                  | _ => .error (.immediateUB "poison/invalid pointer in llvm.experimental.vp.strided.load")
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
          | .bv _ .poison :: _ => .error (.immediateUB "poison bound in llvm.speculative.load")
          | .bv _ (.value bBV) :: _ => .ok (min totalSz bBV.toNat)
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
        .error (.immediateUB "poison pointer or flag in llvm.speculative.load")
      | _, _ => .error (.staticError "llvm.speculative.load expects (ptr, i1, ...)")
  else
    none

private theorem evalVecMemRead?_none_indep {dl cfg mem name retTy argVals o o' argAttrs}
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
              .error (.immediateUB "Misaligned pointer in masked/vp store")
            else
              let idx := if compress then memIdx else i
              let p' := ptrAddBytes dl p (Int.ofNat idx * stride)
              go (i + 1) (memIdx + 1) ((p', vals.getD i (poisonOf elemTy)) :: acc)
          | _ => .error (.immediateUB "poison/invalid pointer in masked/vp store")
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
          | _ => .error (.immediateUB "poison/invalid pointer in masked/vp scatter")
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
          .error (.staticError s!"{name} with non-byte-sized element type is not supported")
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
                      .error (.immediateUB "Misaligned pointer in llvm.experimental.vp.strided.store")
                    else
                      let lanePtr? : Except ExecError Pointer :=
                        if i == 0 then .ok p
                        else match strideOpt with
                          | some stride => .ok (ptrAddBytes dl p (Int.ofNat i * stride))
                          | none => .error (.immediateUB "poison stride in llvm.experimental.vp.strided.store")
                      match lanePtr? with
                      | .error e => .error e
                      | .ok lp => collectStrided (i + 1) ((lp, vals.getD i (poisonOf elemTy)) :: acc)
                  | _ => .error (.immediateUB "poison/invalid pointer in llvm.experimental.vp.strided.store")
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
        if stride < rows then .error (.immediateUB "stride < rows in llvm.matrix.column.major.store")
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
              .error (.immediateUB "Invalid memory access with a poison pointer in llvm.matrix.column.major.store")
            else
              let ws := (List.range cols).flatMap fun c =>
                (List.range rows).map fun r =>
                  (ptrAddBytes dl p (Int.ofNat ((c * strideIdx + r) * elemSz)),
                   vals.getD (c * rows + r) (poisonOf elemTy))
              execStoreList dl cfg elemTy 1 mem ws
          | _ => .error (.immediateUB "poison/invalid pointer in llvm.matrix.column.major.store")
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
                | _ => .error (.immediateUB "poison/invalid pointer in vector.histogram")
              else collectPtrs (i + 1) acc
            | _ => .error (.immediateUB "poison mask lane in vector.histogram")
        termination_by ptrs.length - i
        match collectPtrs 0 [] with
        | .error e => .error e
        | .ok activePtrs => execHistogramLoop dl cfg op w incVal mem activePtrs
      | _ => .error (.staticError s!"{name} expects (ptrs, inc, mask)")
  else
    none

private theorem evalVecMemWrite?_preserves_wf {dl cfg mem name argVals argAttrs mem'}
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

/-- Non-allocating memory & pure intrinsics/libcalls (shared between `Step` and `Exec`). -/
def evalNonAllocIntrinsicExec? (dl : DataLayout) (cfg : SemanticsConfig) (mem : MemoryState)
    (name : String) (retTy : LlvmRetType) (fmf : FastMathFlags) (argVals : List RegisterValue)
    (o : OracleState) (allowLibcalls : Bool := true) (argAttrs : List (List ValueAttr) := []) :
    Option (Except ExecError (RegisterValue × MemoryState × OracleState)) :=
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
  else
    match evalVecMemRead? dl cfg mem name retTy argVals o argAttrs with
    | some r => some (r.map fun (v, o') => (v, mem, o'))
    | none =>
      match evalVecMemWrite? dl cfg mem name argVals argAttrs with
      | some r => some (r.map fun m' => (.void, m', o))
      | none =>
        match (if allowLibcalls then evalNonAllocLibcall? dl mem name argVals else none) with
        | some r => some (r.map fun (v, m') => (v, m', o))
        | none =>
          (evalPureIntrinsicExec? cfg name retTy fmf argVals o).map fun r =>
            r.map fun (v, o') => (v, mem, o')

theorem evalNonAllocIntrinsicExec?_preserves_wf {dl cfg mem name retTy fmf argVals o allowLibcalls argAttrs res mem' o'}
    (hwf : MemoryState.WellFormed mem)
    (h : evalNonAllocIntrinsicExec? dl cfg mem name retTy fmf argVals o allowLibcalls argAttrs = some (.ok (res, mem', o'))) :
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
            cases hvr : evalVecMemRead? dl cfg mem name retTy argVals o argAttrs with
            | some r =>
              rw [hvr] at h
              cases r with
              | error e => cases h
              | ok p => cases h; exact hwf
            | none =>
              rw [hvr] at h
              cases hvw : evalVecMemWrite? dl cfg mem name argVals argAttrs with
              | some r =>
                rw [hvw] at h
                cases r with
                | error e => cases h
                | ok m1 => cases h; exact evalVecMemWrite?_preserves_wf hwf hvw
              | none =>
                rw [hvw] at h
                cases hl : (if allowLibcalls then evalNonAllocLibcall? dl mem name argVals else none) with
                | some r =>
                  rw [hl] at h
                  cases r with
                  | error e => cases h
                  | ok p =>
                    cases h
                    by_cases ha : allowLibcalls = true
                    · rw [if_pos ha] at hl; exact evalNonAllocLibcall?_preserves_wf hwf hl
                    · rw [if_neg ha] at hl; cases hl
                | none =>
                  rw [hl] at h
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
  cases hd : evalPureDetIntrinsic? cfg name retTy fmf argVals with
  | some r => simp [hd] at h
  | none => rfl

/-- Whether `evalNonAllocIntrinsicExec?` recognizes a name is independent of the oracle. -/
theorem evalNonAllocIntrinsicExec?_none_indep {dl cfg mem name retTy fmf argVals o o' allowLibcalls argAttrs}
    (h : evalNonAllocIntrinsicExec? dl cfg mem name retTy fmf argVals o allowLibcalls argAttrs = none) :
    evalNonAllocIntrinsicExec? dl cfg mem name retTy fmf argVals o' allowLibcalls argAttrs = none := by
  unfold evalNonAllocIntrinsicExec? at h ⊢
  obtain ⟨hc1, h⟩ := ite_some_eq_none h; rw [if_neg hc1]
  obtain ⟨hc2, h⟩ := ite_some_eq_none h; rw [if_neg hc2]
  obtain ⟨hc3, h⟩ := ite_some_eq_none h; rw [if_neg hc3]
  obtain ⟨hc4, h⟩ := ite_some_eq_none h; rw [if_neg hc4]
  obtain ⟨hc5, h⟩ := ite_some_eq_none h; rw [if_neg hc5]
  cases hvr : evalVecMemRead? dl cfg mem name retTy argVals o argAttrs with
  | some r => simp [hvr] at h
  | none =>
    rw [evalVecMemRead?_none_indep (o' := o') hvr]
    simp only [hvr] at h
    cases hvw : evalVecMemWrite? dl cfg mem name argVals argAttrs with
    | some r => simp [hvw] at h
    | none =>
      simp only [hvw] at h
      cases hl : (if allowLibcalls = true then evalNonAllocLibcall? dl mem name argVals else none) with
      | some r => simp [hl] at h
      | none =>
        cases hp : evalPureIntrinsicExec? cfg name retTy fmf argVals o with
        | some r => simp [hl, hp] at h
        | none =>
          have hp' := evalPureIntrinsicExec?_none_indep (o' := o') hp
          simp [hp']

/-- Check whether an `llvm.assume` operand bundle tag requires evaluating its operand arguments. -/
def assumeBundleShouldEval (tag : String) : Bool :=
  tag == "nonnull" || tag == "noundef" || tag == "align" ||
  tag == "dereferenceable" || tag == "dereferenceable_or_null" || tag == "range"

/-- Evaluate a single `llvm.assume` operand bundle on already-evaluated operand values. -/
def evalAssumeBundlePure (dl : DataLayout) (mem : MemoryState)
    (tag : String) (vals : List RegisterValue) : Except ExecError Unit :=
  match tag with
  | "nonnull" =>
    match vals with
    | [.ptr _ .poison] => .error (.immediateUB "llvm.assume nonnull violated (poison)")
    | [.ptr as (.value p)] =>
      if p.isNull dl as then .error (.immediateUB "llvm.assume nonnull violated (null)")
      else .ok ()
    | _ => .ok ()
  | "noundef" =>
    match vals with
    | [v] =>
      if v.containsPoison then .error (.immediateUB "llvm.assume noundef violated (poison)")
      else .ok ()
    | _ => .ok ()
  | "dereferenceable" =>
    match vals with
    | [pVal, .bv _ (.value sz)] =>
      match applySingleAttrPure dl mem (.ptr 0) pVal (.dereferenceable sz.toNat) with
      | .ok _ => .ok ()
      | .error e => .error e
    | [_, .bv _ .poison] => .error (.immediateUB "llvm.assume dereferenceable size is poison")
    | _ => .ok ()
  | "dereferenceable_or_null" =>
    match vals with
    | [pVal, .bv _ (.value sz)] =>
      match applySingleAttrPure dl mem (.ptr 0) pVal (.dereferenceableOrNull sz.toNat) with
      | .ok _ => .ok ()
      | .error e => .error e
    | [_, .bv _ .poison] => .error (.immediateUB "llvm.assume dereferenceable_or_null size is poison")
    | _ => .ok ()
  | "align" =>
    match vals with
    | .ptr _ .poison :: _ => .error (.immediateUB "llvm.assume align pointer is poison")
    | .ptr _ (.value p) :: aVal :: rest =>
      if p.addr.toNat == 0 then .ok ()
      else
        match aVal with
        | .bv _ .poison => .error (.immediateUB "llvm.assume align value is poison")
        | .bv _ (.value abv) =>
          let a := abv.toNat
          if a == 0 || (a &&& (a - 1)) != 0 then
            .error (.immediateUB s!"llvm.assume align({a}) is not a power of 2")
          else
            let off? : Except ExecError Nat := match rest with
              | [] => .ok 0
              | .bv _ .poison :: _ => .error (.immediateUB "llvm.assume align offset is poison")
              | .bv _ (.value obv) :: _ => .ok obv.toNat
              | _ => .ok 0
            match off? with
            | .error e => .error e
            | .ok off =>
              if (p.addr.toNat + a - (off % a)) % a != 0 then
                .error (.immediateUB s!"llvm.assume align({a}) violated for pointer")
              else .ok ()
        | _ => .ok ()
    | _ => .ok ()
  | "range" =>
    match vals with
    | [.bv _ .poison, _, _] => .error (.immediateUB "llvm.assume range value is poison")
    | [.bv _ (.value vbv), .bv _ (.value lbv), .bv _ (.value hbv)] =>
      let v := vbv.toNat
      let lo := lbv.toNat
      let hi := hbv.toNat
      let inRange :=
        if lo ≤ hi then lo ≤ v && v < hi
        else v ≥ lo || v < hi
      if inRange then .ok ()
      else .error (.immediateUB "llvm.assume range violated")
    | [_, .bv _ .poison, _] | [_, _, .bv _ .poison] =>
      .error (.immediateUB "llvm.assume range bound is poison")
    | _ => .ok ()
  | _ => .ok ()

end LeanNanoLlvm.Semantics
