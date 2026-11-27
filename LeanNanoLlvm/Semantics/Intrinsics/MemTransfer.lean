import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.DataLayout
import LeanNanoLlvm.Semantics.Operations
import LeanNanoLlvm.Util.Text

/-!
# `memcpy`, `memmove` and `memset`

The memory-transfer intrinsics and libcalls, with `llubi`'s length, overlap and access checks.
-/

namespace LeanNanoLlvm.Semantics

open AST
open RegisterValue (poisonOf)

/-- Verified memory transfer (`memcpy` / `memmove`). -/
def execMemTransferPure (mem : MemoryState) (destVal srcVal lenVal : RegisterValue)
    (isMemMove isLibCall : Bool) : Except ExecError MemoryState :=
  match lenVal with
  | .bv _ .poison => .error (.immediateUB s!"{if isMemMove then "memmove" else "memcpy"} called with poison length.")
  | .bv _ (.value bv) =>
    let len := bv.toNat
    if len ≥ 2 ^ 64 then
      .error (.immediateUB s!"{if isMemMove then "memmove" else "memcpy"} called with length overflows uint64_t.")
    else if len == 0 then .ok mem
    else match destVal with
      | .ptr _ .poison => .error (.immediateUB s!"{if isMemMove then "memmove" else "memcpy"} called with poison destination pointer.")
      | .ptr _ (.value dstPtr) =>
        match srcVal with
        | .ptr _ .poison => .error (.immediateUB s!"{if isMemMove then "memmove" else "memcpy"} called with poison source pointer.")
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
                .error (.immediateUB "memcpy with overlapping source and destination.")
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
      by_cases hbig : 2 ^ 64 ≤ lbv.toNat
      · rw [if_pos hbig] at h; cases h
      rw [if_neg hbig] at h
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
  | .bv _ .poison => .error (.immediateUB "memset called with poison length.")
  | .bv _ (.value bv) =>
    let len := bv.toNat
    if len ≥ 2 ^ 64 then .error (.immediateUB "memset called with length overflows uint64_t.")
    else if len == 0 then .ok mem
    else match destVal with
      | .ptr _ .poison => .error (.immediateUB "memset called with poison destination pointer.")
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
      by_cases hbig : 2 ^ 64 ≤ lbv.toNat
      · rw [if_pos hbig] at h; cases h
      rw [if_neg hbig] at h
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

end LeanNanoLlvm.Semantics
