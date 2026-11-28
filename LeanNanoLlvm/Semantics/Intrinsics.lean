import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.DataLayout
import LeanNanoLlvm.Semantics.Operations
import LeanNanoLlvm.Semantics.Intrinsics.MemTransfer
import LeanNanoLlvm.Semantics.Intrinsics.Alloc
import LeanNanoLlvm.Semantics.Intrinsics.Pure
import LeanNanoLlvm.Semantics.Intrinsics.Libc
import LeanNanoLlvm.Semantics.Intrinsics.VectorMemory

/-!
# Intrinsic and libcall dispatch

`evalNonAllocIntrinsicExec?` routes a call to a non-allocating intrinsic or libcall to its
family (`Intrinsics/*`); `none` means the callee is not one, so the call enters a function.
`llvm.assume` operand bundles are evaluated here as well.
-/

namespace LeanNanoLlvm.Semantics

open AST
open RegisterValue (poisonOf)

/-- Lifetime intrinsics on an inaccessible object (of a caller suspended in a tail call) are UB. -/
def lifetimeInaccessible (mem : MemoryState) (p : Pointer) : Bool :=
  match mem.resolveObject? p with
  | some mo => mem.isInaccessible mo.allocId
  | none => false

def lifetimeInaccessibleUB (mem : MemoryState) (p : Pointer) : ExecError :=
  .immediateUB s!"Try to access an inaccessible memory object: {mem.ptrString p}."

/-- Non-allocating memory & pure intrinsics/libcalls (shared between `Step` and `Exec`). -/
def evalNonAllocIntrinsicExec? (dl : DataLayout) (cfg : SemanticsConfig) (mem : MemoryState)
    (name : String) (retTy : LlvmRetType) (fmf : FastMathFlags) (argVals : List RegisterValue)
    (o : OracleState) (allowLibcalls : Bool := true) (argAttrs : List (List ValueAttr) := []) :
    Option (Except ExecError (RegisterValue × MemoryState × OracleState)) :=
  if strHasPrefix name "llvm.lifetime.start" then
    some <| match argVals.getLast? with
      | some (.ptr _ (.value p)) =>
        if lifetimeInaccessible mem p then .error (lifetimeInaccessibleUB mem p)
        else .ok (.void, mem.lifetimeStart cfg p, o)
      | _ => .ok (.void, mem, o)
  else if strHasPrefix name "llvm.lifetime.end" then
    some <| match argVals.getLast? with
      | some (.ptr _ (.value p)) =>
        if lifetimeInaccessible mem p then .error (lifetimeInaccessibleUB mem p)
        else .ok (.void, mem.lifetimeEnd p, o)
      | _ => .ok (.void, mem, o)
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
        | some r =>
          -- llubi checks every argument of a library call for poison before running it
          match argVals.findIdx? (fun | .bv _ .poison | .ptr _ .poison | .float _ .poison => true | _ => false) with
          | some i => some (.error (.immediateUB (libcallPoisonArgMsg i)))
          | none => some (r.map fun (v, m') => (v, m', o))
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
    split at h
    · split at h
      · cases h
      · cases h; exact MemoryState.lifetimeStart_preserves_wf hwf cfg _
    · cases h; exact hwf
  · rw [if_neg h1] at h
    by_cases h2 : strHasPrefix name "llvm.lifetime.end" = true
    · rw [if_pos h2] at h
      split at h
      · split at h
        · cases h
        · cases h; exact MemoryState.lifetimeEnd_preserves_wf hwf _
      · cases h; exact hwf
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
                  dsimp only at h
                  split at h
                  · cases h
                  · cases r with
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
      | some r => simp only [hl] at h; split at h <;> cases h
      | none =>
        cases hp : evalPureIntrinsicExec? cfg name retTy fmf argVals o with
        | some r => simp [hl, hp] at h
        | none =>
          have hp' := evalPureIntrinsicExec?_none_indep (o' := o') hp
          simp [hp']

/-- Check whether an `llvm.assume` operand bundle tag requires evaluating its operand arguments. -/
def assumeBundleShouldEval (tag : String) : Bool :=
  tag == "nonnull" || tag == "noundef" || tag == "align" ||
  tag == "dereferenceable" || tag == "dereferenceable_or_null" || tag == "range" ||
  tag == "separate_storage"

/-- Evaluate a single `llvm.assume` operand bundle on already-evaluated operand values. -/
def evalAssumeBundlePure (dl : DataLayout) (mem : MemoryState)
    (tag : String) (vals : List RegisterValue) : Except ExecError Unit :=
  match tag with
  | "nonnull" =>
    match vals with
    | [.ptr _ .poison] => .error (.immediateUB "Assume on poison pointer.")
    | [.ptr as (.value p)] =>
      if p.isNull dl as then .error (.immediateUB s!"The pointer {mem.ptrString p} violates nonnull assumption.")
      else .ok ()
    | _ => .ok ()
  | "noundef" =>
    match vals with
    | [v] =>
      if v.containsPoison then .error (.immediateUB s!"The value {v.llubiString mem dl} violates noundef assumption.")
      else .ok ()
    | _ => .ok ()
  | "dereferenceable" =>
    match vals with
    | [.ptr _ .poison, _] => .error (.immediateUB "Assume on poison pointer.")
    | [pVal, .bv _ (.value sz)] =>
      if sz.toNat == 0 then .ok () else
      match applySingleAttrPure dl mem (.ptr 0) pVal (.dereferenceable sz.toNat) with
      | .ok _ => .ok ()
      | .error _ => .error (.immediateUB s!"The pointer {pVal.llubiString mem dl} violates dereferenceable({sz.toInt}) assumption.")
    | [_, .bv _ .poison] => .error (.immediateUB "llvm.assume dereferenceable size is poison")
    | _ => .ok ()
  | "dereferenceable_or_null" =>
    match vals with
    | [.ptr _ .poison, _] => .error (.immediateUB "Assume on poison pointer.")
    | [pVal, .bv _ (.value sz)] =>
      if sz.toNat == 0 then .ok () else
      match applySingleAttrPure dl mem (.ptr 0) pVal (.dereferenceableOrNull sz.toNat) with
      | .ok _ => .ok ()
      | .error _ => .error (.immediateUB s!"The pointer {pVal.llubiString mem dl} violates dereferenceable_or_null({sz.toInt}) assumption.")
    | [_, .bv _ .poison] => .error (.immediateUB "llvm.assume dereferenceable_or_null size is poison")
    | _ => .ok ()
  | "align" =>
    match vals with
    | .ptr _ .poison :: _ => .error (.immediateUB "Assume on poison pointer.")
    | .ptr _ (.value p) :: aVal :: rest =>
      match aVal with
      | .bv _ .poison => .error (.immediateUB "Unexpected poison integer value.")
      | .bv _ (.value abv) =>
        let a := abv.toNat
        let off? : Except ExecError Int := match rest with
          | [] => .ok 0
          | .bv _ .poison :: _ => .error (.immediateUB "Unexpected poison integer value.")
          | .bv _ (.value obv) :: _ => .ok obv.toInt
          | _ => .ok 0
        match off? with
        | .error e => .error e
        | .ok off =>
          let w := p.addrWidth
          let checked : Nat := (((p.addr.toNat : Int) - off) % (2 ^ w : Int)).toNat
          if a == 0 || (a &&& (a - 1)) != 0 then
            if checked != 0 then
              .error (.immediateUB s!"Assume on pointer {mem.ptrString p} with a nonzero adjusted address and a non-power-of-two alignment {a}.")
            else .ok ()
          else if checked % a != 0 then
            .error (.immediateUB s!"The pointer {mem.ptrString p} violates align({a}) assumption.")
          else .ok ()
      | _ => .ok ()
    | _ => .ok ()
  | "range" =>
    match vals with
    | [.bv _ .poison, .bv _ (.value lbv), .bv _ (.value hbv)] =>
      .error (.immediateUB s!"The value poison violates range({lbv.toInt}, {hbv.toInt}) assumption.")
    | [.bv _ .poison, _, _] => .error (.immediateUB "The value poison violates range assumption.")
    | [.bv _ (.value vbv), .bv _ (.value lbv), .bv _ (.value hbv)] =>
      let v := vbv.toNat
      let lo := lbv.toNat
      let hi := hbv.toNat
      let inRange :=
        if lo ≤ hi then lo ≤ v && v < hi
        else v ≥ lo || v < hi
      if inRange then .ok ()
      else .error (.immediateUB s!"The value {(RegisterValue.bv _ (.value vbv)).llubiString mem dl} violates range({lbv.toInt}, {hbv.toInt}) assumption.")
    | [_, .bv _ .poison, _] | [_, _, .bv _ .poison] =>
      .error (.immediateUB "llvm.assume range bound is poison")
    | _ => .ok ()
  -- other bundles on pointers (`separate_storage`, ...): llubi only rejects a poison pointer
  | _ =>
    match vals with
    | .ptr _ .poison :: _ => .error (.immediateUB "Assume on poison pointer.")
    | _ => .ok ()

end LeanNanoLlvm.Semantics
