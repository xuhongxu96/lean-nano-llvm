import Lean
import LeanNanoLlvm.Refinement.Refinement

/-! # Evaluating `orderValueAttrs` during symbolic execution

`applyValueAttrsPure` applies a value's attributes in phase order (`orderValueAttrs`: poison-
generating attributes, then `noundef`, then `dereferenceable(_or_null)`). Attribute lists come
from parsed IR and are ground, so `reduceOrderValueAttrs` reorders the literal list directly:
each element's phase is read off its head constructor, and the original element expressions
are kept (so `range (-32) (-16)` stays in the form the rest of the simp set expects). Generic
list lemmas (`List.filter_cons`, `List.cons_append`, ...) would do the same but also fire on
every other list in the machine state. -/

namespace LeanNanoLlvm.Refinement

open Lean Meta
open LeanNanoLlvm Semantics

/-- The phase of a `ValueAttr` constructor (mirrors `AST.ValueAttr.phase`). -/
private def phaseOfCtor : Name → Option Nat
  | ``AST.ValueAttr.noundef => some 1
  | ``AST.ValueAttr.dereferenceable => some 2
  | ``AST.ValueAttr.dereferenceableOrNull => some 3
  | ``AST.ValueAttr.nonnull | ``AST.ValueAttr.align | ``AST.ValueAttr.range
  | ``AST.ValueAttr.rangeList | ``AST.ValueAttr.nofpclass | ``AST.ValueAttr.byval
  | ``AST.ValueAttr.sret | ``AST.ValueAttr.noalias | ``AST.ValueAttr.readonly => some 0
  | _ => none

/-- `orderValueAttrs [a₁, …, aₙ]` ↦ the same elements, stably sorted by phase (by `rfl`). -/
dsimproc reduceOrderValueAttrs (orderValueAttrs _) := fun e => do
  unless e.isAppOfArity ``orderValueAttrs 1 do return .continue
  let some (ty, elems) := (e.getArg! 0).listLit? | return .continue
  let mut tagged : Array (Nat × Expr) := #[]
  for a in elems do
    let some c := (← whnfR a).getAppFn.constName? | return .continue
    let some ph := phaseOfCtor c | return .continue
    tagged := tagged.push (ph, a)
  let sorted := (List.range 4).flatMap fun ph => (tagged.filter (·.1 == ph)).toList.map (·.2)
  return .done (← mkListLit ty sorted)


/-! ## Scalar integer attributes

`applyValueAttrsPure` of a single attribute is `applySingleAttrPure`. For the scalar integer
values that symbolic execution binds to parameters and results, these equations give its result
directly: `noundef` passes a value and is immediate UB on poison; `range` keeps a value in range
and makes it poison otherwise (a `PoisonOr` `if`, as for other poison-producing operations). -/

open AST in
theorem applySingleAttrPure_noundef_bv_value (dl : DataLayout) (mem : MemoryState)
    (ty : LlvmType) {w : Nat} (x : BitVec w) :
    applySingleAttrPure dl mem ty (.bv w (.value x)) .noundef = .ok (.bv w (.value x)) := rfl

open AST in
theorem applySingleAttrPure_noundef_bv_poison (dl : DataLayout) (mem : MemoryState)
    (ty : LlvmType) {w : Nat} :
    applySingleAttrPure dl mem ty (.bv w .poison) .noundef =
      .error (.immediateUB s!"The value {(RegisterValue.bv w .poison).llubiString mem dl} violates noundef attribute.") :=
  rfl

open AST in
/-- `range lo hi` on a value: kept in LLVM's half-open, possibly wrapping range `[lo, hi)` of width
`w`, poison outside. The condition is stated over `toNat` (no auxiliary definition), so that
with literal bounds it becomes linear arithmetic for the closers. -/
theorem applySingleAttrPure_range_bv_value (dl : DataLayout) (mem : MemoryState)
    (ty : LlvmType) {w : Nat} (x : BitVec w) (lo hi : Int) :
    applySingleAttrPure dl mem ty (.bv w (.value x)) (.range lo hi) =
      .ok (.bv w (if (if (BitVec.ofInt w lo).toNat ≤ (BitVec.ofInt w hi).toNat
          then (BitVec.ofInt w lo).toNat ≤ x.toNat && x.toNat < (BitVec.ofInt w hi).toNat
          else x.toNat ≥ (BitVec.ofInt w lo).toNat || x.toNat < (BitVec.ofInt w hi).toNat)
        then .value x else .poison)) := by
  simp only [applySingleAttrPure, liftUnaryPure]
  split <;> split <;> simp_all

/-- Binding an `.ok` in `Except` (the attribute sequence of a value). -/
theorem except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    ((Except.ok a : Except ε α) >>= f) = f a := rfl

/-- Binding an `.error` in `Except`: the error. -/
theorem except_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    ((Except.error e : Except ε α) >>= f) = .error e := rfl

open AST in
theorem applySingleAttrPure_range_bv_poison (dl : DataLayout) (mem : MemoryState)
    (ty : LlvmType) {w : Nat} (lo hi : Int) :
    applySingleAttrPure dl mem ty (.bv w .poison) (.range lo hi) = .ok (.bv w .poison) := rfl

end LeanNanoLlvm.Refinement
