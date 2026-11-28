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

end LeanNanoLlvm.Refinement
