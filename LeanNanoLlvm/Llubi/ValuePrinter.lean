import LeanNanoLlvm.Semantics.Value

/-!
# `llubi` value printer

Renders runtime `RegisterValue`s exactly like `llvm::ubi::AnyValue::print` (`llubi`'s
`--verbose` output): `i32 -1`, `T`/`F` for `i1`, `float 1.500000e+00`, `ptr 0x8 [alloc + 4]`,
`b16 0x!! !!!!0101`, and `{ ... }` for every aggregate/vector.  The renderer itself lives in the
semantics layer (`RegisterValue.llubiString`, `MemoryState.ptrString`) because the semantics also
uses it to phrase Immediate-UB diagnostics exactly as `llubi` does.
-/

namespace LeanNanoLlvm.Llubi

open LeanNanoLlvm.AST
open LeanNanoLlvm.Semantics

/-- `Pointer::print`. -/
def printPointer (mem : MemoryState) (p : Pointer) : String := mem.ptrString p

/-- `AnyValue::print`. -/
def printValue (mem : MemoryState) (dl : DataLayout) (v : RegisterValue) : String :=
  v.llubiString mem dl

end LeanNanoLlvm.Llubi
