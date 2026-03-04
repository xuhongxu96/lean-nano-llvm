import LeanNanoLlvm.AST
import LeanNanoLlvm.Tactic
import LeanNanoLlvm.Semantics

open LeanNanoLlvm

open AST.Syntax
open Semantics

section

open scoped LeanNanoLlvm.AST.Syntax

def runCodeToMsg {φ : Nat} (c : @LeanNanoLlvm.AST.Code φ) (resKey : AST.Identifier) : String :=
  match (denoteNanoLlvmCode c).run default with
  | .ok (_, st) => s!"ok: {st.registers.get? resKey}"
  | .error e => s!"error: {e}"

#eval runCodeToMsg [llvm-code|
  %1 = add i8 1, 2
  %2 = mul i8 %1, 8
] [llvm-identifier| %2]

theorem add_two_i32 : forall (a b : ℤ),
  (do
    let (_, st) ← (denoteNanoLlvmCode (
      [llvm-code| %1 = add i32 <a:int>, <b:int>]
    )).run default

    pure (match st.registers.get? [llvm-identifier| %1] with
      | some (.bv 32 v) => some v
      | _ => none)
  ) = .ok (some (.value ((a : BitVec 32) + (b : BitVec 32)))) := by
  intros
  simp [simp_llvm]
  rfl

theorem add_two_i32_then_trunc_to_i8 : forall (a b : ℤ),
  (do
    let (_, st) ← (denoteNanoLlvmCode (
      [llvm-code|
        %1 = add i32 <a:int>, <b:int>
        %2 = trunc i32 %1 to i8
      ]
    )).run default

    pure (match st.registers.get? [llvm-identifier| %2] with
      | some (.bv 8 v) => some v
      | _ => none)
  ) = .ok (some (.value (((a : BitVec 32) + (b : BitVec 32)).setWidth 8))) := by
  intros
  simp [simp_llvm, simp_llvm_option]
  rfl

end
