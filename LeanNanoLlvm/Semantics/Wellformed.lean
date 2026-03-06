import LeanNanoLlvm.Semantics.Denote

namespace LeanNanoLlvm
namespace AST

variable {φ : Nat}

inductive Declaration.WellFormed (decl : @Declaration φ) : Prop where
  | mk :
    decl.type.asFunction? = some ⟨retTy, argTys⟩ →
    retTy.isVoid? ∨ (retTy.asRet? = some retRetTy ∧ retRetTy.asInt?.isSome) →
    (∀ argTy ∈ argTys, argTy.asFunction?.isNone) →
    WellFormed decl

inductive Definition.WellFormed (defn : @Definition φ) : Prop where
  | mk : defn.prototype.WellFormed → WellFormed defn

theorem declaration_wellFormed_iff (decl : @Declaration φ) :
    decl.WellFormed ↔
      ∃ retTy argTys, decl.type = LlvmType.function retTy argTys
      ∧ (retTy.isVoid? = true ∨ (∃ retRetTy, retTy.asRet? = some retRetTy ∧ retRetTy.asInt?.isSome))
      ∧ (∀ argTy ∈ argTys, argTy.asFunction?.isNone)
  := by
  constructor
  . intro h
    cases h with
    | mk h =>
      aesop
  . simp
    rintro retTy argTys htype (hret1|(⟨retRetTy, ⟨hret2, hret3⟩⟩)) hargs
    constructor
    . simp_all
      constructor
      . cases retTy
        . rfl
        . contradiction
      . rfl
    . left
      simp
    . simp_all
    . exact (LlvmType.i1)
    . constructor
      . simp_all
        constructor
        . rfl
        . rfl
      . right
        simp_all
        constructor
        . rfl
        . simp_all
      . simp_all


theorem definition_wellFormed_iff (defn : @Definition φ) :
    defn.WellFormed ↔ defn.prototype.WellFormed := by
  constructor
  . intro h
    cases h with
    | mk hproto =>
      exact hproto
  . intro hproto
    constructor
    . exact hproto

end AST

end LeanNanoLlvm
