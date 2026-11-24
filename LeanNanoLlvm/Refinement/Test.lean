import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax
import LeanNanoLlvm.AST.Unexpander

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

/-! ### 1. Basic Arithmetic & Reflexivity Refinement (Modern Mode: `undef` disabled) -/

open scoped LeanNanoLlvm.AST.Syntax in
def addDef : @AST.Definition 0 := [llvm-definition|
  define i8 @f(i8 %a, i8 %b) {
  entry:
    %x = add i8 %a, %b
    ret i8 %x
  }
]

theorem addDef_is_refined_by_itself : addDef ⊑ addDef :=
  Definition.Refines.refl addDef

theorem ret_add_x_0_is_refined_by_ret_x :
  open scoped LeanNanoLlvm.AST.Syntax in
  [llvm-definition|
    define i8 @f(i8 %x) {
    entry:
      ret i8 %x
    }
  ]
  ⊑
  [llvm-definition|
    define i8 @f(i8 %x) {
    entry:
      %x = add i8 %x, 0
      ret i8 %x
    }
  ]
  := by
  intro args _ _ _ hargs
  right
  cases args with
  | nil => simp [Definition.ArgValuesWellFormed] at hargs
  | cons arg rest =>
    cases rest with
    | cons _ _ => simp [Definition.ArgValuesWellFormed] at hargs
    | nil =>
      cases arg <;> simp [Definition.ArgValuesWellFormed, RegisterValue.WellFormedFor] at hargs
      subst hargs
      rename_i v
      constructor
      · intro _ o'
        exact ⟨.bv 8 v, by simp [simp_llvm]⟩
      · intro o ret h
        have hret : ret = .bv 8 v := by
          simp [simp_llvm] at h
          exact h.symm
        subst hret
        refine ⟨o, .bv 8 v, ?_, RegisterValue.Refines.refl _⟩
        rcases v with ⟨none | b⟩ <;> simp [simp_llvm, simp_llvm_option]

abbrev singletonWidths (w : Nat) : List.Vector Nat 1 := ⟨[w], by simp⟩

theorem ret_add_x_0_is_refined_by_ret_x_generic (w : Nat) :
  open scoped LeanNanoLlvm.AST.Syntax in
  [llvm-1-definition|
    define i$0 @f(i$0 %x) {
    entry:
      ret i$0 %x
    }
  ].instantiateWidths (singletonWidths w)
  ⊑
  [llvm-1-definition|
    define i$0 @f(i$0 %x) {
    entry:
      %x = add i$0 %x, 0
      ret i$0 %x
    }
  ].instantiateWidths (singletonWidths w)
  := by
  intro args _ _ _ hargs
  right
  cases args with
  | nil => simp [Definition.ArgValuesWellFormed, singletonWidths] at hargs
  | cons arg rest =>
    cases rest with
    | cons _ _ => simp [Definition.ArgValuesWellFormed, singletonWidths] at hargs
    | nil =>
      cases arg <;> simp [Definition.ArgValuesWellFormed, RegisterValue.WellFormedFor, singletonWidths] at hargs
      subst hargs
      rename_i v
      constructor
      · intro _ o'
        exact ⟨.bv w v, by simp [singletonWidths, simp_llvm]⟩
      · intro o ret h
        have hret : ret = .bv w v := by
          simp [singletonWidths, simp_llvm] at h
          exact h.symm
        subst hret
        refine ⟨o, .bv w v, ?_, RegisterValue.Refines.refl _⟩
        rcases v with ⟨none | b⟩ <;> simp [singletonWidths, simp_llvm, simp_llvm_option]

/-! ### 2. Optional `undef` Refinement (Explicitly Enabled via `SemanticsConfig.withUndef`) -/

private theorem bitvec_double_eq_mul_two_generic {w : Nat} (b : BitVec w) :
    b + b = b * (2 : BitVec w) := by
  apply BitVec.eq_of_toFin_eq
  apply Fin.ext
  simp [Fin.val_add, Fin.val_mul, BitVec.toFin_ofNat]
  rw [← Nat.two_mul b.toNat, Nat.mul_comm]

private theorem bitvec_mul_two_ne_one_generic {w : Nat} (hpos : 0 < w) (b : BitVec w) :
    b * (2#w) ≠ 1#w := by
  intro h
  have hval :
      (((b * (2#w)).toFin : Fin (2 ^ w)) : Nat) =
        (((1#w).toFin : Fin (2 ^ w)) : Nat) := by
    simp_all
  simp [Fin.val_mul, BitVec.toFin_ofNat] at hval
  have hmod := congrArg (fun n => n % 2) hval
  have hright : (1 % 2 ^ w) % 2 = 1 := by
    cases w with
    | zero => cases Nat.not_lt_zero _ hpos
    | succ n => simp
  simp [hright] at hmod

open scoped LeanNanoLlvm.AST.Syntax in
@[simp]
def undefAddDef : @AST.Definition 0 := [llvm-definition|
  define i1 @f() {
    entry:
      %x = add i1 undef, undef
      ret i1 %x
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
@[simp]
def undefMul2Def : @AST.Definition 0 := [llvm-definition|
  define i1 @f() {
    entry:
      %x = mul i1 undef, 2
      ret i1 %x
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
@[simp]
def undefAddDef8 : @AST.Definition 0 := [llvm-definition|
  define i8 @f() {
    entry:
      %x = add i8 undef, undef
      ret i8 %x
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
@[simp]
def undefMul2Def8 : @AST.Definition 0 := [llvm-definition|
  define i8 @f() {
    entry:
      %x = mul i8 undef, 2
      ret i8 %x
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
theorem undef_add_is_refined_by_undef_mul2_generic (w : Nat) :
  [llvm-1-definition|
    define i$0 @f() {
      entry:
        %x = mul i$0 undef, 2
        ret i$0 %x
    }
  ].instantiateWidths (singletonWidths w)
  ⊑[SemanticsConfig.withUndef]
  [llvm-1-definition|
    define i$0 @f() {
      entry:
        %x = add i$0 undef, undef
        ret i$0 %x
    }
  ].instantiateWidths (singletonWidths w)
  := by
  intro args _ _ _ hargs
  right
  cases args with
  | cons _ _ => simp [Definition.ArgValuesWellFormed, singletonWidths] at hargs
  | nil =>
    constructor
    · intro _ o'
      exact ⟨.bv w (.value ((BitVec.ofNat w (o' 0)) * (2#w))),
        by simp [singletonWidths, simp_llvm, simp_llvm_option, SemanticsConfig.withUndef]⟩
    · intro o retVal h
      have hret : retVal = .bv w (.value ((BitVec.ofNat w (o 0)) * (2#w))) := by
        simp [singletonWidths, simp_llvm, simp_llvm_option, SemanticsConfig.withUndef] at h
        exact h.symm
      subst hret
      refine ⟨NondetOracle.const (o 0), .bv w (.value ((BitVec.ofNat w (o 0)) * (2#w))),
        ?_, RegisterValue.Refines.refl _⟩
      simp [singletonWidths, simp_llvm, simp_llvm_option, SemanticsConfig.withUndef, bitvec_double_eq_mul_two_generic]

open scoped LeanNanoLlvm.AST.Syntax in
theorem undef_mul2_is_not_refined_by_undef_add_generic (w : Nat) (hpos : 0 < w) :
  ¬ (([llvm-1-definition|
    define i$0 @f() {
      entry:
        %x = add i$0 undef, undef
        ret i$0 %x
    }
  ].instantiateWidths (singletonWidths w))
  ⊑[SemanticsConfig.withUndef]
  ([llvm-1-definition|
    define i$0 @f() {
      entry:
        %x = mul i$0 undef, 2
        ret i$0 %x
    }
  ].instantiateWidths (singletonWidths w)))
  := by
  intro h
  have hwfMul : AST.Definition.WellFormedWith .withUndef
      ([llvm-1-definition|
        define i$0 @f() {
          entry:
            %x = mul i$0 undef, 2
            ret i$0 %x
        }
      ].instantiateWidths (singletonWidths w)) := by
    simp [simp_wellform, singletonWidths, SemanticsConfig.withUndef]
  have hwfAdd : AST.Definition.WellFormedWith .withUndef
      ([llvm-1-definition|
        define i$0 @f() {
          entry:
            %x = add i$0 undef, undef
            ret i$0 %x
        }
      ].instantiateWidths (singletonWidths w)) := by
    simp [simp_wellform, singletonWidths, SemanticsConfig.withUndef]
  have hinst := h [] hwfMul hwfAdd rfl (by simp [Definition.ArgValuesWellFormed, singletonWidths])
  rcases hinst with ⟨oUB, msg, hUB⟩ | ⟨_, href⟩
  · simp [singletonWidths, simp_llvm, simp_llvm_option, SemanticsConfig.withUndef] at hUB
  · have haddRun :
        runNanoLlvmM (evalNanoLlvmDefinition ([llvm-1-definition|
          define i$0 @f() {
            entry:
              %x = add i$0 undef, undef
              ret i$0 %x
          }
        ].instantiateWidths (singletonWidths w)) [])
          (initStateFor .withUndef) ⟨NondetOracle.ofList [1, 0], 0⟩ =
        .ok (.bv w (.value (1#w))) := by
      simp [singletonWidths, simp_llvm, simp_llvm_option, SemanticsConfig.withUndef]
    obtain ⟨o', ret_x, hmulRun, hvalRef⟩ := href (NondetOracle.ofList [1, 0]) (.bv w (.value (1#w))) haddRun
    simp [singletonWidths, simp_llvm, simp_llvm_option, SemanticsConfig.withUndef] at hmulRun
    subst hmulRun
    simp [RegisterValue.Refines] at hvalRef
    exact bitvec_mul_two_ne_one_generic hpos (BitVec.ofNat w (o' 0)) hvalRef

theorem undef_add_is_refined_by_undef_mul2 :
    undefMul2Def ⊑[SemanticsConfig.withUndef] undefAddDef :=
  undef_add_is_refined_by_undef_mul2_generic 1

theorem undef_mul2_is_not_refined_by_undef_add :
    ¬ (undefAddDef ⊑[SemanticsConfig.withUndef] undefMul2Def) :=
  undef_mul2_is_not_refined_by_undef_add_generic 1 (by omega)

theorem undef_add_is_refined_by_undef_mul2_i8 :
    undefMul2Def8 ⊑[SemanticsConfig.withUndef] undefAddDef8 :=
  undef_add_is_refined_by_undef_mul2_generic 8

theorem undef_mul2_is_not_refined_by_undef_add_i8 :
    ¬ (undefAddDef8 ⊑[SemanticsConfig.withUndef] undefMul2Def8) :=
  undef_mul2_is_not_refined_by_undef_add_generic 8 (by omega)

/-! ### 3. Poison Refinement -/

open scoped LeanNanoLlvm.AST.Syntax in
def poisonDef : @AST.Definition 0 := [llvm-definition|
  define i8 @f() {
  entry:
    ret i8 poison
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
def zeroDef : @AST.Definition 0 := [llvm-definition|
  define i8 @f() {
  entry:
    ret i8 0
  }
]

theorem poison_is_refined_by_zero : zeroDef ⊑ poisonDef := by
  intro args _ _ _ hargs
  right
  cases args with
  | cons _ _ => simp [Definition.ArgValuesWellFormed, poisonDef] at hargs
  | nil =>
    constructor
    · intro _ o'
      exact ⟨.bv 8 (.value (0 : BitVec 8)), by simp [zeroDef, simp_llvm]⟩
    · intro o ret h
      have hret : ret = .bv 8 (.value (0 : BitVec 8)) := by
        simp [zeroDef, simp_llvm] at h
        exact h.symm
      subst hret
      exact ⟨o, .bv 8 .poison, by simp [poisonDef, simp_llvm], rfl⟩

theorem zero_is_not_refined_by_poison : ¬ (poisonDef ⊑ zeroDef) := by
  intro h
  have hwfZero : zeroDef.WellFormedWith .modern := by
    simp [zeroDef, simp_wellform]
  have hwfPoison : poisonDef.WellFormedWith .modern := by
    simp [poisonDef, simp_wellform]
  have hinst := h [] hwfZero hwfPoison rfl (by simp [Definition.ArgValuesWellFormed, zeroDef])
  rcases hinst with ⟨oUB, msg, hUB⟩ | ⟨_, href⟩
  · simp [zeroDef, simp_llvm] at hUB
  · obtain ⟨o', ret_x, hzero, hvalRef⟩ :=
      href NondetOracle.zero (.bv 8 .poison) (by simp [poisonDef, simp_llvm])
    simp [zeroDef, simp_llvm] at hzero
    subst hzero
    simp [RegisterValue.Refines] at hvalRef

/-! ### 4. Immediate UB Refinement (UB Refines to Any Behavior) -/

open scoped LeanNanoLlvm.AST.Syntax in
theorem ret_42_refines_udiv_by_zero :
  [llvm-definition|
    define i8 @f(i8 %x) {
    entry:
      ret i8 42
    }
  ]
  ⊑
  [llvm-definition|
    define i8 @f(i8 %x) {
    entry:
      %r = udiv i8 %x, 0
      ret i8 %r
    }
  ]
  := by
  intro args _ _ _ hargs
  cases args with
  | nil => simp [Definition.ArgValuesWellFormed] at hargs
  | cons arg rest =>
    cases rest with
    | cons _ _ => simp [Definition.ArgValuesWellFormed] at hargs
    | nil =>
      cases arg <;> simp [Definition.ArgValuesWellFormed, RegisterValue.WellFormedFor] at hargs
      subst hargs
      rename_i v
      left
      refine ⟨NondetOracle.zero, "Division by zero", ?_⟩
      rcases v with ⟨none | b⟩ <;> simp [simp_llvm, evalIntBinaryOpM, evalDivRemUB]

/-! ### 5. True Nondeterministic `freeze` Refinement -/

open scoped LeanNanoLlvm.AST.Syntax in
def freezePoisonDef : @AST.Definition 0 := [llvm-definition|
  define i8 @f() {
  entry:
    %r = freeze i8 poison
    ret i8 %r
  }
]

theorem zero_refines_freeze_poison : zeroDef ⊑ freezePoisonDef := by
  intro args _ _ _ hargs
  right
  cases args with
  | cons _ _ => simp [Definition.ArgValuesWellFormed, freezePoisonDef] at hargs
  | nil =>
    constructor
    · intro _ o'
      exact ⟨.bv 8 (.value (0 : BitVec 8)), by simp [zeroDef, simp_llvm]⟩
    · intro o ret h
      have hret : ret = .bv 8 (.value (0 : BitVec 8)) := by
        simp [zeroDef, simp_llvm] at h
        exact h.symm
      subst hret
      refine ⟨NondetOracle.zero, .bv 8 (.value (0 : BitVec 8)), ?_, RegisterValue.Refines.refl _⟩
      simp [freezePoisonDef, simp_llvm, SemanticsConfig.modern, drawBitVec]

theorem freeze_poison_not_refines_zero : ¬ (freezePoisonDef ⊑ zeroDef) := by
  intro h
  have hwfZero : zeroDef.WellFormedWith .modern := by
    simp [zeroDef, simp_wellform]
  have hwfFreeze : freezePoisonDef.WellFormedWith .modern := by
    simp [freezePoisonDef, simp_wellform]
  have hinst := h [] hwfZero hwfFreeze rfl (by simp [Definition.ArgValuesWellFormed, zeroDef])
  rcases hinst with ⟨oUB, msg, hUB⟩ | ⟨_, href⟩
  · simp [zeroDef, simp_llvm] at hUB
  · have hfr :
        runNanoLlvmM (evalNanoLlvmDefinition freezePoisonDef [])
          (initStateFor .modern) ⟨NondetOracle.const 1, 0⟩ =
        .ok (.bv 8 (.value (1 : BitVec 8))) := by
      simp [freezePoisonDef, simp_llvm, SemanticsConfig.modern, drawBitVec]
    obtain ⟨o', ret_x, hzero, hvalRef⟩ := href (NondetOracle.const 1) (.bv 8 (.value (1 : BitVec 8))) hfr
    simp [zeroDef, simp_llvm] at hzero
    subst hzero
    simp [RegisterValue.Refines] at hvalRef

/-! ### 6. IEEE-754 Floating-Point Refinement (`fneg (fneg %x)` & Fast-Math Flags) -/

open scoped LeanNanoLlvm.AST.Syntax in
theorem fneg_fneg_is_refined_by_id :
  [llvm-definition|
    define float @f(float %x) {
    entry:
      ret float %x
    }
  ]
  ⊑
  [llvm-definition|
    define float @f(float %x) {
    entry:
      %y = fneg float %x
      %z = fneg float %y
      ret float %z
    }
  ]
  := by
  intro args _ _ _ hargs
  right
  cases args with
  | nil => simp [Definition.ArgValuesWellFormed] at hargs
  | cons arg rest =>
    cases rest with
    | cons _ _ => simp [Definition.ArgValuesWellFormed] at hargs
    | nil =>
      cases arg <;> simp [Definition.ArgValuesWellFormed, RegisterValue.WellFormedFor] at hargs
      subst hargs
      rename_i v
      constructor
      · intro _ o'
        exact ⟨.float .float v, by simp [simp_llvm, evalTypedExp, concretizeType, concretizeRetType]⟩
      · intro o retVal h
        have hret : retVal = .float .float v := by
          simp [simp_llvm, evalTypedExp, concretizeType, concretizeRetType] at h
          exact h.symm
        subst hret
        refine ⟨o, .float .float v, ?_, RegisterValue.Refines.refl _⟩
        rcases v with ⟨none | flt⟩
        · simp [simp_llvm, evalTypedExp, concretizeType, concretizeRetType, liftUnary,
                evalFloatUnaryScalar, evalFloatUnaryOp, drawBool, writeRegister]
        · simp [simp_llvm, evalTypedExp, concretizeType, concretizeRetType, liftUnary,
                evalFloatUnaryScalar, evalFloatUnaryOp, handleFMF, drawBool, writeRegister]

open scoped LeanNanoLlvm.AST.Syntax in
theorem fadd_refines_fadd_nnan :
  [llvm-definition|
    define float @f(float %a, float %b) {
    entry:
      %r = fadd float %a, %b
      ret float %r
    }
  ]
  ⊑
  [llvm-definition|
    define float @f(float %a, float %b) {
    entry:
      %r = fadd nnan float %a, %b
      ret float %r
    }
  ]
  := by
  intro args _ _ _ hargs
  right
  rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · simp [Definition.ArgValuesWellFormed] at hargs
  · simp [Definition.ArgValuesWellFormed] at hargs
  · cases a <;> cases b <;>
      simp [Definition.ArgValuesWellFormed, RegisterValue.WellFormedFor] at hargs
    rcases hargs with ⟨rfl, rfl⟩
    rename_i va vb
    have hba : (AST.Identifier.local_id (.name "b") == AST.Identifier.local_id (.name "a")) = false := rfl
    have hden : ∀ (x : IEEEFloat FloatFormat.single) (b1 b2 : Bool),
        handleDenormal .ieee b1 b2 x = x := by
      intro x b1 b2
      unfold handleDenormal
      split_ifs <;> rfl
    have hstep : ∀ (o : NondetOracle),
        ∃ (rt rs : FloatW .float),
          runNanoLlvmM (evalNanoLlvmDefinition ([llvm-definition|
            define float @f(float %a, float %b) {
            entry:
              %r = fadd float %a, %b
              ret float %r
            }
          ]) [.float .float va, .float .float vb]) (initStateFor .modern) ⟨o, 0⟩ = .ok (.float .float rt) ∧
          runNanoLlvmM (evalNanoLlvmDefinition ([llvm-definition|
            define float @f(float %a, float %b) {
            entry:
              %r = fadd nnan float %a, %b
              ret float %r
            }
          ]) [.float .float va, .float .float vb]) (initStateFor .modern) ⟨o, 0⟩ = .ok (.float .float rs) ∧
          RegisterValue.Refines (.float .float rt) (.float .float rs) := by
      intro o
      rcases va with ⟨none | fa⟩
      · refine ⟨.poison, .poison, ?_, ?_, rfl⟩
        · simp [simp_llvm, evalTypedExp, concretizeType, concretizeRetType, liftBinary,
                evalFloatBinaryScalar, evalFloatBinaryOp, drawBool, drawNat, writeRegister,
                Std.ExtHashMap.getElem_insert, hba]
        · simp [simp_llvm, evalTypedExp, concretizeType, concretizeRetType, liftBinary,
                evalFloatBinaryScalar, evalFloatBinaryOp, drawBool, drawNat, writeRegister,
                Std.ExtHashMap.getElem_insert, hba]
      · rcases vb with ⟨none | fb⟩
        · refine ⟨.poison, .poison, ?_, ?_, rfl⟩
          · simp [simp_llvm, evalTypedExp, concretizeType, concretizeRetType, liftBinary,
                  evalFloatBinaryScalar, evalFloatBinaryOp, drawBool, drawNat, writeRegister,
                  Std.ExtHashMap.getElem_insert, hba]
          · simp [simp_llvm, evalTypedExp, concretizeType, concretizeRetType, liftBinary,
                  evalFloatBinaryScalar, evalFloatBinaryOp, drawBool, drawNat, writeRegister,
                  Std.ExtHashMap.getElem_insert, hba]
        · let flipL := (o 0) % 2 == 1
          let flipR := (o 1) % 2 == 1
          let denormL := (o 2) % 2 == 1
          let denormR := (o 3) % 2 == 1
          let nanSign := (o 4) % 2 == 1
          let nanPick := o 5
          let rt := evalFloatBinaryOp .modern (.fadd {}) flipL flipR denormL denormR nanSign nanPick (.value fa) (.value fb)
          let rs := evalFloatBinaryOp .modern (.fadd { «nnan» := true }) flipL flipR denormL denormR nanSign nanPick (.value fa) (.value fb)
          refine ⟨rt, rs, ?_, ?_, ?_⟩
          · simp [rt, flipL, flipR, denormL, denormR, nanSign, nanPick,
                  simp_llvm, evalTypedExp, concretizeType, concretizeRetType, liftBinary,
                  evalFloatBinaryScalar, drawBool, drawNat, writeRegister,
                  Std.ExtHashMap.getElem_insert, hba]
          · simp [rs, flipL, flipR, denormL, denormR, nanSign, nanPick,
                  simp_llvm, evalTypedExp, concretizeType, concretizeRetType, liftBinary,
                  evalFloatBinaryScalar, drawBool, drawNat, writeRegister,
                  Std.ExtHashMap.getElem_insert, hba]
          · simp only [rt, rs, evalFloatBinaryOp, handleFMF, hden, SemanticsConfig.modern,
                       PoisonOr.value_bind, Bool.true_and, Bool.false_and,
                       ite_false, Bool.false_eq_true]
            by_cases ha : fa.isNaN = true
            · rw [ha]; simp
            · rw [Bool.eq_false_iff.mpr ha]
              by_cases hb : fb.isNaN = true
              · rw [hb]; simp
              · rw [Bool.eq_false_iff.mpr hb]
                simp only [Bool.false_eq_true, ite_false, PoisonOr.value_bind]
                by_cases hr : (IEEEFloat.add RoundingMode.RNE fa fb).isNaN = true
                · rw [hr]; simp
                · rw [Bool.eq_false_iff.mpr hr]; simp
    constructor
    · intro _ o'
      obtain ⟨rt, _, hrun, _, _⟩ := hstep o'
      exact ⟨.float .float rt, hrun⟩
    · intro o retVal h
      obtain ⟨rt, rs, hrunT, hrunS, href⟩ := hstep o
      rw [hrunT] at h
      injection h with hret
      subst hret
      exact ⟨o, .float .float rs, hrunS, href⟩
  · simp [Definition.ArgValuesWellFormed] at hargs

/-! ### 7. Select Non-Poison-Propagation Refinement -/

open scoped LeanNanoLlvm.AST.Syntax in
theorem ret_a_refines_select_true :
  [llvm-definition|
    define i32 @f(i32 %a, i32 %b) {
    entry:
      ret i32 %a
    }
  ]
  ⊑
  [llvm-definition|
    define i32 @f(i32 %a, i32 %b) {
    entry:
      %r = select i1 true, i32 %a, i32 %b
      ret i32 %r
    }
  ]
  := by
  intro args _ _ _ hargs
  right
  rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · simp [Definition.ArgValuesWellFormed] at hargs
  · simp [Definition.ArgValuesWellFormed] at hargs
  · cases a <;> cases b <;>
      simp [Definition.ArgValuesWellFormed, RegisterValue.WellFormedFor] at hargs
    rcases hargs with ⟨rfl, rfl⟩
    rename_i va vb
    have hba : (AST.Identifier.local_id (.name "b") == AST.Identifier.local_id (.name "a")) = false := rfl
    constructor
    · intro _ o'
      exact ⟨.bv 32 va, by simp [simp_llvm, Std.ExtHashMap.getElem_insert, hba]⟩
    · intro o retVal h
      have hret : retVal = .bv 32 va := by
        simp [simp_llvm, Std.ExtHashMap.getElem_insert, hba] at h
        exact h.symm
      subst hret
      refine ⟨o, .bv 32 va, ?_, RegisterValue.Refines.refl _⟩
      simp [simp_llvm, evalTypedExp, concretizeType, writeRegister,
            Std.ExtHashMap.getElem_insert, hba]
  · simp [Definition.ArgValuesWellFormed] at hargs

/-! ### 8. Stack Memory Store-to-Load Forwarding Refinement -/

private theorem readScalarBits_loop_modern_eq
    (dl : AST.DataLayout) (bytes : Array MemByte) (offsetInBits numBits : Nat)
    (i rem valBits : Nat) (hasUndef isPoison provOk : Bool)
    (provAcc : Option Provenance) (padNonZero : Bool) (o o0 : OracleState) :
    readScalarBits.loop dl .modern bytes offsetInBits numBits i rem valBits
      hasUndef isPoison provOk provAcc padNonZero o =
    let r := readScalarBits.loop dl .modern bytes offsetInBits numBits i rem valBits
      hasUndef isPoison provOk provAcc padNonZero o0
    (r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2.1, o) := by
  induction rem generalizing i valBits hasUndef isPoison provOk provAcc padNonZero with
  | zero => rfl
  | succ r ih =>
    simp only [readScalarBits.loop, SemanticsConfig.modern]
    cases getLogicalBit dl bytes (offsetInBits + i) with
    | poison => exact ih ..
    | undef => exact ih ..
    | concrete b provBit => exact ih ..

private theorem byte_roundtrip_i8 (v : IntW 8) (o : OracleState) :
    bytesToValue .default64LE .modern
      (valueToBytes .default64LE .modern (.bv 8 v) (.int (.concrete 8)))
      (.int (.concrete 8)) o = (.bv 8 v, v == .poison, o) := by
  simp only [valueToBytes, bytesToValue, writeScalarBits, readScalarBits,
             AST.DataLayout.typeStoreSize, AST.DataLayout.typeSizeInBits,
             AST.DataLayout.alignTo]
  rcases v with ⟨none | bv⟩
  · rfl
  · rw [readScalarBits_loop_modern_eq (o0 := ⟨fun _ => 0, 0⟩)]
    have hcheck : ∀ hi lo : Fin 16,
        let n := hi.val * 16 + lo.val
        let bs := writeBitLoop AST.DataLayout.default64LE 0
          (fun i => if i < 8 then MemBit.concrete ((BitVec.ofNat 8 n).getLsbD i) none else MemBit.concrete false none)
          0 8 (Array.replicate 1 MemByte.zero)
        let r := readScalarBits.loop AST.DataLayout.default64LE .modern bs 0 8 0 8 0 false false true none false ⟨fun _ => 0, 0⟩
        r.1 = n ∧ r.2.1 = false ∧ r.2.2.1 = false ∧ r.2.2.2.2.2.1 = false := by
      decide
    have hhi : bv.toNat / 16 < 16 := by have := bv.isLt; omega
    have hlo : bv.toNat % 16 < 16 := by omega
    have hk := hcheck ⟨bv.toNat / 16, hhi⟩ ⟨bv.toNat % 16, hlo⟩
    have hn : bv.toNat / 16 * 16 + bv.toNat % 16 = bv.toNat := by omega
    have hbv : BitVec.ofNat 8 (bv.toNat / 16 * 16 + bv.toNat % 16) = bv := by
      rw [hn]; simp
    dsimp only at hk
    rw [hbv, hn] at hk
    rcases hk with ⟨h1, h2, h3, h4⟩
    have hstep2 : (8 + 7) / 8 = 1 := rfl
    have hstep1 : ((if True then if 8 ≤ 1 then 0 + 8 else 1 * 8 else 0 + 8) - 0) = 8 := rfl
    change (if _ then _ else _) = _
    simp only [hstep2, hstep1]
    rw [h3, h4, h1, h2]
    have hof : BitVec.ofNat 8 bv.toNat = bv := by simp
    simp [hof]
    intro hc
    cases hc

private theorem valueToBytes_i8_singleton (v : IntW 8) :
    ∃ b : MemByte, valueToBytes .default64LE .modern (.bv 8 v) (.int (.concrete 8)) = #[b] := by
  have hloop : ∀ (fn : Nat → MemBit) (i rem : Nat) (b : MemByte),
      ∃ b', writeBitLoop .default64LE 0 fn i rem #[b] = #[b'] := by
    intro fn i rem
    induction rem generalizing i with
    | zero => intro b; exact ⟨b, rfl⟩
    | succ r ih =>
      intro b
      simp only [writeBitLoop, setLogicalBit, getLogicalByte, setLogicalByte,
                 AST.DataLayout.default64LE, Nat.zero_add]
      by_cases hi : i / 8 < 1
      · have hdiv : i / 8 = 0 := by omega
        simp [hdiv]
        exact ih (i + 1) (b.setBit (i % 8) (fn i))
      · simp [hi]
        exact ih (i + 1) b
  simp only [valueToBytes, writeScalarBits, AST.DataLayout.typeStoreSize,
             AST.DataLayout.typeSizeInBits, AST.DataLayout.default64LE]
  rcases v with ⟨none | bv⟩
  · exact hloop _ 0 _ MemByte.zero
  · exact hloop _ 0 _ MemByte.zero

private def stackI8Obj : MemoryObject :=
  { allocId := 1, baseAddr := 8, size := 1, align := 1, addrSpace := 0, name := "p",
    state := .alive, allocKind := .stack, isConstant := false,
    bytes := Array.replicate 1 MemByte.poison }

private def stackI8Mem : MemoryState :=
  { nextAllocId := 2, nextAddr := 10, usedMem := 1,
    objects := (∅ : Std.ExtHashMap AllocId MemoryObject).insert 1 stackI8Obj }

private theorem alloc_stack_i8 :
    MemoryState.allocate {} AST.DataLayout.default64LE SemanticsConfig.modern 1 1 "p" 0 .uninitialized .stack =
      .ok (stackI8Obj, stackI8Mem) := by
  simp [MemoryState.allocate, MemoryState.exceedsMaxObjectSize, AST.DataLayout.default64LE,
        AST.DataLayout.getPointerLayout, AST.DataLayout.alignTo, SemanticsConfig.modern,
        MemByte.uninitFor, stackI8Obj, stackI8Mem]

private theorem derive_stack_i8 :
    MemoryState.derivePointer AST.DataLayout.default64LE stackI8Obj =
      { prov := .concrete 1, addrWidth := 64, addr := 8#64 } := by
  simp [MemoryState.derivePointer, stackI8Obj, AST.DataLayout.default64LE, AST.DataLayout.getPointerLayout]

private theorem verify_store_stack_i8 :
    stackI8Mem.verifyMemAccess { prov := .concrete 1, addrWidth := 64, addr := 8#64 } 1 1 true =
      .ok (stackI8Obj, 0) := by
  simp [MemoryState.verifyMemAccess, MemoryState.resolveObject?, stackI8Mem, stackI8Obj]

private def stackI8ObjWith (b : MemByte) : MemoryObject :=
  { stackI8Obj with bytes := #[b] }

private theorem read_after_write_singleton (b : MemByte) :
    let mem2 := stackI8Mem.writeObjectBytes 1 0 #[b]
    mem2.verifyMemAccess { prov := .concrete 1, addrWidth := 64, addr := 8#64 } 1 1 false =
      .ok (stackI8ObjWith b, 0) ∧
    MemoryState.readObjectBytes (stackI8ObjWith b) 0 1 = #[b] := by
  constructor
  · simp [MemoryState.writeObjectBytes, MemoryState.verifyMemAccess, MemoryState.resolveObject?,
          stackI8Mem, stackI8Obj, stackI8ObjWith]
  · rfl

theorem ret_x_refines_alloca_store_load_i8 :
  open scoped LeanNanoLlvm.AST.Syntax in
  [llvm-definition|
    define i8 @f(i8 %x) {
    entry:
      ret i8 %x
    }
  ]
  ⊑
  [llvm-definition|
    define i8 @f(i8 %x) {
    entry:
      %p = alloca i8, align 1
      store i8 %x, ptr %p, align 1
      %v = load i8, ptr %p, align 1
      ret i8 %v
    }
  ]
  := by
  intro args _ _ _ hargs
  right
  cases args with
  | nil => simp [Definition.ArgValuesWellFormed] at hargs
  | cons arg rest =>
    cases rest with
    | cons _ _ => simp [Definition.ArgValuesWellFormed] at hargs
    | nil =>
      cases arg <;> simp [Definition.ArgValuesWellFormed, RegisterValue.WellFormedFor] at hargs
      subst hargs
      rename_i v
      have hpx : (AST.Identifier.local_id (.name "p") == AST.Identifier.local_id (.name "x")) = false := rfl
      have hallocId : stackI8Obj.allocId = 1 := rfl
      have hsize : AST.DataLayout.default64LE.typeAllocSize (.int (.concrete 8)) = 1 := by
        simp [AST.DataLayout.default64LE, AST.DataLayout.typeAllocSize, AST.DataLayout.typeStoreSize,
              AST.DataLayout.typeSizeInBits, AST.DataLayout.typeABIAlign, AST.DataLayout.intABIAlign,
              AST.DataLayout.alignTo]
      have hstore : AST.DataLayout.default64LE.typeStoreSize (.int (.concrete 8)) = 1 := by
        simp [AST.DataLayout.default64LE, AST.DataLayout.typeStoreSize, AST.DataLayout.typeSizeInBits]
      obtain ⟨b, hb⟩ := valueToBytes_i8_singleton v
      have hrt : ∀ o : OracleState,
          bytesToValue .default64LE .modern #[b] (.int (.concrete 8)) o = (.bv 8 v, v == .poison, o) := by
        intro o
        rw [← hb]
        exact byte_roundtrip_i8 v o
      have hmem := read_after_write_singleton b
      constructor
      · intro _ o'
        exact ⟨.bv 8 v, by simp [simp_llvm]⟩
      · intro o retVal h
        have hret : retVal = .bv 8 v := by
          simp [simp_llvm] at h
          exact h.symm
        subst hret
        refine ⟨o, .bv 8 v, ?_, RegisterValue.Refines.refl _⟩
        simp [simp_llvm, evalTypedExp, concretizeType, writeRegister, freeCurrentFrameAllocas,
              AST.RawId.ToString, Std.ExtHashMap.getElem_insert, hpx, hallocId,
              hsize, hstore, alloc_stack_i8, derive_stack_i8, verify_store_stack_i8,
              hb, hmem.1, hmem.2, hrt]

end LeanNanoLlvm.Refinement
