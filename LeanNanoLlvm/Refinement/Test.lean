import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

open scoped LeanNanoLlvm.AST.Syntax in
def addDef : @AST.Definition 0 := [llvm-definition|
  define i8 @f(i8 %a, i8 %b) {
  entry:
    %x = add i8 %a, %b
    ret i8 %x
  }
]

theorem addDef_refines_itself : addDef ⊑ addDef := by
  intro args retval _ _ _ _ u h
  exact ⟨u, h⟩

theorem ret_add_x_0_refines_ret_x :
  open scoped LeanNanoLlvm.AST.Syntax in
  [llvm-definition|
    define i8 @f(i8 %x) {
    entry:
      %x = add i8 %x, 0
      ret i8 %x
    }
  ] ⊑ [llvm-definition|
    define i8 @f(i8 %x) {
    entry:
      ret i8 %x
    }
  ] := by
  intro args retval hwfAdd hwfRet hsig hargs u h
  cases args with
  | nil =>
      simp [Definition.ArgValuesWellFormed] at hargs
  | cons arg rest =>
      cases rest with
      | nil =>
          cases arg <;> simp [Definition.ArgValuesWellFormed,
            RegisterValue.WellFormedFor] at hargs
          rename_i w v
          subst hargs
          simp [simp_llvm, simp_wellform, simp_llvm_option] at *
      | cons arg' rest' =>
          simp [Definition.ArgValuesWellFormed] at hargs

abbrev singletonWidths (w : Nat) : List.Vector Nat 1 := ⟨[w], by simp⟩

theorem ret_add_x_0_refines_ret_x_generic (w : Nat) :
  open scoped LeanNanoLlvm.AST.Syntax in
  [llvm-1-definition|
    define i$0 @f(i$0 %x) {
    entry:
      %x = add i$0 %x, 0
      ret i$0 %x
    }
  ].instantiateWidths (singletonWidths w)
  ⊑
  [llvm-1-definition|
    define i$0 @f(i$0 %x) {
    entry:
      ret i$0 %x
    }
  ].instantiateWidths (singletonWidths w) := by
  intro args retval hwfAdd hwfRet hsig hargs u h
  cases args with
  | nil =>
      simp [Definition.ArgValuesWellFormed, singletonWidths] at hargs
  | cons arg rest =>
      cases rest with
      | nil =>
          cases arg <;> simp [Definition.ArgValuesWellFormed,
            RegisterValue.WellFormedFor, singletonWidths] at hargs
          rename_i w' v
          subst hargs
          simp [singletonWidths, simp_llvm, simp_wellform, simp_llvm_option] at *
      | cons arg' rest' =>
          simp [Definition.ArgValuesWellFormed, singletonWidths] at hargs

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

theorem undef_add_refines_undef_mul2 : undefAddDef ⊑ undefMul2Def := by
  intro args retval hwfAdd hwfMul hsig hargs u h
  cases args with
  | nil =>
    simp [Definition.ArgValuesWellFormed] at hargs
    cases u with
    | nil =>
        have hnil :
            runNanoLlvmStateM (denoteNanoLlvmDefinition undefMul2Def []) default ({ supplyChain := [], supplyIndex := 0 }) =
              Except.error "" := by
          rfl
        rw [hnil] at h
        cases h
    | cons x xs =>
      have hx :
          runNanoLlvmStateM (denoteNanoLlvmDefinition undefMul2Def []) default ({ supplyChain := x :: xs, supplyIndex := 0 }) =
            Except.ok (RegisterValue.bv 1 (.value (0 : BitVec 1))) := by
        simp [simp_llvm]
        rfl
      refine ⟨[0, 0], ?_⟩
      have haddRun :
          runNanoLlvmStateM (denoteNanoLlvmDefinition undefAddDef []) default ({ supplyChain := [0, 0], supplyIndex := 0 }) =
            Except.ok (RegisterValue.bv 1 (.value (0 : BitVec 1))) := by
        simp [simp_llvm]
        rfl
      simp_all
  | cons arg rest =>
    simp [Definition.ArgValuesWellFormed] at hargs

theorem undef_add_not_refines_undef_mul2 : ¬ (undefMul2Def ⊑ undefAddDef) := by
  intro h
  have haddRun :
      runNanoLlvmStateM (denoteNanoLlvmDefinition undefAddDef []) default
        ({ supplyChain := [1, 0], supplyIndex := 0 }) =
        Except.ok (RegisterValue.bv 1 (.value (1 : BitVec 1))) := by
    simp [simp_llvm]
    rfl
  obtain ⟨u', hu'⟩ := h [] (RegisterValue.bv 1 (.value (1 : BitVec 1)))
    (by simp [simp_wellform])
    (by simp [simp_wellform])
    (by rfl)
    (by simp [Definition.ArgValuesWellFormed, simp_wellform])
    [1, 0] haddRun
  cases u' with
  | nil =>
      have hnil :
          runNanoLlvmStateM (denoteNanoLlvmDefinition undefMul2Def []) default
            ({ supplyChain := [], supplyIndex := 0 }) =
            Except.error "" := by
        rfl
      rw [hnil] at hu'
      cases hu'
  | cons x xs =>
      have hmulRun :
          runNanoLlvmStateM (denoteNanoLlvmDefinition undefMul2Def []) default
            ({ supplyChain := x :: xs, supplyIndex := 0 }) =
            Except.ok (RegisterValue.bv 1 (.value (0 : BitVec 1))) := by
        simp [simp_llvm]
        rfl
      rw [hmulRun] at hu'
      cases hu'

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

private theorem bitvec8_double_eq_mul_two (b : BitVec 8) :
    b + b = b * (2 : BitVec 8) := by
  apply BitVec.eq_of_toFin_eq
  apply Fin.ext
  simp [Fin.val_add, Fin.val_mul, BitVec.toFin_ofNat]
  rw [← Nat.two_mul b.toNat, Nat.mul_comm]

private theorem bitvec8_mul_two_ne_one (b : BitVec 8) :
    b * (2 : BitVec 8) ≠ (1 : BitVec 8) := by
  intro h
  have hval : (((b * (2 : BitVec 8)).toFin : Fin 256) : Nat) = (((1 : BitVec 8).toFin : Fin 256) : Nat) := by
    simpa using congrArg Fin.val (congrArg BitVec.toFin h)
  simp [Fin.val_mul, BitVec.toFin_ofNat] at hval
  have hmod := congrArg (fun n => n % 2) hval
  have hleft : ((b.toNat * 2) % 256) % 2 = 0 := by
    rw [show 256 = 128 * 2 by decide, Nat.mod_mul_left_mod]
    rw [Nat.mul_mod]
    simp
  simp [hleft] at hmod

theorem undef_add_refines_undef_mul2_i8 : undefAddDef8 ⊑ undefMul2Def8 := by
  intro args retval hwfAdd hwfMul hsig hargs u h
  cases args with
  | nil =>
    simp [Definition.ArgValuesWellFormed] at hargs
    cases u with
    | nil =>
        have hnil :
            runNanoLlvmStateM (denoteNanoLlvmDefinition undefMul2Def8 []) default
              ({ supplyChain := [], supplyIndex := 0 }) =
              Except.error "" := by
          rfl
        rw [hnil] at h
        cases h
    | cons x xs =>
      have hmulRun :
          runNanoLlvmStateM (denoteNanoLlvmDefinition undefMul2Def8 []) default
            ({ supplyChain := x :: xs, supplyIndex := 0 }) =
            Except.ok (RegisterValue.bv 8 (.value ((BitVec.ofNat 8 x) * (2 : BitVec 8)))) := by
        simp [simp_llvm]
        rfl
      refine ⟨[x, x], ?_⟩
      have haddRun :
          runNanoLlvmStateM (denoteNanoLlvmDefinition undefAddDef8 []) default
            ({ supplyChain := [x, x], supplyIndex := 0 }) =
            Except.ok (RegisterValue.bv 8 (.value ((BitVec.ofNat 8 x) + (BitVec.ofNat 8 x)))) := by
        simp [simp_llvm]
        rfl
      rw [hmulRun] at h
      injection h with hret
      rw [haddRun]
      simp_all [bitvec8_double_eq_mul_two]
  | cons arg rest =>
    simp [Definition.ArgValuesWellFormed] at hargs

theorem undef_add_not_refines_undef_mul2_i8 : ¬ (undefMul2Def8 ⊑ undefAddDef8) := by
  intro h
  have haddRun :
      runNanoLlvmStateM (denoteNanoLlvmDefinition undefAddDef8 []) default
        ({ supplyChain := [1, 0], supplyIndex := 0 }) =
        Except.ok (RegisterValue.bv 8 (.value (1 : BitVec 8))) := by
    simp [simp_llvm]
    rfl
  obtain ⟨u', hu'⟩ := h [] (RegisterValue.bv 8 (.value (1 : BitVec 8)))
    (by simp [simp_wellform])
    (by simp [simp_wellform])
    (by rfl)
    (by simp [Definition.ArgValuesWellFormed, simp_wellform])
    [1, 0] haddRun
  cases u' with
  | nil =>
      have hnil :
          runNanoLlvmStateM (denoteNanoLlvmDefinition undefMul2Def8 []) default
            ({ supplyChain := [], supplyIndex := 0 }) =
            Except.error "" := by
        rfl
      rw [hnil] at hu'
      cases hu'
  | cons x xs =>
      have hmulRun :
          runNanoLlvmStateM (denoteNanoLlvmDefinition undefMul2Def8 []) default
            ({ supplyChain := x :: xs, supplyIndex := 0 }) =
            Except.ok (RegisterValue.bv 8 (.value ((BitVec.ofNat 8 x) * (2 : BitVec 8)))) := by
        simp [simp_llvm]
        rfl
      rw [hmulRun] at hu'
      injection hu' with hu'
      injection hu' with _ hu'
      injection hu' with hu'
      injection hu' with hu'
      exact bitvec8_mul_two_ne_one (BitVec.ofNat 8 x) hu'

private theorem bitvec_double_eq_mul_two_generic {w : Nat} (b : BitVec w) :
    b + b = b * (2 : BitVec w) := by
  apply BitVec.eq_of_toFin_eq
  apply Fin.ext
  simp [Fin.val_add, Fin.val_mul, BitVec.toFin_ofNat]
  rw [← Nat.two_mul b.toNat, Nat.mul_comm]

private theorem bitvec_mul_two_ne_one_generic {w : Nat} (hpos : 0 < w) (b : BitVec w) :
    b * (2 : BitVec w) ≠ BitVec.ofNat w 1 := by
  intro h
  have hval :
      (((b * (2 : BitVec w)).toFin : Fin (2 ^ w)) : Nat) =
        (((BitVec.ofNat w 1).toFin : Fin (2 ^ w)) : Nat) := by
    simpa using congrArg Fin.val (congrArg BitVec.toFin h)
  simp [Fin.val_mul, BitVec.toFin_ofNat] at hval
  have hmod := congrArg (fun n => n % 2) hval
  have hright : (1 % 2 ^ w) % 2 = 1 := by
    cases w with
    | zero => cases Nat.not_lt_zero _ hpos
    | succ n =>
        rw [show 2 ^ Nat.succ n = 2 ^ n * 2 by rw [Nat.pow_succ]]
        rw [Nat.mod_mul_left_mod]
  simp [hright] at hmod

open scoped LeanNanoLlvm.AST.Syntax in
theorem undef_add_refines_undef_mul2_generic (w : Nat) :
  [llvm-1-definition|
    define i$0 @f() {
      entry:
        %x = add i$0 undef, undef
        ret i$0 %x
    }
  ].instantiateWidths (singletonWidths w)
  ⊑
  [llvm-1-definition|
    define i$0 @f() {
      entry:
        %x = mul i$0 undef, 2
        ret i$0 %x
    }
  ].instantiateWidths (singletonWidths w) := by
  intro args retval hwfAdd hwfMul hsig hargs u h
  cases args with
  | nil =>
    simp [Definition.ArgValuesWellFormed] at hargs
    cases u with
    | nil =>
        have hnil :
            runNanoLlvmStateM (denoteNanoLlvmDefinition ([llvm-1-definition|
              define i$0 @f() {
                entry:
                  %x = mul i$0 undef, 2
                  ret i$0 %x
              }
            ].instantiateWidths (singletonWidths w)) []) default
              ({ supplyChain := [], supplyIndex := 0 }) =
              Except.error "" := by
          simp
          rfl
        rw [hnil] at h
        cases h
    | cons x xs =>
      have hmulRun :
          runNanoLlvmStateM (denoteNanoLlvmDefinition ([llvm-1-definition|
            define i$0 @f() {
              entry:
                %x = mul i$0 undef, 2
                ret i$0 %x
            }
          ].instantiateWidths (singletonWidths w)) []) default
            ({ supplyChain := x :: xs, supplyIndex := 0 }) =
            Except.ok (RegisterValue.bv w (.value ((BitVec.ofNat w x) * (2 : BitVec w)))) := by
        simp [simp_llvm]
        rfl
      refine ⟨[x, x], ?_⟩
      have haddRun :
          runNanoLlvmStateM (denoteNanoLlvmDefinition ([llvm-1-definition|
            define i$0 @f() {
              entry:
                %x = add i$0 undef, undef
                ret i$0 %x
            }
          ].instantiateWidths (singletonWidths w)) []) default
            ({ supplyChain := [x, x], supplyIndex := 0 }) =
            Except.ok (RegisterValue.bv w (.value ((BitVec.ofNat w x) + (BitVec.ofNat w x)))) := by
        simp [simp_llvm]
        rfl
      rw [hmulRun] at h
      -- injection h with hret
      rw [haddRun]
      injection h with h
      simp_all [bitvec_double_eq_mul_two_generic]
  | cons arg rest =>
    simp [Definition.ArgValuesWellFormed] at hargs


end LeanNanoLlvm.Refinement
