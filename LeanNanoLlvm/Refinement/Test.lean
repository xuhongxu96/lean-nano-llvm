import LeanNanoLlvm.Refinement
import LeanNanoLlvm.AST.Syntax
import LeanNanoLlvm.AST.Unexpander

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

theorem addDef_is_refined_by_itself : addDef ⊑ addDef := by
  intro args _ _ _ _
  constructor
  · simp_all
  · intro u ret h
    exact ⟨u, Or.inl h⟩

theorem ret_add_x_0_is_refined_by_ret_x :
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
  intro args hwfAdd hwfRet hsig hargs
  constructor
  · intro hdefined u
    obtain ⟨ret_x, hx⟩ := hdefined u
    cases args with
    | nil =>
        simp [Definition.ArgValuesWellFormed] at hargs
    | cons arg rest =>
        cases rest with
        | nil =>
            cases arg <;> simp [Definition.ArgValuesWellFormed,
              RegisterValue.WellFormedFor] at hargs
            simp_all [simp_llvm, simp_wellform]
        | cons arg' rest' =>
            simp [Definition.ArgValuesWellFormed] at hargs
  · intro u ret h
    cases args with
    | nil =>
        simp [Definition.ArgValuesWellFormed] at hargs
    | cons arg rest =>
        cases rest with
        | nil =>
            cases arg <;> simp [Definition.ArgValuesWellFormed,
              RegisterValue.WellFormedFor] at hargs
            simp_all [simp_llvm, simp_wellform]
        | cons arg' rest' =>
            simp [Definition.ArgValuesWellFormed] at hargs

abbrev singletonWidths (w : Nat) : List.Vector Nat 1 := ⟨[w], by simp⟩

theorem ret_add_x_0_is_refined_by_ret_x_generic (w : Nat) :
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
  intro args hwfAdd hwfRet hsig hargs
  constructor
  · intro hdefined u
    obtain ⟨ret_x, hx⟩ := hdefined u
    cases args with
    | nil =>
        simp [Definition.ArgValuesWellFormed, singletonWidths] at hargs
    | cons arg rest =>
        cases rest with
        | nil =>
            cases arg <;> simp [Definition.ArgValuesWellFormed,
              RegisterValue.WellFormedFor, singletonWidths] at hargs
            simp_all [singletonWidths, simp_llvm, simp_wellform]
        | cons arg' rest' =>
            simp [Definition.ArgValuesWellFormed, singletonWidths] at hargs
  · intro u ret h
    cases args with
    | nil =>
        simp [Definition.ArgValuesWellFormed, singletonWidths] at hargs
    | cons arg rest =>
        cases rest with
        | nil =>
            cases arg <;> simp [Definition.ArgValuesWellFormed,
              RegisterValue.WellFormedFor, singletonWidths] at hargs
            simp_all [singletonWidths, simp_llvm, simp_wellform]
        | cons arg' rest' =>
            simp [Definition.ArgValuesWellFormed, singletonWidths] at hargs

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
    simp_all
  simp [Fin.val_mul, BitVec.toFin_ofNat] at hval
  have hmod := congrArg (fun n => n % 2) hval
  have hright : (1 % 2 ^ w) % 2 = 1 := by
    cases w with
    | zero => cases Nat.not_lt_zero _ hpos
    | succ n =>
      simp
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

theorem undef_add_is_refined_by_undef_mul2 : undefAddDef ⊑ undefMul2Def := by
  intro args hwfAdd hwfMul hsig hargs
  constructor
  · intro hdefined u'
    cases args with
    | nil =>
      have hnil : False := by
        have hrun :
            runNanoLlvmStateM (denoteNanoLlvmDefinition undefAddDef []) default
              ({ supplyChain := [], supplyIndex := 0 }) =
              Except.error "" := by
          rfl
        obtain ⟨ret_x, hret_x⟩ := hdefined []
        simp_all
      simp_all
    | cons arg rest =>
      simp [Definition.ArgValuesWellFormed] at hargs
  · intro u ret h
    cases args with
    | nil =>
      simp [Definition.ArgValuesWellFormed] at hargs
      cases u with
      | nil =>
          have hnil :
              runNanoLlvmStateM (denoteNanoLlvmDefinition undefMul2Def []) default ({ supplyChain := [], supplyIndex := 0 }) =
                Except.error "" := by
            rfl
          simp_all
      | cons x xs =>
        have hmulRun :
            runNanoLlvmStateM (denoteNanoLlvmDefinition undefMul2Def []) default ({ supplyChain := x :: xs, supplyIndex := 0 }) =
              Except.ok (RegisterValue.bv 1 (.value (0 : BitVec 1))) := by
          simp [simp_llvm]
          rfl
        refine ⟨[x, x], Or.inl ?_⟩
        have haddRun :
            runNanoLlvmStateM (denoteNanoLlvmDefinition undefAddDef []) default ({ supplyChain := [x, x], supplyIndex := 0 }) =
              Except.ok (RegisterValue.bv 1 (.value ((BitVec.ofNat 1 x) + (BitVec.ofNat 1 x)))) := by
          simp [simp_llvm]
          rfl
        simp_all [bitvec_double_eq_mul_two_generic]
    | cons arg rest =>
      simp [Definition.ArgValuesWellFormed] at hargs

theorem undef_mul2_is_not_refined_by_undef_add : ¬ (undefMul2Def ⊑ undefAddDef) := by
  intro h
  have haddRun :
      runNanoLlvmStateM (denoteNanoLlvmDefinition undefAddDef []) default
        ({ supplyChain := [1, 0], supplyIndex := 0 }) =
        Except.ok (RegisterValue.bv 1 (.value (1 : BitVec 1))) := by
    simp [simp_llvm]
    rfl
  obtain ⟨u', hu'⟩ := (h []
    (by simp [simp_wellform])
    (by simp [simp_wellform])
    (by rfl)
    (by simp [Definition.ArgValuesWellFormed, simp_wellform])
    ).2 [1, 0] (RegisterValue.bv 1 (.value (1 : BitVec 1))) haddRun
  cases u' with
  | nil =>
      have hnil :
          runNanoLlvmStateM (denoteNanoLlvmDefinition undefMul2Def []) default
            ({ supplyChain := [], supplyIndex := 0 }) =
            Except.error "" := by
        rfl
      simp_all
  | cons x xs =>
      have hmulRun :
          runNanoLlvmStateM (denoteNanoLlvmDefinition undefMul2Def []) default
            ({ supplyChain := x :: xs, supplyIndex := 0 }) =
            Except.ok (RegisterValue.bv 1 (.value (0 : BitVec 1))) := by
        simp [simp_llvm]
        rfl
      simp_all

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

theorem undef_add_is_refined_by_undef_mul2_i8 : undefAddDef8 ⊑ undefMul2Def8 := by
  intro args hwfAdd hwfMul hsig hargs
  constructor
  · intro hdefined u'
    cases args with
    | nil =>
      have hnil : False := by
        have hrun :
            runNanoLlvmStateM (denoteNanoLlvmDefinition undefAddDef8 []) default
              ({ supplyChain := [], supplyIndex := 0 }) =
              Except.error "" := by
          rfl
        obtain ⟨ret_x, hret_x⟩ := hdefined []
        simp_all
      simp_all
    | cons arg rest =>
      simp [Definition.ArgValuesWellFormed] at hargs
  · intro u ret h
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
          simp_all
      | cons x xs =>
        have hmulRun :
            runNanoLlvmStateM (denoteNanoLlvmDefinition undefMul2Def8 []) default
              ({ supplyChain := x :: xs, supplyIndex := 0 }) =
              Except.ok (RegisterValue.bv 8 (.value ((BitVec.ofNat 8 x) * (2 : BitVec 8)))) := by
          simp [simp_llvm]
          rfl
        refine ⟨[x, x], Or.inl ?_⟩
        have haddRun :
            runNanoLlvmStateM (denoteNanoLlvmDefinition undefAddDef8 []) default
              ({ supplyChain := [x, x], supplyIndex := 0 }) =
              Except.ok (RegisterValue.bv 8 (.value ((BitVec.ofNat 8 x) + (BitVec.ofNat 8 x)))) := by
          simp [simp_llvm]
          rfl
        simp_all [bitvec_double_eq_mul_two_generic]
    | cons arg rest =>
      simp [Definition.ArgValuesWellFormed] at hargs

theorem undef_mul2_is_not_refined_by_undef_add_i8 : ¬ (undefMul2Def8 ⊑ undefAddDef8) := by
  intro h
  have haddRun :
      runNanoLlvmStateM (denoteNanoLlvmDefinition undefAddDef8 []) default
        ({ supplyChain := [1, 0], supplyIndex := 0 }) =
        Except.ok (RegisterValue.bv 8 (.value (1 : BitVec 8))) := by
    simp [simp_llvm]
    rfl
  obtain ⟨u', hu'⟩ := (h []
    (by simp [simp_wellform])
    (by simp [simp_wellform])
    (by rfl)
    (by simp [Definition.ArgValuesWellFormed, simp_wellform])
    ).2 [1, 0] (RegisterValue.bv 8 (.value (1 : BitVec 8))) haddRun
  cases u' with
  | nil =>
      have hnil :
          runNanoLlvmStateM (denoteNanoLlvmDefinition undefMul2Def8 []) default
            ({ supplyChain := [], supplyIndex := 0 }) =
            Except.error "" := by
        rfl
      simp_all
  | cons x xs =>
      have hmulRun :
          runNanoLlvmStateM (denoteNanoLlvmDefinition undefMul2Def8 []) default
            ({ supplyChain := x :: xs, supplyIndex := 0 }) =
            Except.ok (RegisterValue.bv 8 (.value ((BitVec.ofNat 8 x) * (2 : BitVec 8)))) := by
        simp [simp_llvm]
        rfl
      simp_all
      have hcontra := bitvec_mul_two_ne_one_generic (by simp) (BitVec.ofNat 8 x)
      contradiction

open scoped LeanNanoLlvm.AST.Syntax in
theorem undef_add_is_refined_by_undef_mul2_generic (w : Nat) :
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
  intro args hwfAdd hwfMul hsig hargs
  constructor
  · intro hdefined u'
    cases args with
    | nil =>
      have hnil : False := by
        have hrun :
          runNanoLlvmStateM (denoteNanoLlvmDefinition ([llvm-1-definition|
            define i$0 @f() {
              entry:
                %x = add i$0 undef, undef
                ret i$0 %x
              }
            ].instantiateWidths (singletonWidths w)) []) default
              ({ supplyChain := [], supplyIndex := 0 }) =
              Except.error "" := by
          simp
          rfl
        obtain ⟨ret_x, hret_x⟩ := hdefined []
        simp_all
      exact False.elim hnil
    | cons arg rest =>
      simp [Definition.ArgValuesWellFormed] at hargs
  · intro u hRet h
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
          simp_all
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
        refine ⟨[x, x], Or.inl ?_⟩
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
        simp_all [bitvec_double_eq_mul_two_generic]
    | cons arg rest =>
      simp [Definition.ArgValuesWellFormed] at hargs

open scoped LeanNanoLlvm.AST.Syntax in
theorem undef_mul2_is_not_refined_by_undef_add_generic (w : Nat) (hpos : 0 < w) :
  ¬ ([llvm-1-definition|
    define i$0 @f() {
      entry:
        %x = mul i$0 undef, 2
        ret i$0 %x
    }
  ].instantiateWidths (singletonWidths w)
  ⊑
  [llvm-1-definition|
    define i$0 @f() {
      entry:
        %x = add i$0 undef, undef
        ret i$0 %x
    }
  ].instantiateWidths (singletonWidths w)) := by
  intro h
  have haddRun :
      runNanoLlvmStateM (denoteNanoLlvmDefinition ([llvm-1-definition|
        define i$0 @f() {
          entry:
            %x = add i$0 undef, undef
            ret i$0 %x
        }
      ].instantiateWidths (singletonWidths w)) []) default
        ({ supplyChain := [1, 0], supplyIndex := 0 }) =
      Except.ok (RegisterValue.bv w (.value (BitVec.ofNat w 1))) := by
    simp [simp_llvm]
    change Except.ok (RegisterValue.bv w (.value ((BitVec.ofNat w 1) + (BitVec.ofNat w 0)))) =
      Except.ok (RegisterValue.bv w (.value (BitVec.ofNat w 1)))
    simp
  obtain ⟨u', hu'⟩ := (h []
    (by simp [simp_wellform])
    (by simp [simp_wellform])
    (by rfl)
    (by simp [Definition.ArgValuesWellFormed, simp_wellform])
    ).2 [1, 0] (RegisterValue.bv w (.value (BitVec.ofNat w 1))) haddRun
  cases u' with
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
      simp_all
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
      simp_all
      have hcontra := bitvec_mul_two_ne_one_generic hpos (BitVec.ofNat w x)
      contradiction

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

private theorem run_poisonDef (u : UndefChain) :
    runNanoLlvmStateM (denoteNanoLlvmDefinition poisonDef []) default
      ({ supplyChain := u, supplyIndex := 0 }) =
    Except.ok (RegisterValue.bv 8 .poison) := by
  rfl

private theorem run_zeroDef (u : UndefChain) :
    runNanoLlvmStateM (denoteNanoLlvmDefinition zeroDef []) default
      ({ supplyChain := u, supplyIndex := 0 }) =
    Except.ok (RegisterValue.bv 8 (.value (0 : BitVec 8))) := by
  rfl

theorem poison_is_refined_by_zero : poisonDef ⊑ zeroDef := by
  intro args hwfPoison hwfZero hsig hargs
  constructor
  · intro _ u
    cases args with
    | nil =>
        refine ⟨RegisterValue.bv 8 (.value (0 : BitVec 8)), ?_⟩
        rfl
    | cons arg rest =>
        have : False := by
          simp [Definition.ArgValuesWellFormed, poisonDef] at hargs
        exact False.elim this
  · intro u ret h
    cases args with
    | nil =>
        refine ⟨u, Or.inr ?_⟩
        have hret : ret = RegisterValue.bv 8 (.value (0 : BitVec 8)) := by
          rw [run_zeroDef u] at h
          injection h with hret
          exact hret.symm
        subst ret
        exact ⟨RegisterValue.bv 8 .poison, run_poisonDef u, rfl⟩
    | cons arg rest =>
        have : False := by
          simp [Definition.ArgValuesWellFormed, poisonDef] at hargs
        exact False.elim this

theorem zero_is_not_refined_by_poison : ¬ (zeroDef ⊑ poisonDef) := by
  intro h
  obtain ⟨u', hu'⟩ := (h []
    (by simp [simp_wellform, zeroDef])
    (by simp [simp_wellform, poisonDef])
    (by rfl)
    (by simp [Definition.ArgValuesWellFormed, simp_wellform, zeroDef])
    ).2 [] (RegisterValue.bv 8 .poison) (run_poisonDef [])
  obtain ⟨ret_x, hret_x, href⟩ := hu'.elim
    (fun hret_x => False.elim (by
      rw [run_zeroDef u'] at hret_x
      cases hret_x))
    (fun h2 => h2)
  have hret0 : ret_x = RegisterValue.bv 8 (.value (0 : BitVec 8)) := by
    rw [run_zeroDef u'] at hret_x
    injection hret_x with hret0
    exact hret0.symm
  subst ret_x
  simp at href

end LeanNanoLlvm.Refinement
