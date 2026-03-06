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
  ) = .ok (some (.value ((a : BitVec 32) + (b : BitVec 32) |>.setWidth 8))) := by
  intros
  simp [simp_llvm, simp_llvm_option]
  rfl

@[simp]
def stWithUndef0_i8_5 : NanoLlvmState :=
  { registers := (default : NanoLlvmState).registers
  , undefs := (default : NanoLlvmState).undefs.insert [llvm-rawid| 0] (.bv 8 (.value (5 : BitVec 8)))
  }

theorem add_with_assigned_undef_i8 :
  (do
    let (_, st) ← (denoteNanoLlvmCode (
      [llvm-code| %y = add i8 undef, 1]
    )).run stWithUndef0_i8_5

    pure (match st.registers.get? [llvm-identifier| %y] with
      | some (.bv 8 v) => some v
      | _ => none)
  ) = .ok (some (.value (6 : BitVec 8))) := by
  simp [stWithUndef0_i8_5, simp_llvm, simp_llvm_option]
  rfl

theorem poison_propagates_through_add :
  (do
    let (_, st) ← (denoteNanoLlvmCode (
      [llvm-code|
        %p = add nsw i8 127, 1
        %y = add i8 %p, 1
      ]
    )).run (default : NanoLlvmState)

    pure (match st.registers.get? [llvm-identifier| %y] with
      | some (.bv 8 v) => some v
      | _ => none)
  ) = .ok (some (.poison)) := by
  simp [simp_llvm, simp_llvm_option]
  rfl

theorem freeze_of_nonpoison_is_identity :
  (do
    let (_, st) ← (denoteNanoLlvmCode (
      [llvm-code| %f = freeze i8 7]
    )).run (default : NanoLlvmState)

    pure (match st.registers.get? [llvm-identifier| %f] with
      | some (.bv 8 v) => some v
      | _ => none)
  ) = .ok (some (.value (7 : BitVec 8))) := by
  simp [simp_llvm, simp_llvm_option]
  rfl

theorem freeze_of_poison_returns_zero_current_model :
  (do
    let (_, st) ← (denoteNanoLlvmCode (
      [llvm-code|
        %p = add nsw i8 127, 1
        %f = freeze i8 %p
      ]
    )).run (default : NanoLlvmState)

    pure (match st.registers.get? [llvm-identifier| %f] with
      | some (.bv 8 v) => some v
      | _ => none)
  ) = .ok (some (.value (0 : BitVec 8))) := by
  simp [simp_llvm, simp_llvm_option]
  rfl

theorem freeze_of_assigned_undef_value :
  (do
    let (_, st) ← (denoteNanoLlvmCode (
      [llvm-code| %f = freeze i8 undef]
    )).run stWithUndef0_i8_5

    pure (match st.registers.get? [llvm-identifier| %f] with
      | some (.bv 8 v) => some v
      | _ => none)
  ) = .ok (some (.value (5 : BitVec 8))) := by
  simp [stWithUndef0_i8_5, simp_llvm, simp_llvm_option]
  rfl

@[simp]
def runDefinitionRet {φ : Nat} (d : @AST.Definition φ) (args : List RegisterValue)
    (st : NanoLlvmState := default) : Except String RegisterValue := do
  let (retval, _) ← (denoteNanoLlvmDefinition d args).run st
  pure retval

theorem denote_definition_with_undef :
  runDefinitionRet
    [llvm-definition|
      define i8 @f(i8 %a) {
      entry:
        %x = add i8 undef, %a
        ret i8 %x
      }
    ]
    [ .bv 8 (.value (1 : BitVec 8)) ]
    stWithUndef0_i8_5
    = .ok (.bv 8 (.value (6 : BitVec 8))) := by
  simp [simp_llvm, simp_llvm_option]
  rfl

theorem denote_definition_freeze_poison :
  runDefinitionRet
    [llvm-definition|
      define i8 @f() {
      entry:
        %p = add nsw i8 127, 1
        %f = freeze i8 %p
        ret i8 %f
      }
    ]
    []
    = .ok (.bv 8 (.value (0 : BitVec 8))) := by
  simp [simp_llvm, simp_llvm_option]
  rfl

theorem denote_definition_ret_void :
  runDefinitionRet
    [llvm-definition|
      define void @f() {
      entry:
        ret void
      }
    ]
    []
    = .ok .void := by
  simp [simp_llvm, simp_llvm_option]
  rfl

def wfDefinition : @AST.Definition 512 :=
  [llvm-definition|
    define i8 @f(i8 %a) {
    entry:
      %x = add i8 %a, 1
      ret i8 %x
    }
  ]

theorem wfDefinition_wellFormed : wfDefinition.WellFormed := by
  rw [AST.definition_wellFormed_iff]
  refine ⟨_, _, ?_, rfl, rfl, by simp [wfDefinition], ?_, ?_⟩
  . rw [AST.declaration_wellFormed_iff]
    simp [AST.Declaration.WellFormedType, wfDefinition]
  . simp [wfDefinition, AST.Code.WellFormedFrom, AST.Instruction.WellFormedWith,
      AST.Exp.WellFormedFor, AST.Exp.WellScopedTo, AST.InstructionId.DefinesLocal]
  . simp [wfDefinition, AST.Terminator.WellFormedWith, AST.Code.definedIds,
      AST.Exp.WellFormedFor, AST.Exp.WellScopedTo]

def badDefinitionDuplicateArgs : @AST.Definition 512 :=
  [llvm-definition|
    define i8 @f(i8 %a, i8 %a) {
    entry:
      ret i8 %a
    }
  ]

theorem badDefinitionDuplicateArgs_not_wellFormed :
    ¬ badDefinitionDuplicateArgs.WellFormed := by
  rw [AST.definition_wellFormed_iff]
  simp [badDefinitionDuplicateArgs, AST.Code.WellFormedFrom, AST.Terminator.WellFormedWith,
    AST.Exp.WellFormedFor, AST.Exp.WellScopedTo, AST.Code.definedIds]

def badDefinitionUnboundRet : @AST.Definition 512 :=
  [llvm-definition|
    define i8 @f() {
    entry:
      ret i8 %x
    }
  ]

theorem badDefinitionUnboundRet_not_wellFormed :
    ¬ badDefinitionUnboundRet.WellFormed := by
  rw [AST.definition_wellFormed_iff]
  simp [badDefinitionUnboundRet, AST.Code.WellFormedFrom, AST.Terminator.WellFormedWith,
    AST.Exp.WellFormedFor, AST.Exp.WellScopedTo, AST.Code.definedIds]

theorem wfDefinition_argValuesWellFormed :
    Semantics.Definition.ArgValuesWellFormed wfDefinition [RegisterValue.bv 8 (.value (7 : BitVec 8))] := by
  simp [Semantics.Definition.ArgValuesWellFormed, Semantics.RegisterValue.WellFormedFor, wfDefinition]

theorem wfDefinition_argValuesIllFormed_wrongWidth :
    ¬ Semantics.Definition.ArgValuesWellFormed wfDefinition [RegisterValue.bv 16 (.value (7 : BitVec 16))] := by
  simp [Semantics.Definition.ArgValuesWellFormed, Semantics.RegisterValue.WellFormedFor, wfDefinition]

theorem wfDefinition_argValuesIllFormed_wrongArity :
    ¬ Semantics.Definition.ArgValuesWellFormed wfDefinition [] := by
  simp [Semantics.Definition.ArgValuesWellFormed, wfDefinition]

end
