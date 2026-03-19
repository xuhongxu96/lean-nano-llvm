import LeanNanoLlvm.AST
import LeanNanoLlvm.Tactic
import LeanNanoLlvm.Semantics

open LeanNanoLlvm

open AST.Syntax
open Semantics

section

open scoped LeanNanoLlvm.AST.Syntax

def runCodeToMsg {φ : Nat} (c : @LeanNanoLlvm.AST.Code φ) (resKey : AST.Identifier) : String :=
  match runNanoLlvmStateMWithState (evalNanoLlvmCode c) with
  | .ok ((_, st), _) => s!"ok: {st.registers.get? resKey}"
  | .error e => s!"error: {e}"

#eval runCodeToMsg [llvm-code|
  %1 = add i8 1, 2
  %2 = mul i8 %1, 8
] [llvm-identifier| %2]

theorem add_two_i32 : forall (a b : ℤ),
  (do
    let ((_, st), _) ← runNanoLlvmStateMWithState (evalNanoLlvmCode (
      [llvm-code| %1 = add i32 <a:int>, <b:int>]
    )
    )
    pure (match st.registers.get? [llvm-identifier| %1] with
      | some (.bv 32 v) => some v
      | _ => none)
  ) = .ok (some (.value ((a : BitVec 32) + (b : BitVec 32)))) := by
  intros
  simp [simp_llvm]
  rfl


theorem add_two_i32_then_trunc_to_i8 : forall (a b : ℤ),
  (do
    let ((_, st), _) ← runNanoLlvmStateMWithState (evalNanoLlvmCode (
      [llvm-code|
        %1 = add i32 <a:int>, <b:int>
        %2 = trunc i32 %1 to i8
      ]
    ))

    pure (match st.registers.get? [llvm-identifier| %2] with
      | some (.bv 8 v) => some v
      | _ => none)
  ) = .ok (some (.value ((a : BitVec 32) + (b : BitVec 32) |>.setWidth 8))) := by
  intros
  simp [simp_llvm]
  rfl


theorem poison_propagates_through_add :
  (do
    let ((_, st), _) ← runNanoLlvmStateMWithState (evalNanoLlvmCode (
      [llvm-code|
        %p = add nsw i8 127, 1
        %y = add i8 %p, 1
      ]
    ))

    pure (match st.registers.get? [llvm-identifier| %y] with
      | some (.bv 8 v) => some v
      | _ => none)
  ) = .ok (some (.poison)) := by
  simp [simp_llvm]
  rfl

theorem freeze_of_nonpoison_is_identity :
  (do
    let ((_, st), _) ← runNanoLlvmStateMWithState (evalNanoLlvmCode (
      [llvm-code| %f = freeze i8 7]
    ))

    pure (match st.registers.get? [llvm-identifier| %f] with
      | some (.bv 8 v) => some v
      | _ => none)
  ) = .ok (some (.value (7 : BitVec 8))) := by
  simp [simp_llvm]
  rfl

theorem freeze_of_poison_returns_zero_current_model :
  (do
    let ((_, st), _) ← runNanoLlvmStateMWithState (evalNanoLlvmCode (
      [llvm-code|
        %p = add nsw i8 127, 1
        %f = freeze i8 %p
      ]
    ))

    pure (match st.registers.get? [llvm-identifier| %f] with
      | some (.bv 8 v) => some v
      | _ => none)
  ) = .ok (some (.value (0 : BitVec 8))) := by
  simp [simp_llvm]
  rfl

@[simp]
def runDefinitionRet {φ : Nat} (d : @AST.Definition φ) (args : List RegisterValue)
    (st : NanoLlvmState := default) : Except String RegisterValue := do
  runNanoLlvmStateM (evalNanoLlvmDefinition d args) st

theorem eval_definition_freeze_poison :
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
  simp [simp_llvm]
  rfl

theorem eval_definition_ret_void :
  runDefinitionRet
    [llvm-definition|
      define void @f() {
      entry:
        ret void
      }
    ]
    []
    = .ok .void := by
  simp [simp_llvm]
  rfl

def wfDefinition : @AST.Definition 0 :=
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

def badDefinitionDuplicateArgs : @AST.Definition 0 :=
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

def badDefinitionUnboundRet : @AST.Definition 0 :=
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


abbrev singletonWidths (w : Nat) : List.Vector Nat 1 := ⟨[w], by simp⟩

theorem runInstantiatedDefinition_poly :
    runInstantiatedDefinition (singletonWidths 8) [llvm-1-definition|
    define i$0 @f(i$0 %a) {
    entry:
      %x = add i$0 %a, 1
      ret i$0 %x
    }
  ] [ .bv 8 (.value (2 : BitVec 8)) ]
      = .ok (.bv 8 (.value (3 : BitVec 8))) := by
  simp [simp_llvm]
  rfl

end
