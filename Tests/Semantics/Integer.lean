import LeanNanoLlvm.AST
import LeanNanoLlvm.Tactic
import LeanNanoLlvm.Semantics
import Tests.Semantics.Helpers

/-! Semantics tests: core integer arithmetic, poison, freeze and well-formedness. -/

open LeanNanoLlvm
open AST.Syntax
open Semantics

section

open scoped LeanNanoLlvm.AST.Syntax

/-! ### Core Integer Arithmetic, Poison, Freeze & Well-Formedness -/

theorem add_two_i32 : ∀ (a b : Int),
  (do
    let (regs, _) ← runCode [llvm-code| %1 = add i32 <a:int>, <b:int>]
    pure (match regs.get? [llvm-identifier| %1] with
      | some (.bv 32 v) => some v
      | _ => none)
  ) = .ok (some (.value (BitVec.ofInt 32 a + BitVec.ofInt 32 b))) := by
  intro a b
  rfl

theorem add_two_i32_then_trunc_to_i8 : ∀ (a b : Int),
  (do
    let (regs, _) ← runCode [llvm-code|
      %1 = add i32 <a:int>, <b:int>
      %2 = trunc i32 %1 to i8
    ]
    pure (match regs.get? [llvm-identifier| %2] with
      | some (.bv 8 v) => some v
      | _ => none)
  ) = .ok (some (.value ((BitVec.ofInt 32 a + BitVec.ofInt 32 b).setWidth 8))) := by
  intro a b
  rfl

theorem poison_propagates_through_add :
  (do
    let (regs, _) ← runCode [llvm-code|
      %p = add nsw i8 127, 1
      %y = add i8 %p, 1
    ]
    pure (match regs.get? [llvm-identifier| %y] with
      | some (.bv 8 v) => some v
      | _ => none)
  ) = .ok (some .poison) := by
  decide +kernel

theorem freeze_of_nonpoison_is_identity :
  (do
    let (regs, _) ← runCode [llvm-code| %f = freeze i8 7]
    pure (match regs.get? [llvm-identifier| %f] with
      | some (.bv 8 v) => some v
      | _ => none)
  ) = .ok (some (.value (7 : BitVec 8))) := by
  decide +kernel

theorem freeze_of_poison_returns_zero_legacy_compat :
  (do
    let (regs, _) ← runCode [llvm-code|
      %p = add nsw i8 127, 1
      %f = freeze i8 %p
    ] .legacyCompat
    pure (match regs.get? [llvm-identifier| %f] with
      | some (.bv 8 v) => some v
      | _ => none)
  ) = .ok (some (.value (0 : BitVec 8))) := by
  decide +kernel

theorem freeze_of_poison_draws_from_oracle_modern :
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
    .modern
    .default64LE
    { oracle := NondetOracle.ofList [42] }
    = .ok (.bv 8 (.value (42 : BitVec 8))) := by
  decide +kernel

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
  decide +kernel

def wfDefinition : AST.Definition :=
  [llvm-definition|
    define i8 @f(i8 %a) {
    entry:
      %x = add i8 %a, 1
      ret i8 %x
    }
  ]

theorem wfDefinition_wellFormed : wfDefinition.WellFormed := by
  rw [AST.definition_wellFormed_iff, AST.definition_wellFormedWith_iff]
  refine ⟨_, _, _, ?_, rfl, rfl, by simp [wfDefinition], by simp [wfDefinition], by simp [wfDefinition], ?_⟩
  · rw [AST.declaration_wellFormed_iff]
    simp [AST.Declaration.WellFormedType, wfDefinition]
  · simp [wfDefinition, simp_wellform]

def badDefinitionDuplicateArgs : AST.Definition :=
  [llvm-definition|
    define i8 @f(i8 %a, i8 %a) {
    entry:
      ret i8 %a
    }
  ]

theorem badDefinitionDuplicateArgs_not_wellFormed :
    ¬ badDefinitionDuplicateArgs.WellFormed := by
  rw [AST.definition_wellFormed_iff, AST.definition_wellFormedWith_iff]
  simp [badDefinitionDuplicateArgs, simp_wellform]

def badDefinitionUnboundRet : AST.Definition :=
  [llvm-definition|
    define i8 @f() {
    entry:
      ret i8 %x
    }
  ]

theorem badDefinitionUnboundRet_not_wellFormed :
    ¬ badDefinitionUnboundRet.WellFormed := by
  rw [AST.definition_wellFormed_iff, AST.definition_wellFormedWith_iff]
  simp [badDefinitionUnboundRet, simp_wellform]

theorem wfDefinition_argValuesWellFormed :
    Semantics.Definition.ArgValuesWellFormed wfDefinition [RegisterValue.bv 8 (.value (7 : BitVec 8))] := by
  simp [Semantics.Definition.ArgValuesWellFormed, Semantics.RegisterValue.WellFormedForList,
        Semantics.RegisterValue.WellFormedFor, wfDefinition]

theorem wfDefinition_argValuesIllFormed_wrongWidth :
    ¬ Semantics.Definition.ArgValuesWellFormed wfDefinition [RegisterValue.bv 16 (.value (7 : BitVec 16))] := by
  simp [Semantics.Definition.ArgValuesWellFormed, Semantics.RegisterValue.WellFormedForList,
        Semantics.RegisterValue.WellFormedFor, wfDefinition]

theorem wfDefinition_argValuesIllFormed_wrongArity :
    ¬ Semantics.Definition.ArgValuesWellFormed wfDefinition [] := by
  simp [Semantics.Definition.ArgValuesWellFormed, Semantics.RegisterValue.WellFormedForList, wfDefinition]

/-- Width-parametric definition using plain Lean `Nat` antiquotation `i$(w)`. -/
def addOneDef (w : Nat) : AST.Definition :=
  [llvm-definition|
    define i$(w) @f(i$(w) %a) {
    entry:
      %x = add i$(w) %a, 1
      ret i$(w) %x
    }
  ]

theorem runDefinition_width_antiquot :
    runDefinition (addOneDef 8) [.bv 8 (.value (2 : BitVec 8))] =
      .ok (.bv 8 (.value (3 : BitVec 8))) := by
  decide +kernel

end
