import LeanNanoLlvm.AST
import LeanNanoLlvm.Tactic
import LeanNanoLlvm.Semantics

/-! Shared runners (`runCodeToMsg`, `runDefinitionRet`, UB/static-error predicates) for the semantics tests. -/

open LeanNanoLlvm
open AST.Syntax
open Semantics

section

open scoped LeanNanoLlvm.AST.Syntax

/-! ### Helper Runners -/

def runCodeToMsg (c : AST.Code) (resKey : AST.Identifier) : String :=
  match runCode c with
  | .ok (regs, _) => s!"ok: {regs.get? resKey}"
  | .error e => s!"error: {e}"

#eval runCodeToMsg [llvm-code|
  %1 = add i8 1, 2
  %2 = mul i8 %1, 8
] [llvm-identifier| %2]

@[simp]
def runDefinitionRet (d : AST.Definition) (args : List RegisterValue)
    (cfg : SemanticsConfig := .modern) (dl : AST.DataLayout := .default64LE)
    (o : OracleState := default) : Except ExecError RegisterValue :=
  runDefinition d args cfg dl o

def isImmediateUB {α : Type} : Except ExecError α → Bool
  | .error (.immediateUB _) => true
  | _ => false

def isStaticError {α : Type} : Except ExecError α → Bool
  | .error (.staticError _) => true
  | _ => false

end
