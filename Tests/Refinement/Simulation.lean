import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import LeanNanoLlvm.AST.Unexpander
import Tests.Refinement.Helpers

/-! Refinement tests: backward simulation on diverging loops. -/

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

/-! ### Backward Simulation (`Config.IsRefinedBy.of_simulation`) on Diverging Loops -/

open scoped LeanNanoLlvm.AST.Syntax in
def loopWithAddDef : AST.Definition := [llvm-definition|
  define void @spin(i32 %x) {
  entry:
    %y = add i32 %x, 0
    br label %entry
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
def tightLoopDef : AST.Definition := [llvm-definition|
  define void @spin(i32 %x) {
  entry:
    br label %entry
  }
]

/--
Eliminating a redundant `%y = add i32 %x, 0` inside an infinite loop preserves full behavioral
refinement (including `Diverges`), proved cleanly via `Config.IsRefinedBy.of_simulation` with
a 2-to-1 `PlusStep` simulation!
-/
theorem loop_with_add_is_refined_by_tight_loop :
    loopWithAddDef ⊒ tightLoopDef := by
  refine ⟨rfl, ?_⟩
  intro initMem args _ hargs
  rcases args with _ | ⟨arg, _ | _⟩
  · llvm_wf [loopWithAddDef] at hargs
  · cases arg <;> llvm_wf [loopWithAddDef] at hargs
    subst hargs
    rename_i v
    rw [initCallConfig_1 .modern .default64LE initMem loopWithAddDef rfl (Or.inl rfl) rfl rfl rfl rfl]
    rw [initCallConfig_1 .modern .default64LE initMem tightLoopDef rfl (Or.inl rfl) rfl rfl rfl rfl]
    let regs0 : AssocMap AST.Identifier RegisterValue :=
      (∅ : AssocMap AST.Identifier RegisterValue).insert (.local_id (.name "x")) (.bv 32 v)
    let stY : MachineState := {
      frames := [{ defn := tightLoopDef, curBlock := .name "entry", remainingCode := [],
                   terminator := entryTerm tightLoopDef, registers := regs0 }]
      memory := initMem, config := .modern, dataLayout := .default64LE }
    -- Source register map after 0 or more loop iterations (either `regs0` or `regs0.insert %y v`)
    let isSourceLoopState (cX : Config) : Prop :=
      ∃ regsX : AssocMap AST.Identifier RegisterValue,
        regsX.get? (.local_id (.name "x")) = some (.bv 32 v) ∧
        cX = .running {
          frames := [{ defn := loopWithAddDef, curBlock := .name "entry",
                       remainingCode := entryCode loopWithAddDef,
                       terminator := entryTerm loopWithAddDef, registers := regsX }]
          memory := initMem, config := .modern, dataLayout := .default64LE }
    let R : MemoryInjection → Config → Config → Prop :=
      fun inj cX cY => inj = .id ∧ isSourceLoopState cX ∧ cY = .running stY
    refine Config.IsRefinedBy.of_simulation R (fun _ => 0) ?_ ?_ ?_ (MemoryInjection.id_idOn _)
      ⟨rfl, ⟨regs0, by llvm_step [regs0], rfl⟩, rfl⟩
    · rintro _ _ _ _ ⟨_, _, hcY⟩; cases hcY
    · rintro _ _ _ ⟨_, _, hcY⟩ (⟨_, h⟩ | ⟨_, h⟩) <;> rw [hcY] at h <;> cases h
    · rintro inj cX cY evY cY' ⟨rfl, ⟨regsX, hgetX, rfl⟩, rfl⟩ hsY
      -- Target deterministically branches back to `stY`
      rw [Step.term_iff rfl rfl rfl] at hsY
      obtain ⟨rfl, hsY⟩ := hsY
      cases hsY with
      | br_step hj =>
        cases hj with
        | ok hfind hsplit hphi =>
          have hfind' : tightLoopDef.findBlock? (.name "entry") = some (tightLoopDef.blocks.head (by decide)) := rfl
          rw [hfind'] at hfind
          injection hfind with hblk; subst hblk
          cases hsplit
          cases hphi with
          | nil =>
            -- Source takes 2 steps (`add` then `br`) back to `isSourceLoopState`
            have haddVal : liftBinaryPure (.int 32) (.bv 32 v) (.bv 32 (.value 0#32))
                (evalIntBinaryScalarPure (.add false false)) = .ok (.bv 32 v) := by
              cases v using PoisonOr.casesOn' with
              | poison => llvm_simp
              | value bv => llvm_simp
            have hs1 : Step (.running {
                frames := [{ defn := loopWithAddDef, curBlock := .name "entry",
                             remainingCode := entryCode loopWithAddDef,
                             terminator := entryTerm loopWithAddDef, registers := regsX }]
                memory := initMem, config := .modern, dataLayout := .default64LE })
              none
              (.running {
                frames := [{ defn := loopWithAddDef, curBlock := .name "entry",
                             remainingCode := [],
                             terminator := entryTerm loopWithAddDef,
                             registers := regsX.insert (.local_id (.name "y")) (.bv 32 v) }]
                memory := initMem, config := .modern, dataLayout := .default64LE }) :=
              Step.instr rfl rfl
                (StepInstr.intBinaryOp_ok
                  (EvalExp.leaf_ok (by simp [evalPureLeafExp?, hgetX]))
                  (EvalExp.leaf_ok (by llvm_step))
                  haddVal)
            have hs2 : Step (.running {
                frames := [{ defn := loopWithAddDef, curBlock := .name "entry",
                             remainingCode := [],
                             terminator := entryTerm loopWithAddDef,
                             registers := regsX.insert (.local_id (.name "y")) (.bv 32 v) }]
                memory := initMem, config := .modern, dataLayout := .default64LE })
              none
              (.running {
                frames := [{ defn := loopWithAddDef, curBlock := .name "entry",
                             remainingCode := entryCode loopWithAddDef,
                             terminator := entryTerm loopWithAddDef,
                             registers := regsX.insert (.local_id (.name "y")) (.bv 32 v) }]
                memory := initMem, config := .modern, dataLayout := .default64LE }) :=
              Step.term rfl rfl rfl
                (StepTerm.br_step (StepJump.ok (nextBlk := loopWithAddDef.blocks.head (by decide)) rfl rfl EvalPhis.nil))
            have hyx : (AST.Identifier.local_id (.name "y") == AST.Identifier.local_id (.name "x")) = false := rfl
            refine Or.inr ⟨[], _, .id, MemoryInjection.Extends.refl _,
              Or.inl ⟨none, _, [], hs1, StarStep.single hs2, rfl⟩, trivial,
              rfl, ⟨regsX.insert (.local_id (.name "y")) (.bv 32 v),
                by simp [AssocMap.get?_insert, hyx, hgetX], rfl⟩, rfl⟩
        | phi_err hfind hsplit hphi =>
          have hfind' : tightLoopDef.findBlock? (.name "entry") = some (tightLoopDef.blocks.head (by decide)) := rfl
          rw [hfind'] at hfind
          injection hfind with hblk; subst hblk
          cases hsplit
          cases hphi
        | missing_block hfind =>
          have : tightLoopDef.findBlock? (.name "entry") ≠ none := by decide +kernel
          exact absurd hfind this
  · llvm_wf [loopWithAddDef] at hargs

end LeanNanoLlvm.Refinement
