import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import LeanNanoLlvm.AST.Unexpander
import Tests.Refinement.Helpers
import Tests.Refinement.MemoryForwarding

/-! Refinement tests: caller-visible memory refinement (positive and negative). -/

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

/-! ### Caller-Visible Memory Refinement (Positive & Negative Tests) -/

open scoped LeanNanoLlvm.AST.Syntax in
def singleStoreCallerDef : AST.Definition := [llvm-definition|
  define void @f(ptr %p, i8 %v) {
  entry:
    store i8 %v, ptr %p, align 1
    ret void
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
def doubleStoreCallerDef : AST.Definition := [llvm-definition|
  define void @f(ptr %p, i8 %v) {
  entry:
    store i8 1, ptr %p, align 1
    store i8 %v, ptr %p, align 1
    ret void
  }
]

/--
Dead-store elimination on a caller-passed pointer `ptr %p` (arbitrary well-formed `initMem`):
eliminating the overwritten `store i8 1, ptr %p` preserves caller-visible memory identically,
and whenever `%p` is invalid/poison/readonly/OOB, source immediately triggers UB (`CanAbort`).
-/
theorem dead_store_elim_caller_mem_i8 :
    doubleStoreCallerDef ⊒ singleStoreCallerDef := by
  refine ⟨rfl, ?_⟩
  intro initMem args hwfMem hargs
  rcases args with _ | ⟨pArg, _ | ⟨vArg, _ | _⟩⟩
  · llvm_wf [doubleStoreCallerDef] at hargs
  · llvm_wf [doubleStoreCallerDef] at hargs
  · cases pArg <;> cases vArg <;>
      llvm_wf [doubleStoreCallerDef] at hargs
    rcases hargs with ⟨rfl, rfl⟩
    rename_i pv vv
    have hvp : (AST.Identifier.local_id (.name "v") == AST.Identifier.local_id (.name "p")) = false := rfl
    rw [initCallConfig_2 .modern .default64LE initMem singleStoreCallerDef
          rfl (Or.inl rfl) rfl rfl rfl rfl rfl]
    rw [initCallConfig_2 .modern .default64LE initMem doubleStoreCallerDef
          rfl (Or.inl rfl) rfl rfl rfl rfl rfl]
    cases pv using PoisonOr.casesOn' with
    | poison =>
      left; left
      refine ⟨[], "Invalid memory access with a poison pointer.", StarStep.step (ev := none) ?_ (StarStep.refl _)⟩
      apply Step.instr rfl rfl
      exact StepInstr.store_ptr_poison
        (EvalExp.leaf_ok (by simp [evalPureLeafExp?]; rfl))
        (EvalExp.leaf_ok (by llvm_step [hvp]; rfl))
    | value ptr =>
      cases hver : initMem.verifyMemAccess ptr 1 1 true with
      | error err =>
        obtain ⟨msg, rfl⟩ := MemoryState.verifyMemAccess_error_is_ub hver
        left; left
        refine ⟨[], msg, StarStep.step (ev := none) ?_ (StarStep.refl _)⟩
        refine Step.instr rfl rfl ?_
        exact StepInstr.store_mem_err (err := .immediateUB msg)
          (EvalExp.leaf_ok (by simp [evalPureLeafExp?]; rfl))
          (EvalExp.leaf_ok (by llvm_step [hvp]; exact ⟨rfl, rfl⟩))
          (by simpa [typeStoreSize_i8] using hver)
      | ok pair =>
        obtain ⟨mo, offset⟩ := pair
        obtain ⟨b1, hb1⟩ := valueToBytes_i8_singleton (.value (1#8))
        obtain ⟨b2, hb2⟩ := valueToBytes_i8_singleton vv
        have hver1 := MemoryState.verifyMemAccess_bindWildcard_same hwfMem hver
        have hwfB := MemoryState.bindWildcard_preserves_wf hwfMem ptr.prov mo.allocId
        have hver2 := MemoryState.verifyMemAccess_writeObjectBytes_same hwfB hver1 offset #[b1]
        have hmemEq :
            ((((initMem.bindWildcard ptr.prov mo.allocId).writeObjectBytes mo.allocId offset
                (valueToBytes .default64LE .modern (.bv 8 (.value (1#8))) (.int 8))).bindWildcard
              ptr.prov mo.allocId).writeObjectBytes
              mo.allocId offset (valueToBytes .default64LE .modern (.bv 8 vv) (.int 8))) =
            (initMem.bindWildcard ptr.prov mo.allocId).writeObjectBytes mo.allocId offset
              (valueToBytes .default64LE .modern (.bv 8 vv) (.int 8)) := by
          rw [MemoryState.bindWildcard_writeObjectBytes_comm, MemoryState.bindWildcard_idemp, hb1, hb2]
          exact MemoryState.writeObjectBytes_overwrite_singleton (initMem.bindWildcard ptr.prov mo.allocId) mo.allocId offset b1 b2
        refine Config.IsRefinedBy.of_det_halted
          (det_step_chain
            (fun ev c' => by
              rw [Step.store_leaf_iff rfl rfl
                    (val := .bv 8 vv) (as := 0) (p := ptr)
                    (by llvm_step)
                    (by llvm_step [hvp])]
              simp only [typeStoreSize_i8, Option.getD, hver, ↓reduceIte, Bool.false_eq_true]
              rfl)
            (det_step_to_halted fun ev c' => by
              rw [Step.retVoid_top_iff rfl rfl rfl rfl]))
          (StarStep.step (ev := none)
            (Step.instr rfl rfl
              (StepInstr.store_ok
                (EvalExp.leaf_ok (by simp [evalPureLeafExp?]; rfl))
                (EvalExp.leaf_ok (by llvm_step [hvp]; exact ⟨rfl, rfl⟩))
                (by simpa [typeStoreSize_i8] using hver)))
            (StarStep.step (ev := none)
              (Step.instr rfl rfl
                (StepInstr.store_ok
                  (EvalExp.leaf_ok (by llvm_step; rfl))
                  (EvalExp.leaf_ok (by llvm_step [hvp]; exact ⟨rfl, rfl⟩))
                  (by simpa [typeStoreSize_i8, hb1] using hver2)))
              (StarStep.step (ev := none)
                (Step.term rfl rfl rfl (StepTerm.retVoid_ok rfl (StepRet.top_ok rfl rfl)))
                (StarStep.refl _))))
          (RegisterValue.IsRefinedBy.refl _)
          (by dsimp only [MachineState.withFramesAndMemory, CallFrame.advance, freeAllocaList]; rw [hmemEq]; exact MemoryState.IsRefinedBy.refl _ _)
  · llvm_wf [doubleStoreCallerDef] at hargs

private def callerObj1 : MemoryObject :=
  { allocId := 1, baseAddr := 8, size := 1, align := 1, addrSpace := 0, name := "caller",
    state := .alive, allocKind := .stack, isConstant := false, bytes := #[MemByte.zero] }

private def callerMem1 : MemoryState :=
  { nextAllocId := 2, nextAddr := 10, usedMem := 1,
    objects := (∅ : AssocMap AllocId MemoryObject).insert 1 callerObj1 }

private theorem callerMem1_wf : MemoryState.WellFormed callerMem1 := by
  refine ⟨by decide, by decide, ?_⟩
  intro id mo hget
  simp only [callerMem1, AssocMap.get?_insert, AssocMap.get?_empty] at hget
  by_cases h1 : (1 == id) = true
  · rw [if_pos h1] at hget
    cases hget
    have hid : id = 1 := (eq_of_beq h1).symm
    subst hid
    exact ⟨rfl, by decide, by decide, by decide⟩
  · rw [if_neg h1] at hget; cases hget

open scoped LeanNanoLlvm.AST.Syntax in
def bogusStoreCallerDef : AST.Definition := [llvm-definition|
  define void @f(ptr %p) {
  entry:
    store i8 42, ptr %p, align 1
    ret void
  }
]

open scoped LeanNanoLlvm.AST.Syntax in
def nopCallerDef : AST.Definition := [llvm-definition|
  define void @f(ptr %p) {
  entry:
    ret void
  }
]

/--
Negative test for caller-visible memory refinement:
a target that performs a spurious `store i8 42, ptr %p` does NOT refine a no-op `ret void`,
because `MemoryState.IsRefinedBy` rejects the corrupted caller byte (`42 ≠ 0`).
-/
theorem bogus_store_to_caller_mem_not_refines_nop :
    ¬ (nopCallerDef ⊒ bogusStoreCallerDef) := by
  rintro ⟨_, hbeh⟩
  let ptr1 : Pointer := { prov := .concrete 1, addrWidth := 64, addr := 8#64 }
  have hinst := hbeh callerMem1 [.ptr 0 (.value ptr1)] callerMem1_wf
    (by simp [Semantics.Definition.ArgValuesWellFormed, Semantics.RegisterValue.WellFormedForList,
              Semantics.RegisterValue.WellFormedFor, nopCallerDef])
  rw [initCallConfig_1 .modern .default64LE callerMem1 nopCallerDef rfl (Or.inl rfl) rfl rfl rfl rfl] at hinst
  rw [initCallConfig_1 .modern .default64LE callerMem1 bogusStoreCallerDef rfl (Or.inl rfl) rfl rfl rfl rfl] at hinst
  have hXstep : ∀ ev c',
      Step (.running {
        frames := [{ defn := nopCallerDef, curBlock := .name "entry", remainingCode := [],
                     terminator := entryTerm nopCallerDef,
                     registers := (∅ : AssocMap AST.Identifier RegisterValue).insert
                       (.local_id (.name "p")) (.ptr 0 (.value ptr1)) }]
        memory := callerMem1, config := .modern, dataLayout := .default64LE }) ev c' ↔
      ev = none ∧ c' = .halted .void callerMem1 := by
    intro ev c'
    rw [Step.retVoid_top_iff rfl rfl rfl rfl]
    simp only [freeAllocaList]
  have hX := det_step_to_halted hXstep
  rcases hinst with habortX | ⟨_, hterm, _⟩
  · exact hX.1 habortX
  · have hver : callerMem1.verifyMemAccess ptr1 1 1 true = .ok (callerObj1, 0) := by
      unfold MemoryState.verifyMemAccess
      simp [callerMem1, callerObj1, ptr1, MemoryState.resolveObject?, AssocMap.get?_insert]
    let memY := callerMem1.writeObjectBytes 1 0
      (valueToBytes .default64LE .modern (.bv 8 (.value (BitVec.ofInt 8 42))) (.int 8))
    obtain ⟨trX, retX, memX, inj, _, hTermX, _, _, hmemRef⟩ :=
      hterm [] .void memY
        (StarStep.step (ev := none)
          (Step.instr rfl rfl
            (StepInstr.store_ok
              (EvalExp.leaf_ok (by simp [evalPureLeafExp?]; rfl))
              (EvalExp.leaf_ok (by llvm_step; exact ⟨rfl, rfl⟩))
              (by simpa [typeStoreSize_i8] using hver)))
          (StarStep.step (ev := none)
            (Step.term rfl rfl rfl (StepTerm.retVoid_ok rfl (StepRet.top_ok rfl rfl)))
            (StarStep.refl _)))
    obtain ⟨rfl, rfl, hmemEq⟩ := hX.2.2 _ _ _ hTermX
    rw [hmemEq] at hmemRef
    have hid1 : (1 : AllocId) ∈ callerMem1.allocIds := by decide +kernel
    have hobj := hmemRef 1 hid1
    let obj42 : MemoryObject :=
      { callerObj1 with bytes := valueToBytes .default64LE .modern (.bv 8 (.value (BitVec.ofInt 8 42))) (.int 8) }
    have hgetY : memY.objects.get? 1 = some obj42 := by decide +kernel
    have hgetX : callerMem1.objects.get? 1 = some callerObj1 := rfl
    rw [hgetY, hgetX] at hobj
    obtain ⟨_, _, hbytes⟩ := hobj
    have hbyte0 := hbytes (by decide) 0 (by decide)
    have hbit1 := hbyte0 1 (by decide)
    have hbitY : (obj42.bytes.getD 0 MemByte.poison).getBit 1 = MemBit.concrete true none := by
      decide +kernel
    have hbitX : (callerObj1.bytes.getD 0 MemByte.poison).getBit 1 = MemBit.concrete false none := by
      decide +kernel
    rw [hbitY, hbitX] at hbit1
    exact Bool.noConfusion hbit1.1

end LeanNanoLlvm.Refinement
