import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import LeanNanoLlvm.AST.Unexpander
import Tests.Refinement.Helpers
import Tests.Refinement.Basic

/-! Refinement tests: caller-memory store-to-load forwarding and dead `alloca` elimination. -/

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

/-! ### Arbitrary Caller-Memory Store-to-Load Forwarding & Dead `alloca` Elimination -/

private theorem typeAllocSize_i8 :
    AST.DataLayout.default64LE.typeAllocSize (.int 8) = 1 := by decide

theorem typeStoreSize_i8 :
    AST.DataLayout.default64LE.typeStoreSize (.int 8) = 1 := by decide

private theorem alloc_i8_steps_ok {initMem : MemoryState} (hwf : MemoryState.WellFormed initMem)
    {name : String} {obj : MemoryObject} {mem1 : MemoryState}
    (halloc : initMem.allocate .default64LE .modern 1 1 name 0 .uninitialized .stack false = .ok (obj, mem1)) :
    let ptr := MemoryState.derivePointer .default64LE obj
    MemoryState.AllocSpec initMem .default64LE .modern 1 1 name 0 .uninitialized .stack false obj mem1 ∧
    obj.allocId = initMem.nextAllocId ∧
    mem1.verifyMemAccess ptr 1 1 true = .ok (obj, 0) ∧
    (∀ b : MemByte,
      let mem2 := mem1.writeObjectBytes obj.allocId 0 #[b]
      let obj' := { obj with bytes := #[b] }
      mem2.verifyMemAccess ptr 1 1 false = .ok (obj', 0) ∧
      MemoryState.readObjectBytes obj' 0 1 = #[b]) ∧
    (∀ id ∈ initMem.allocIds, mem1.objects.get? id = initMem.objects.get? id) := by
  have hspec := MemoryState.allocate_satisfies_AllocSpec hwf halloc
  have hidEq : obj.allocId = initMem.nextAllocId := hspec.id_eq
  have haddrLt : obj.baseAddr < 2 ^ 64 := by
    have hs := hspec.addr_in_space
    change obj.baseAddr + max 1 1 < 1 <<< 64 at hs
    omega
  have hptrAddr : (MemoryState.derivePointer .default64LE obj).addr.toNat = obj.baseAddr := by
    simp only [MemoryState.derivePointer, AST.DataLayout.default64LE,
               AST.DataLayout.getPointerSizeInBits, hspec.as_eq, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt haddrLt
  have hmem1Objs : mem1.objects = initMem.objects.insert obj.allocId obj := by
    rw [hspec.mem'_eq]
  have hget1 : mem1.objects.get? obj.allocId = some obj := by
    rw [hmem1Objs, AssocMap.get?_insert, beq_self_eq_true]; rfl
  have hresolve1 : mem1.resolveObject? (MemoryState.derivePointer .default64LE obj) = some obj := by
    simp only [MemoryState.resolveObject?, MemoryState.derivePointer, hget1]
  have hverStore : mem1.verifyMemAccess (MemoryState.derivePointer .default64LE obj) 1 1 true = .ok (obj, 0) := by
    unfold MemoryState.verifyMemAccess
    rw [hresolve1]; dsimp only
    rw [hspec.state_eq, hspec.const_eq, hspec.size_eq, hptrAddr]
    simp [Nat.mod_one, hspec.not_mem_inaccessible]
  have hcallerEq : ∀ id ∈ initMem.allocIds, mem1.objects.get? id = initMem.objects.get? id := by
    intro id hid
    have hlt := MemoryState.allocId_lt_nextAllocId_of_mem_allocIds hwf hid
    have hne : obj.allocId ≠ id := by rw [hidEq]; exact Nat.ne_of_gt hlt
    rw [hmem1Objs, AssocMap.get?_insert, beq_false_of_ne hne]; rfl
  refine ⟨hspec, hidEq, hverStore, ?_, hcallerEq⟩
  intro b
  have hwf1 : MemoryState.WellFormed mem1 := MemoryState.allocate_preserves_wf hwf halloc
  have hverLoad0 : mem1.verifyMemAccess (MemoryState.derivePointer .default64LE obj) 1 1 false = .ok (obj, 0) := by
    unfold MemoryState.verifyMemAccess
    rw [hresolve1]; dsimp only
    rw [hspec.state_eq, hspec.size_eq, hptrAddr]
    simp [Nat.mod_one, hspec.not_mem_inaccessible]
  have hverLoad1 := MemoryState.verifyMemAccess_writeObjectBytes_same hwf1 hverLoad0 0 #[b]
  have hgoEq : MemoryState.writeObjectBytes.go 0 #[b] 0 #[b].size obj.bytes = #[b] := by
    rw [hspec.bytes_eq]
    rfl
  rw [hgoEq] at hverLoad1
  have hread : MemoryState.readObjectBytes { obj with bytes := #[b] } 0 1 = #[b] := by
    unfold MemoryState.readObjectBytes
    dsimp only
    rw [hspec.state_eq]
    rfl
  exact ⟨hverLoad1, hread⟩

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
    | concrete b provBit =>
      dsimp only
      cases b with
      | false => exact ih ..
      | true => by_cases hi : i < numBits <;> simp only [hi, ↓reduceIte] <;> exact ih ..

private theorem byte_roundtrip_i8 (v : IntW 8) (o : OracleState) :
    bytesToValue .default64LE .modern
      (valueToBytes .default64LE .modern (.bv 8 v) (.int 8))
      (.int 8) o = (.bv 8 v, v == .poison, o) := by
  simp only [valueToBytes, bytesToValue, writeScalarBits, readScalarBits,
             AST.DataLayout.typeStoreSize, AST.DataLayout.typeSizeInBits,
             AST.DataLayout.typeLayout, AST.DataLayout.alignTo]
  cases v using PoisonOr.casesOn' with
  | poison => rfl
  | value bv =>
    rw [readScalarBits_loop_modern_eq (o0 := { oracle := fun _ => 0 })]
    have hcheck : ∀ hi lo : Fin 16,
        let n := hi.val * 16 + lo.val
        let bs := writeBitLoop AST.DataLayout.default64LE 0
          (fun i => if i < 8 then MemBit.concrete ((BitVec.ofNat 8 n).getLsbD i) none else MemBit.concrete false none)
          0 8 (Array.replicate 1 MemByte.zero)
        let r := readScalarBits.loop AST.DataLayout.default64LE .modern bs 0 8 0 8 0 false false true none false { oracle := fun _ => 0 }
        r.1 = n ∧ r.2.1 = false ∧ r.2.2.1 = false ∧ r.2.2.2.2.2.1 = false := by
      decide +kernel
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
    refine ⟨fun hc => (by cases hc), ?_⟩
    rw [if_neg (by decide)]

theorem valueToBytes_i8_singleton (v : IntW 8) :
    ∃ b : MemByte, valueToBytes .default64LE .modern (.bv 8 v) (.int 8) = #[b] := by
  have hloop : ∀ (fn : Nat → MemBit) (i rem : Nat) (b : MemByte),
      ∃ b', writeBitLoop .default64LE 0 fn i rem #[b] = #[b'] := by
    intro fn i rem
    induction rem generalizing i with
    | zero => intro b; exact ⟨b, rfl⟩
    | succ r ih =>
      intro b
      simp only [writeBitLoop, setLogicalBit, AST.DataLayout.default64LE,
                 AST.DataLayout.isLittleEndian, beq_self_eq_true, ↓reduceIte, Nat.zero_add]
      cases i / 8 with
      | zero =>
        simp only [setLogicalBit.updateList]
        exact ih (i + 1) (b.setBit (i % 8) (fn i))
      | succ k =>
        simp only [setLogicalBit.updateList]
        exact ih (i + 1) b
  simp only [valueToBytes, writeScalarBits, AST.DataLayout.typeStoreSize,
             AST.DataLayout.typeSizeInBits, AST.DataLayout.typeLayout,
             AST.DataLayout.default64LE]
  cases v using PoisonOr.casesOn' with
  | poison => exact hloop _ 0 _ MemByte.zero
  | value bv => exact hloop _ 0 _ MemByte.zero

open scoped LeanNanoLlvm.AST.Syntax in
def allocaStoreLoadI8Def : AST.Definition := [llvm-definition|
  define i8 @f(i8 %x) {
  entry:
    %p = alloca i8, align 1
    store i8 %x, ptr %p, align 1
    %v = load i8, ptr %p, align 1
    ret i8 %v
  }
]

/--
Store-to-load forwarding verified for ALL well-formed caller memories `initMem`!
If `initMem` is out of memory, source `alloca` aborts (`CanAbort`); otherwise source
allocates a fresh stack slot, stores `%x`, loads `%x` back, frees the slot on return,
and leaves every pre-existing caller object in `initMem.allocIds` untouched.
-/
theorem ret_x_refines_alloca_store_load_i8 :
    allocaStoreLoadI8Def ⊒ retXDef 8 := by
  refine ⟨rfl, ?_⟩
  intro initMem args hwfMem hargs
  rcases args with _ | ⟨arg, _ | _⟩
  · llvm_wf [allocaStoreLoadI8Def] at hargs
  · cases arg <;>
      llvm_wf [allocaStoreLoadI8Def] at hargs
    subst hargs
    rename_i v
    rw [initCallConfig_1 .modern .default64LE initMem (retXDef 8) rfl (Or.inl rfl) rfl rfl rfl rfl]
    rw [initCallConfig_1 .modern .default64LE initMem allocaStoreLoadI8Def rfl (Or.inl rfl) rfl rfl rfl rfl]
    cases halloc : initMem.allocate .default64LE .modern 1 1 "p" 0 .uninitialized .stack false with
    | error err =>
      left
      rcases MemoryState.allocate_error_cases halloc with ⟨rfl, hoom⟩ | ⟨msg, rfl, hsz⟩
      · right
        refine ⟨[], .outOfMemory, StarStep.step (ev := none) ?_ (StarStep.refl _)⟩
        exact Step.instr rfl rfl
          (StepInstr.alloca_oom (count := 1) ⟨rfl, rfl⟩ (by simpa [typeAllocSize_i8] using hoom))
      · exact absurd hsz (by decide +kernel)
    | ok pair =>
      obtain ⟨obj, mem1⟩ := pair
      obtain ⟨hspec, hidEq, hverStore, hreadAfterWrite, hcallerEq⟩ := alloc_i8_steps_ok hwfMem halloc
      obtain ⟨b, hb⟩ := valueToBytes_i8_singleton v
      obtain ⟨hverLoad, hreadBytes⟩ := hreadAfterWrite b
      have hpx : (AST.Identifier.local_id (.name "p") == AST.Identifier.local_id (.name "x")) = false := rfl
      have hbtv : BytesToValueRel .default64LE .modern
          (MemoryState.readObjectBytes { obj with bytes := #[b] } 0 1) (.int 8) (.bv 8 v) (v == .poison) := by
        rw [hreadBytes]
        have hrt := byte_roundtrip_i8 v default
        rw [hb] at hrt
        exact bytesToValue_satisfies_rel hrt
      let mem2 := mem1.writeObjectBytes obj.allocId 0 (valueToBytes .default64LE .modern (.bv 8 v) (.int 8))
      let memFinal := mem2.freeObject obj.allocId
      have hmemRef : MemoryState.IsRefinedBy .id initMem.allocIds memFinal initMem := by
        intro id hid
        have hlt := MemoryState.allocId_lt_nextAllocId_of_mem_allocIds hwfMem hid
        have hne : obj.allocId ≠ id := by rw [hidEq]; exact Nat.ne_of_gt hlt
        have heq : memFinal.objects.get? id = initMem.objects.get? id := by
          dsimp only [memFinal, mem2]
          rw [MemoryState.objects_get?_freeObject_ne _ _ hne,
              MemoryState.objects_get?_writeObjectBytes_ne _ _ _ _ hne,
              hcallerEq id hid]
        rw [heq]
        cases initMem.objects.get? id with
        | none => trivial
        | some mo => exact ⟨rfl, rfl, fun _ i _ => MemByte.IsRefinedBy.refl _⟩
      have hbw1 : mem1.bindWildcard (MemoryState.derivePointer .default64LE obj).prov obj.allocId = mem1 :=
        MemoryState.bindWildcard_concrete _ _ _
      have hbw2 : mem2.bindWildcard (MemoryState.derivePointer .default64LE obj).prov obj.allocId = mem2 :=
        MemoryState.bindWildcard_concrete _ _ _
      refine Config.IsRefinedBy.of_det_halted
        (det_step_to_halted fun ev c' => by
          rw [Step.ret_top_leaf_iff rfl rfl rfl rfl (v := .bv 8 v)
                (by llvm_step)]
          simp only [freeAllocaList, applyRetFMFAndAttrsPure, applyValueAttrsPure, applyValueAttrsSeq, reduceOrderValueAttrs, retXDef]
          rfl)
        (StarStep.step (ev := none)
          (Step.instr rfl rfl
            (StepInstr.alloca_ok (count := 1) ⟨rfl, rfl⟩
              (by simpa [typeAllocSize_i8, AST.RawId.toString, allocaInitKind, allocaStoreLoadI8Def] using hspec)))
          (StarStep.step (ev := none)
            (Step.instr rfl rfl
              (StepInstr.store_ok
                (EvalExp.leaf_ok (by llvm_step [hpx]; rfl))
                (EvalExp.leaf_ok (by llvm_step; exact ⟨rfl, rfl⟩))
                (by simpa [typeStoreSize_i8] using hverStore)))
            (StarStep.step (ev := none)
              (Step.instr rfl rfl
                (StepInstr.load_ok
                  (EvalExp.leaf_ok (by llvm_step; exact ⟨rfl, rfl⟩))
                  (by simpa [typeStoreSize_i8, hb, hbw1] using hverLoad)
                  (by simpa [typeStoreSize_i8] using hbtv)
                  rfl
                  (by intro h; cases h)))
              (StarStep.step (ev := none)
                (Step.term rfl rfl rfl
                  (StepTerm.ret_ok rfl
                    (EvalExp.leaf_ok (by llvm_step; rfl))
                    (StepRet.top_ok rfl (by llvm_step [allocaStoreLoadI8Def]))))
                (StarStep.refl _)))))
        (RegisterValue.IsRefinedBy.refl _)
        (by simpa [hbw1, mem2, hbw2, memFinal] using hmemRef)
  · llvm_wf [allocaStoreLoadI8Def] at hargs

open scoped LeanNanoLlvm.AST.Syntax in
def deadAllocaStoreI8Def : AST.Definition := [llvm-definition|
  define i8 @f(i8 %x) {
  entry:
    %p = alloca i8, align 1
    store i8 42, ptr %p, align 1
    ret i8 %x
  }
]

/-- Dead `alloca` + dead `store` elimination verified for ALL well-formed caller memories `initMem`. -/
theorem dead_alloca_store_elim_i8 :
    deadAllocaStoreI8Def ⊒ retXDef 8 := by
  refine ⟨rfl, ?_⟩
  intro initMem args hwfMem hargs
  rcases args with _ | ⟨arg, _ | _⟩
  · llvm_wf [deadAllocaStoreI8Def] at hargs
  · cases arg <;>
      llvm_wf [deadAllocaStoreI8Def] at hargs
    subst hargs
    rename_i v
    rw [initCallConfig_1 .modern .default64LE initMem (retXDef 8) rfl (Or.inl rfl) rfl rfl rfl rfl]
    rw [initCallConfig_1 .modern .default64LE initMem deadAllocaStoreI8Def rfl (Or.inl rfl) rfl rfl rfl rfl]
    cases halloc : initMem.allocate .default64LE .modern 1 1 "p" 0 .uninitialized .stack false with
    | error err =>
      left
      rcases MemoryState.allocate_error_cases halloc with ⟨rfl, hoom⟩ | ⟨msg, rfl, hsz⟩
      · right
        refine ⟨[], .outOfMemory, StarStep.step (ev := none) ?_ (StarStep.refl _)⟩
        exact Step.instr rfl rfl
          (StepInstr.alloca_oom (count := 1) ⟨rfl, rfl⟩ (by simpa [typeAllocSize_i8] using hoom))
      · exact absurd hsz (by decide +kernel)
    | ok pair =>
      obtain ⟨obj, mem1⟩ := pair
      obtain ⟨hspec, hidEq, hverStore, _, hcallerEq⟩ := alloc_i8_steps_ok hwfMem halloc
      have hpx : (AST.Identifier.local_id (.name "p") == AST.Identifier.local_id (.name "x")) = false := rfl
      let mem2 := mem1.writeObjectBytes obj.allocId 0
        (valueToBytes .default64LE .modern (.bv 8 (.value (BitVec.ofInt 8 42))) (.int 8))
      let memFinal := mem2.freeObject obj.allocId
      have hmemRef : MemoryState.IsRefinedBy .id initMem.allocIds memFinal initMem := by
        intro id hid
        have hlt := MemoryState.allocId_lt_nextAllocId_of_mem_allocIds hwfMem hid
        have hne : obj.allocId ≠ id := by rw [hidEq]; exact Nat.ne_of_gt hlt
        have heq : memFinal.objects.get? id = initMem.objects.get? id := by
          dsimp only [memFinal, mem2]
          rw [MemoryState.objects_get?_freeObject_ne _ _ hne,
              MemoryState.objects_get?_writeObjectBytes_ne _ _ _ _ hne,
              hcallerEq id hid]
        rw [heq]
        cases initMem.objects.get? id with
        | none => trivial
        | some mo => exact ⟨rfl, rfl, fun _ i _ => MemByte.IsRefinedBy.refl _⟩
      refine Config.IsRefinedBy.of_det_halted
        (det_step_to_halted fun ev c' => by
          rw [Step.ret_top_leaf_iff rfl rfl rfl rfl (v := .bv 8 v)
                (by llvm_step)]
          simp only [freeAllocaList, applyRetFMFAndAttrsPure, applyValueAttrsPure, applyValueAttrsSeq, reduceOrderValueAttrs, retXDef]
          rfl)
        (StarStep.step (ev := none)
          (Step.instr rfl rfl
            (StepInstr.alloca_ok (count := 1) ⟨rfl, rfl⟩
              (by simpa [typeAllocSize_i8, AST.RawId.toString, allocaInitKind, deadAllocaStoreI8Def] using hspec)))
          (StarStep.step (ev := none)
            (Step.instr rfl rfl
              (StepInstr.store_ok
                (EvalExp.leaf_ok (by simp [evalPureLeafExp?]; rfl))
                (EvalExp.leaf_ok (by llvm_step; exact ⟨rfl, rfl⟩))
                (by simpa [typeStoreSize_i8] using hverStore)))
            (StarStep.step (ev := none)
              (Step.term rfl rfl rfl
                (StepTerm.ret_ok rfl
                  (EvalExp.leaf_ok (by llvm_step [hpx]; rfl))
                  (StepRet.top_ok rfl (by llvm_step [deadAllocaStoreI8Def]))))
              (StarStep.refl _))))
        (RegisterValue.IsRefinedBy.refl _)
        (by simpa [MemoryState.derivePointer] using hmemRef)
  · llvm_wf [deadAllocaStoreI8Def] at hargs

end LeanNanoLlvm.Refinement
