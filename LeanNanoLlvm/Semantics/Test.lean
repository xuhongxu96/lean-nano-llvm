import LeanNanoLlvm.AST
import LeanNanoLlvm.Tactic
import LeanNanoLlvm.Semantics

open LeanNanoLlvm
open AST.Syntax
open Semantics

section

open scoped LeanNanoLlvm.AST.Syntax

/-! ### Helper Runners -/

def runCodeToMsg {φ : Nat} (c : @AST.Code φ) (resKey : AST.Identifier) : String :=
  match runNanoLlvmStateMWithState (evalNanoLlvmCode c) with
  | .ok ((_, st), _) => s!"ok: {st.registers.get? resKey}"
  | .error e => s!"error: {e}"

#eval runCodeToMsg [llvm-code|
  %1 = add i8 1, 2
  %2 = mul i8 %1, 8
] [llvm-identifier| %2]

@[simp]
def runDefinitionRet {φ : Nat} (d : @AST.Definition φ) (args : List RegisterValue)
    (st : NanoLlvmState := default) (u : UndefState := default) : Except ExecError RegisterValue :=
  runNanoLlvmStateM (evalNanoLlvmDefinition d args) st u

def isImmediateUB {α : Type} : Except ExecError α → Bool
  | .error (.immediateUB _) => true
  | _ => false

def isStaticError {α : Type} : Except ExecError α → Bool
  | .error (.staticError _) => true
  | _ => false

/-! ### 1. Core Integer Arithmetic, Poison, Freeze & Well-Formedness -/

theorem add_two_i32 : ∀ (a b : ℤ),
  (do
    let ((_, st), _) ← runNanoLlvmStateMWithState (evalNanoLlvmCode (
      [llvm-code| %1 = add i32 <a:int>, <b:int>]
    ))
    pure (match st.registers.get? [llvm-identifier| %1] with
      | some (.bv 32 v) => some v
      | _ => none)
  ) = .ok (some (.value ((a : BitVec 32) + (b : BitVec 32)))) := by
  intros
  simp [simp_llvm]
  rfl

theorem add_two_i32_then_trunc_to_i8 : ∀ (a b : ℤ),
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

theorem freeze_of_poison_returns_zero_legacy_compat :
  (do
    let ((_, st), _) ← runNanoLlvmStateMWithState (evalNanoLlvmCode (
      [llvm-code|
        %p = add nsw i8 127, 1
        %f = freeze i8 %p
      ]
    )) { config := .legacyCompat }
    pure (match st.registers.get? [llvm-identifier| %f] with
      | some (.bv 8 v) => some v
      | _ => none)
  ) = .ok (some (.value (0 : BitVec 8))) := by
  have hov : (127#8).saddOverflow 1#8 = true := by decide
  simp [simp_llvm, simp_llvm_option, SemanticsConfig.legacyCompat, hov]
  rfl

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
    { config := .modern }
    ⟨[42], 0⟩
    = .ok (.bv 8 (.value (42 : BitVec 8))) := by
  have hov : (127#8).saddOverflow 1#8 = true := by decide
  simp [simp_llvm, simp_llvm_option, SemanticsConfig.modern, drawBitVec, hov]

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

def wfDefinition : @AST.Definition 0 :=
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

def badDefinitionDuplicateArgs : @AST.Definition 0 :=
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

def badDefinitionUnboundRet : @AST.Definition 0 :=
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
  simp [simp_llvm, simp_llvm_option, singletonWidths]

/-! ### 2. Optional `undef` Switch (`disabled` vs `nondet` vs `zero`) -/

def undefUseDef : @AST.Definition 0 :=
  [llvm-definition|
    define i8 @f() {
    entry:
      %x = add i8 undef, 1
      ret i8 %x
    }
  ]

theorem undef_rejected_when_disabled_wf : ¬ undefUseDef.WellFormed := by
  rw [AST.definition_wellFormed_iff, AST.definition_wellFormedWith_iff]
  simp [undefUseDef, simp_wellform, SemanticsConfig.modern]

theorem undef_allowed_when_enabled_wf : undefUseDef.WellFormedWith .withUndef := by
  rw [AST.definition_wellFormedWith_iff]
  refine ⟨_, _, _, ?_, rfl, rfl, by simp [undefUseDef], by simp [undefUseDef], by simp [undefUseDef], ?_⟩
  · rw [AST.declaration_wellFormed_iff]
    simp [AST.Declaration.WellFormedType, undefUseDef]
  · simp [undefUseDef, simp_wellform, SemanticsConfig.withUndef]

theorem undef_rejected_at_runtime_modern :
    isStaticError (runDefinitionRet undefUseDef [] { config := .modern }) = true := by
  native_decide

theorem undef_nondet_draws_from_oracle :
    runDefinitionRet undefUseDef [] { config := .withUndef } ⟨[41], 0⟩ =
      .ok (.bv 8 (.value (42 : BitVec 8))) := by
  native_decide

theorem undef_deterministic_returns_zero :
    runDefinitionRet undefUseDef [] { config := .deterministic } =
      .ok (.bv 8 (.value (1 : BitVec 8))) := by
  native_decide

def uninitAllocaLoadDef : @AST.Definition 0 :=
  [llvm-definition|
    define i8 @f() {
    entry:
      %p = alloca i8, align 1
      %v = load i8, ptr %p, align 1
      ret i8 %v
    }
  ]

theorem uninit_alloca_is_poison_when_undef_disabled :
    runDefinitionRet uninitAllocaLoadDef [] { config := .modern } =
      .ok (.bv 8 .poison) := by
  native_decide

/-- Bit-granular `undef` memory draws 1 bit per uninitialized bit (LSB-first `[0,1,0,1,1,0,1,0]` = `0x5A`). -/
theorem uninit_alloca_is_oracle_value_when_undef_enabled :
    runDefinitionRet uninitAllocaLoadDef [] { config := .withUndef } ⟨[0, 1, 0, 1, 1, 0, 1, 0], 0⟩ =
      .ok (.bv 8 (.value (0x5A : BitVec 8))) := by
  native_decide

/-! ### 3. Immediate UB vs Poison -/

theorem udiv_by_zero_is_immediate_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i8 @f() {
      entry:
        %r = udiv i8 10, 0
        ret i8 %r
      }
    ] []) = true := by
  native_decide

theorem sdiv_int_min_by_neg1_is_immediate_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i8 @f() {
      entry:
        %r = sdiv i8 -128, -1
        ret i8 %r
      }
    ] []) = true := by
  native_decide

theorem srem_poison_rhs_is_immediate_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i8 @f() {
      entry:
        %r = srem i8 5, poison
        ret i8 %r
      }
    ] []) = true := by
  native_decide

theorem udiv_exact_inexact_is_poison :
    runDefinitionRet [llvm-definition|
      define i8 @f() {
      entry:
        %r = udiv exact i8 5, 2
        ret i8 %r
      }
    ] [] = .ok (.bv 8 .poison) := by
  native_decide

theorem or_disjoint_overlap_is_poison :
    runDefinitionRet [llvm-definition|
      define i8 @f() {
      entry:
        %r = or disjoint i8 3, 2
        ret i8 %r
      }
    ] [] = .ok (.bv 8 .poison) := by
  native_decide

theorem br_poison_is_immediate_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        br i1 poison, label %a, label %b
      a:
        ret i32 1
      b:
        ret i32 2
      }
    ] []) = true := by
  native_decide

theorem unreachable_is_immediate_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        unreachable
      }
    ] []) = true := by
  native_decide

theorem assume_false_is_immediate_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        call void @llvm.assume(i1 false)
        ret i32 0
      }
    ] []) = true := by
  native_decide

/-! ### 4. Memory, Endianness, Struct Layout, Provenance & Heap (`llubi`-aligned) -/

def endianByte0Def : @AST.Definition 0 :=
  [llvm-definition|
    define i8 @f() {
    entry:
      %p = alloca i32, align 4
      store i32 16909060, ptr %p, align 4
      %b = load i8, ptr %p, align 1
      ret i8 %b
    }
  ]

/-- `0x01020304 = 16909060`: byte 0 is `0x04` under little-endian. -/
theorem memory_load_little_endian :
    runDefinitionRet endianByte0Def [] { dataLayout := .default64LE } =
      .ok (.bv 8 (.value (0x04 : BitVec 8))) := by
  native_decide

/-- `0x01020304 = 16909060`: byte 0 is `0x01` under big-endian. -/
theorem memory_load_big_endian :
    runDefinitionRet endianByte0Def [] { dataLayout := .default64BE } =
      .ok (.bv 8 (.value (0x01 : BitVec 8))) := by
  native_decide

/-- Mirrors `llubi/test/loadstore_le.ll`: loading `i25` with non-zero padding bits produces `poison`. -/
theorem load_non_byte_sized_nonzero_padding_is_poison :
    runDefinitionRet [llvm-definition|
      define i25 @f() {
      entry:
        %p = alloca i32, align 4
        store i32 -1, ptr %p, align 4
        %v = load i25, ptr %p, align 4
        ret i25 %v
      }
    ] [] = .ok (.bv 25 .poison) := by
  native_decide

/-- Unpacked `{ i8, i32 }` pads field 1 to offset 4; packed `<{ i8, i32 }>` places field 1 at offset 1. -/
theorem gep_unpacked_vs_packed_struct_offsets :
    runDefinitionRet [llvm-definition|
      define i64 @f() {
      entry:
        %u = alloca { i8, i32 }, align 4
        %u1 = getelementptr inbounds { i8, i32 }, ptr %u, i64 0, i32 1
        %ua = ptrtoaddr ptr %u to i64
        %u1a = ptrtoaddr ptr %u1 to i64
        %du = sub i64 %u1a, %ua
        %pk = alloca <{ i8, i32 }>, align 1
        %pk1 = getelementptr inbounds <{ i8, i32 }>, ptr %pk, i64 0, i32 1
        %pka = ptrtoaddr ptr %pk to i64
        %pk1a = ptrtoaddr ptr %pk1 to i64
        %dpk = sub i64 %pk1a, %pka
        %res = add i64 %du, %dpk
        ret i64 %res
      }
    ] [] = .ok (.bv 64 (.value (5 : BitVec 64))) := by
  native_decide

/-- `getelementptr inbounds` past object bounds yields `poison`. -/
theorem gep_inbounds_oob_is_poison :
    runDefinitionRet [llvm-definition|
      define i1 @f() {
      entry:
        %p = alloca i32, align 4
        %q = getelementptr inbounds i32, ptr %p, i64 2
        %c = icmp eq ptr %q, null
        ret i1 %c
      }
    ] [] = .ok (.bv 1 .poison) := by
  native_decide

/-- Pointer provenance survives round-trip through memory (`store ptr` / `load ptr`). -/
theorem pointer_provenance_preserved_through_memory :
    runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %x = alloca i32, align 4
        store i32 77, ptr %x, align 4
        %slot = alloca ptr, align 8
        store ptr %x, ptr %slot, align 8
        %p2 = load ptr, ptr %slot, align 8
        %v = load i32, ptr %p2, align 4
        ret i32 %v
      }
    ] [] = .ok (.bv 32 (.value (77 : BitVec 32))) := by
  native_decide

/-- Overwriting a byte of a stored pointer destroys its provenance; dereferencing causes Immediate UB. -/
theorem pointer_byte_overwrite_destroys_provenance_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %x = alloca i32, align 4
        store i32 77, ptr %x, align 4
        %slot = alloca ptr, align 8
        store ptr %x, ptr %slot, align 8
        %b0 = load i8, ptr %slot, align 1
        store i8 %b0, ptr %slot, align 1
        %bad = load ptr, ptr %slot, align 8
        %v = load i32, ptr %bad, align 4
        ret i32 %v
      }
    ] []) = true := by
  native_decide

/-- Mirrors `llubi/test/inttoptr_generation.ll`: `ptrtoaddr` does NOT expose provenance. -/
theorem ptrtoaddr_does_not_expose_provenance_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %x = alloca i32, align 4
        store i32 99, ptr %x, align 4
        %addr = ptrtoaddr ptr %x to i64
        %p = inttoptr i64 %addr to ptr
        %v = load i32, ptr %p, align 4
        ret i32 %v
      }
    ] []) = true := by
  native_decide

/-- Mirrors `llubi/test/inttoptr_generation.ll`: `ptrtoint` exposes provenance so `inttoptr` succeeds. -/
theorem ptrtoint_exposes_provenance_ok :
    runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %x = alloca i32, align 4
        store i32 99, ptr %x, align 4
        %addr = ptrtoint ptr %x to i64
        %p = inttoptr i64 %addr to ptr
        %v = load i32, ptr %p, align 4
        ret i32 %v
      }
    ] [] = .ok (.bv 32 (.value (99 : BitVec 32))) := by
  native_decide

/-- Mirrors `llubi/test/load_noundef_ub_poison.ll`: `load ..., !noundef` on poison causes Immediate UB. -/
theorem load_noundef_poison_is_immediate_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %p = alloca i32, align 4
        %v = load i32, ptr %p, align 4, !noundef
        ret i32 %v
      }
    ] []) = true := by
  native_decide

/-- Lifetime intrinsics: reading after `llvm.lifetime.end` yields `poison`; writing triggers Immediate UB. -/
theorem lifetime_end_load_is_poison :
    runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %p = alloca i32, align 4
        store i32 123, ptr %p, align 4
        call void @llvm.lifetime.end.p0(i64 4, ptr %p)
        %v = load i32, ptr %p, align 4
        ret i32 %v
      }
    ] [] = .ok (.bv 32 .poison) := by
  native_decide

theorem lifetime_end_store_is_immediate_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %p = alloca i32, align 4
        call void @llvm.lifetime.end.p0(i64 4, ptr %p)
        store i32 123, ptr %p, align 4
        ret i32 0
      }
    ] []) = true := by
  native_decide

/-- Heap `calloc` zero-initializes memory and `free` releases it cleanly. -/
theorem heap_calloc_zero_and_free_ok :
    runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %p = call ptr @calloc(i64 4, i64 4)
        %v0 = load i32, ptr %p, align 4
        store i32 55, ptr %p, align 4
        %v1 = load i32, ptr %p, align 4
        call void @free(ptr %p)
        %r = add i32 %v0, %v1
        ret i32 %r
      }
    ] [] = .ok (.bv 32 (.value (55 : BitVec 32))) := by
  native_decide

theorem heap_use_after_free_is_immediate_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %p = call ptr @malloc(i64 4)
        store i32 1, ptr %p, align 4
        call void @free(ptr %p)
        %v = load i32, ptr %p, align 4
        ret i32 %v
      }
    ] []) = true := by
  native_decide

theorem heap_double_free_is_immediate_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %p = call ptr @malloc(i64 4)
        call void @free(ptr %p)
        call void @free(ptr %p)
        ret i32 0
      }
    ] []) = true := by
  native_decide

theorem heap_free_stack_is_immediate_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %p = alloca i32, align 4
        call void @free(ptr %p)
        ret i32 0
      }
    ] []) = true := by
  native_decide

/-- `llvm.memset`, `llvm.memmove` (overlapping OK), and `llvm.memcpy` (overlapping UB). -/
theorem memset_and_memmove_overlap_ok :
    runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %buf = alloca [4 x i8], align 4
        call void @llvm.memset.p0.i64(ptr %buf, i8 7, i64 2, i1 false)
        %dst = getelementptr inbounds [4 x i8], ptr %buf, i64 0, i64 1
        call void @llvm.memmove.p0.p0.i64(ptr %dst, ptr %buf, i64 2, i1 false)
        %b2 = getelementptr inbounds [4 x i8], ptr %buf, i64 0, i64 2
        %v = load i8, ptr %b2, align 1
        %ext = zext i8 %v to i32
        ret i32 %ext
      }
    ] [] = .ok (.bv 32 (.value (7 : BitVec 32))) := by
  native_decide

theorem memcpy_overlap_is_immediate_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %buf = alloca [4 x i8], align 4
        call void @llvm.memset.p0.i64(ptr %buf, i8 1, i64 4, i1 false)
        %dst = getelementptr inbounds [4 x i8], ptr %buf, i64 0, i64 1
        call void @llvm.memcpy.p0.p0.i64(ptr %dst, ptr %buf, i64 2, i1 false)
        ret i32 0
      }
    ] []) = true := by
  native_decide

theorem null_deref_is_immediate_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %v = load i32, ptr null, align 4
        ret i32 %v
      }
    ] []) = true := by
  native_decide

theorem misaligned_load_is_immediate_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %buf = alloca [8 x i8], align 8
        %p1 = getelementptr inbounds [8 x i8], ptr %buf, i64 0, i64 1
        %v = load i32, ptr %p1, align 4
        ret i32 %v
      }
    ] []) = true := by
  native_decide

/-- Global variables: mutable global reads/writes succeed; writing to a `constant` global is Immediate UB. -/
def globalsModule : @AST.TopLevel 0 := [llvm|
  @g = global i32 40, align 4
  @c = constant i32 2, align 4

  define i32 @ok_fn() {
  entry:
    %a = load i32, ptr @g, align 4
    %b = load i32, ptr @c, align 4
    %s = add i32 %a, %b
    store i32 %s, ptr @g, align 4
    %r = load i32, ptr @g, align 4
    ret i32 %r
  }

  define i32 @write_const_ub() {
  entry:
    store i32 9, ptr @c, align 4
    ret i32 0
  }
]

theorem globals_read_write_ok :
    runModuleFunction globalsModule (.name "ok_fn") =
      .ok (.bv 32 (.value (42 : BitVec 32))) := by
  native_decide

theorem globals_write_constant_is_immediate_ub :
    isImmediateUB (runModuleFunction globalsModule (.name "write_const_ub")) = true := by
  native_decide

/-- Returning a pointer to a callee's `alloca` and dereferencing it in caller causes Immediate UB. -/
def danglingStackModule : @AST.TopLevel 0 := [llvm|
  define ptr @make_dangling() {
  entry:
    %loc = alloca i32, align 4
    store i32 5, ptr %loc, align 4
    ret ptr %loc
  }

  define i32 @main() {
  entry:
    %p = call ptr @make_dangling()
    %v = load i32, ptr %p, align 4
    ret i32 %v
  }
]

theorem dangling_stack_deref_is_immediate_ub :
    isImmediateUB (runModuleFunction danglingStackModule (.name "main")) = true := by
  native_decide

/-! ### 5. IEEE-754 Floating-Point Operations, Formats, FMF, FCmp, Casts & Intrinsics -/

/-- `1.5f + 2.25f = 3.75f` (`0x40700000`) via bitcast to `i32`. -/
theorem fp_fadd_single_exact :
    runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %r = fadd float 1.5, 2.25
        %b = bitcast float %r to i32
        ret i32 %b
      }
    ] [] = .ok (.bv 32 (.value (0x40700000 : BitVec 32))) := by
  native_decide

/-- `frem float 5.5, 2.0 = 1.5` (`0x3FC00000`). -/
theorem fp_frem_single_exact :
    runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %r = frem float 5.5, 2.0
        %b = bitcast float %r to i32
        ret i32 %b
      }
    ] [] = .ok (.bv 32 (.value (0x3FC00000 : BitVec 32))) := by
  native_decide

/-- `fneg float 0.0 = -0.0` (`0x80000000`). -/
theorem fp_fneg_zero_sign :
    runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %r = fneg float 0.0
        %b = bitcast float %r to i32
        ret i32 %b
      }
    ] [] = .ok (.bv 32 (.value (0x80000000 : BitVec 32))) := by
  native_decide

/-- `half` (`1.5 + 2.5 = 4.0` = `0x4400`) and `bfloat` (`1.0 + 2.0 = 3.0` = `0x4040`) and `fp128`. -/
theorem fp_half_and_bfloat_exact :
    runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %h = fadd half 1.5, 2.5
        %hb = bitcast half %h to i16
        %bf = fadd bfloat 1.0, 2.0
        %bfb = bitcast bfloat %bf to i16
        %h32 = zext i16 %hb to i32
        %bf32 = zext i16 %bfb to i32
        %hi = shl i32 %h32, 16
        %res = or i32 %hi, %bf32
        ret i32 %res
      }
    ] [] = .ok (.bv 32 (.value (0x44004040 : BitVec 32))) := by
  native_decide

theorem fp_fp128_and_double_exact :
    runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %q = fadd fp128 1.5, 2.5
        %d = fptrunc fp128 %q to double
        %i = fptosi double %d to i32
        ret i32 %i
      }
    ] [] = .ok (.bv 32 (.value (4 : BitVec 32))) := by
  native_decide

/-- Fast-math flags: `fadd nnan` with NaN (`0.0 / 0.0`) produces `poison`; `fadd ninf` with `+Inf` produces `poison`. -/
theorem fp_fmf_nnan_produces_poison :
    runDefinitionRet [llvm-definition|
      define float @f() {
      entry:
        %nan = fdiv float 0.0, 0.0
        %r = fadd nnan float %nan, 1.0
        ret float %r
      }
    ] [] = .ok (.float .float .poison) := by
  native_decide

theorem fp_fmf_ninf_produces_poison :
    runDefinitionRet [llvm-definition|
      define float @f() {
      entry:
        %inf = fdiv float 1.0, 0.0
        %r = fadd ninf float %inf, 1.0
        ret float %r
      }
    ] [] = .ok (.float .float .poison) := by
  native_decide

/-- `fcmp`: `-0.0 == +0.0` (`oeq` true), NaN is `uno` (true) and not `oeq` (false). -/
theorem fp_fcmp_signed_zero_and_nan :
    runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %z = fcmp oeq float -0.0, 0.0
        %nan = fdiv float 0.0, 0.0
        %u = fcmp uno float %nan, 1.0
        %eq = fcmp oeq float %nan, %nan
        %z32 = zext i1 %z to i32
        %u32 = zext i1 %u to i32
        %eq32 = zext i1 %eq to i32
        %s1 = add i32 %z32, %u32
        %s2 = add i32 %s1, %eq32
        ret i32 %s2
      }
    ] [] = .ok (.bv 32 (.value (2 : BitVec 32))) := by
  native_decide

/-- FP conversions: `sitofp`, `fptosi` truncation toward zero, OOB → `poison`, `uitofp nneg` on negative → `poison`. -/
theorem fp_conversions_and_trunc_toward_zero :
    runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %f = sitofp i32 -7 to double
        %q = fdiv double %f, 2.0
        %i = fptosi double %q to i32
        ret i32 %i
      }
    ] [] = .ok (.bv 32 (.value ((-3 : Int) : BitVec 32))) := by
  native_decide

theorem fp_fptosi_oob_is_poison :
    runDefinitionRet [llvm-definition|
      define i8 @f() {
      entry:
        %i = fptosi float 200.0 to i8
        ret i8 %i
      }
    ] [] = .ok (.bv 8 .poison) := by
  native_decide

theorem fp_uitofp_nneg_negative_is_poison :
    runDefinitionRet [llvm-definition|
      define float @f() {
      entry:
        %r = uitofp nneg i32 -1 to float
        ret float %r
      }
    ] [] = .ok (.float .float .poison) := by
  native_decide

/-- FP intrinsics: `llvm.fma`, `llvm.copysign`, `llvm.fabs`, `llvm.minimum`, `llvm.fptosi.sat`, `llvm.is.fpclass`. -/
theorem fp_intrinsics_suite :
    runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %fma = call float @llvm.fma.f32(float 2.0, float 3.0, float 4.0)
        %neg = call float @llvm.copysign.f32(float %fma, float -1.0)
        %abs = call float @llvm.fabs.f32(float %neg)
        %i1 = fptosi float %abs to i32
        %sat = call i8 @llvm.fptosi.sat.i8.f32(float 500.0)
        %i2 = sext i8 %sat to i32
        %cls = call i1 @llvm.is.fpclass.f32(float -0.0, i32 32)
        %i3 = zext i1 %cls to i32
        %s1 = add i32 %i1, %i2
        %s2 = add i32 %s1, %i3
        ret i32 %s2
      }
    ] [] = .ok (.bv 32 (.value (138 : BitVec 32))) := by
  native_decide

/-- Rounding mode test: `1.0f / 3.0f` rounds down (`0x3EAAAAAB` in RNE vs `0x3EAAAAAA` in RTZ). -/
def oneThirdDef : @AST.Definition 0 :=
  [llvm-definition|
    define i32 @f() {
    entry:
      %q = fdiv float 1.0, 3.0
      %b = bitcast float %q to i32
      ret i32 %b
    }
  ]

theorem fp_rounding_rne_vs_rtz :
    runDefinitionRet oneThirdDef [] { config := { roundingMode := .RNE } } =
      .ok (.bv 32 (.value (0x3EAAAAAB : BitVec 32))) ∧
    runDefinitionRet oneThirdDef [] { config := { roundingMode := .RTZ } } =
      .ok (.bv 32 (.value (0x3EAAAAAA : BitVec 32))) := by
  native_decide

/-! ### 6. Control Flow, Parallel `phi`, `switch`, Recursion, Indirect Calls, Aggregates & Vectors -/

/-- Parallel `phi` test via Fibonacci loop (`fib(10) = 55`). -/
def fibDef : @AST.Definition 0 :=
  [llvm-definition|
    define i32 @fib(i32 %n) {
    entry:
      br label %loop
    loop:
      %i = phi i32 [ 0, %entry ], [ %inext, %body ]
      %a = phi i32 [ 0, %entry ], [ %b, %body ]
      %b = phi i32 [ 1, %entry ], [ %sum, %body ]
      %done = icmp eq i32 %i, %n
      br i1 %done, label %exit, label %body
    body:
      %sum = add i32 %a, %b
      %inext = add i32 %i, 1
      br label %loop
    exit:
      ret i32 %a
    }
  ]

theorem cfg_loop_parallel_phi_fib10 :
    runDefinitionRet fibDef [.bv 32 (.value (10 : BitVec 32))] =
      .ok (.bv 32 (.value (55 : BitVec 32))) := by
  native_decide

/-- `switch` terminator test. -/
def switchDef : @AST.Definition 0 :=
  [llvm-definition|
    define i32 @sw(i32 %x) {
    entry:
      switch i32 %x, label %dflt [
        i32 0, label %c0
        i32 2, label %c2
      ]
    c0:
      ret i32 100
    c2:
      ret i32 200
    dflt:
      ret i32 999
    }
  ]

theorem cfg_switch_cases_and_default :
    runDefinitionRet switchDef [.bv 32 (.value (2 : BitVec 32))] = .ok (.bv 32 (.value (200 : BitVec 32))) ∧
    runDefinitionRet switchDef [.bv 32 (.value (7 : BitVec 32))] = .ok (.bv 32 (.value (999 : BitVec 32))) := by
  native_decide

/-- Recursive function call (`fact(5) = 120`) and indirect call through a function pointer. -/
def callsModule : @AST.TopLevel 0 := [llvm|
  define i32 @fact(i32 %n) {
  entry:
    %base = icmp sle i32 %n, 1
    br i1 %base, label %done, label %rec
  done:
    ret i32 1
  rec:
    %n1 = sub i32 %n, 1
    %recval = call i32 @fact(i32 %n1)
    %res = mul i32 %n, %recval
    ret i32 %res
  }

  define i32 @inc(i32 %x) {
  entry:
    %r = add i32 %x, 1
    ret i32 %r
  }

  define i32 @call_indirect(i32 %v) {
  entry:
    %slot = alloca ptr, align 8
    store ptr @inc, ptr %slot, align 8
    %fn = load ptr, ptr %slot, align 8
    %r = call i32 %fn(i32 %v)
    ret i32 %r
  }
]

theorem module_recursive_factorial_5 :
    runModuleFunction callsModule (.name "fact") [.bv 32 (.value (5 : BitVec 32))] =
      .ok (.bv 32 (.value (120 : BitVec 32))) := by
  native_decide

theorem module_indirect_function_pointer_call :
    runModuleFunction callsModule (.name "call_indirect") [.bv 32 (.value (41 : BitVec 32))] =
      .ok (.bv 32 (.value (42 : BitVec 32))) := by
  native_decide

/-- Aggregates (`insertvalue`/`extractvalue`) and vectors (`insertelement`/`extractelement`/`shufflevector`/lane-wise `add` & `select`). -/
theorem aggregates_and_vectors_eval :
    runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %s0 = insertvalue { i32, [2 x i32] } zeroinitializer, i32 10, 0
        %s1 = insertvalue { i32, [2 x i32] } %s0, i32 20, 1, 1
        %a0 = extractvalue { i32, [2 x i32] } %s1, 0
        %a1 = extractvalue { i32, [2 x i32] } %s1, 1, 1
        %v1 = add <2 x i32> <i32 1, i32 2>, <i32 3, i32 4>
        %v2 = insertelement <2 x i32> %v1, i32 100, i32 0
        %sh = shufflevector <2 x i32> %v1, <2 x i32> %v2, <2 x i32> <i32 1, i32 2>
        %sel = select <2 x i1> <i1 true, i1 false>, <2 x i32> %sh, <2 x i32> %v1
        %e0 = extractelement <2 x i32> %sel, i32 0
        %e1 = extractelement <2 x i32> %sel, i32 1
        %t1 = add i32 %a0, %a1
        %t2 = add i32 %e0, %e1
        %res = add i32 %t1, %t2
        ret i32 %res
      }
    ] [] = .ok (.bv 32 (.value (42 : BitVec 32))) := by
  native_decide

/-- Integer bit-manipulation, saturating, and overflow intrinsics. -/
theorem integer_intrinsics_suite :
    runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %a = call i32 @llvm.abs.i32(i32 -10, i1 false)
        %m = call i32 @llvm.smax.i32(i32 %a, i32 7)
        %lz = call i32 @llvm.ctlz.i32(i32 16, i1 false)
        %pop = call i32 @llvm.ctpop.i32(i32 7)
        %sat = call i8 @llvm.uadd.sat.i8(i8 200, i8 100)
        %sat32 = zext i8 %sat to i32
        %ov = call { i8, i1 } @llvm.sadd.with.overflow.i8(i8 120, i8 20)
        %ovFlag = extractvalue { i8, i1 } %ov, 1
        %ov32 = zext i1 %ovFlag to i32
        %s1 = add i32 %m, %lz
        %s2 = add i32 %s1, %pop
        %s3 = add i32 %s2, %sat32
        %s4 = add i32 %s3, %ov32
        ret i32 %s4
      }
    ] [] = .ok (.bv 32 (.value (296 : BitVec 32))) := by
  native_decide

end
