import LeanNanoLlvm.AST
import LeanNanoLlvm.Tactic
import LeanNanoLlvm.Semantics
import Tests.Semantics.Helpers

/-! Semantics tests: memory, endianness, struct layout, provenance and heap. -/

open LeanNanoLlvm
open AST.Syntax
open Semantics

section

open scoped LeanNanoLlvm.AST.Syntax

/-! ### Memory, Endianness, Struct Layout, Provenance & Heap (`llubi`-aligned) -/

def endianByte0Def : AST.Definition :=
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
    runDefinitionRet endianByte0Def [] .modern .default64LE =
      .ok (.bv 8 (.value (0x04 : BitVec 8))) := by
  decide +kernel

/-- `0x01020304 = 16909060`: byte 0 is `0x01` under big-endian. -/
theorem memory_load_big_endian :
    runDefinitionRet endianByte0Def [] .modern .default64BE =
      .ok (.bv 8 (.value (0x01 : BitVec 8))) := by
  decide +kernel

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
  decide +kernel

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
  decide +kernel

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
  decide +kernel

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
  decide +kernel

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
  decide +kernel

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
  decide +kernel

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
  decide +kernel

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
  decide +kernel

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
  decide +kernel

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
  decide +kernel

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
  decide +kernel

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
  decide +kernel

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
  decide +kernel

theorem heap_free_stack_is_immediate_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %p = alloca i32, align 4
        call void @free(ptr %p)
        ret i32 0
      }
    ] []) = true := by
  decide +kernel

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
  decide +kernel

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
  decide +kernel

theorem null_deref_is_immediate_ub :
    isImmediateUB (runDefinitionRet [llvm-definition|
      define i32 @f() {
      entry:
        %v = load i32, ptr null, align 4
        ret i32 %v
      }
    ] []) = true := by
  decide +kernel

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
  decide +kernel

/-- Global variables: mutable global reads/writes succeed; writing to a `constant` global is Immediate UB. -/
def globalsModule : AST.TopLevel := [llvm|
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
  decide +kernel

theorem globals_write_constant_is_immediate_ub :
    isImmediateUB (runModuleFunction globalsModule (.name "write_const_ub")) = true := by
  decide +kernel

/-- Returning a pointer to a callee's `alloca` and dereferencing it in caller causes Immediate UB. -/
def danglingStackModule : AST.TopLevel := [llvm|
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
  decide +kernel

end
