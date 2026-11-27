import LeanNanoLlvm.AST
import LeanNanoLlvm.Tactic
import LeanNanoLlvm.Semantics
import Tests.Semantics.Helpers

/-! Semantics tests: FP intrinsics, vector FP reductions, load metadata, `byval`, named structs. -/

open LeanNanoLlvm
open AST.Syntax
open Semantics

section

open scoped LeanNanoLlvm.AST.Syntax

/-! ### Phase 2: IEEE-754 FP Intrinsics, Vector FP Reductions, Load Metadata, `byval`, Named Structs -/

def fpRoundingModule : AST.TopLevel := [llvm|
declare float @llvm.ceil.f32(float)
declare float @llvm.floor.f32(float)
declare float @llvm.trunc.f32(float)
declare float @llvm.round.f32(float)
declare float @llvm.roundeven.f32(float)
declare float @llvm.sqrt.f32(float)
declare float @llvm.ldexp.f32.i32(float, i32)
declare float @llvm.canonicalize.f32(float)
declare float @llvm.vector.reduce.fadd.v4f32(float, <4x float>)
declare float @llvm.vector.reduce.fmaximum.v4f32(<4x float>)

define i32 @test_fp_round() {
entry:
  %c = call float @llvm.ceil.f32(float 1.25)
  %f = call float @llvm.floor.f32(float -1.25)
  %t = call float @llvm.trunc.f32(float -1.75)
  %r1 = call float @llvm.round.f32(float 2.5)
  %r2 = call float @llvm.roundeven.f32(float 2.5)
  %s = call float @llvm.sqrt.f32(float 9.0)
  %l = call float @llvm.ldexp.f32.i32(float 1.5, i32 2)
  %k = call float @llvm.canonicalize.f32(float 1.0)
  -- c=2, f=-2, t=-1, r1=3, r2=2, s=3, l=6, k=1 => sum = 14
  %s1 = fadd float %c, %f
  %s2 = fadd float %s1, %t
  %s3 = fadd float %s2, %r1
  %s4 = fadd float %s3, %r2
  %s5 = fadd float %s4, %s
  %s6 = fadd float %s5, %l
  %s7 = fadd float %s6, %k
  %res = fptosi float %s7 to i32
  ret i32 %res
}

define i32 @test_fp_vec_reduce() {
entry:
  %v0 = insertelement <4x float> zeroinitializer, float 1.0, i32 0
  %v1 = insertelement <4x float> %v0, float 2.0, i32 1
  %v2 = insertelement <4x float> %v1, float 3.0, i32 2
  %v3 = insertelement <4x float> %v2, float 4.0, i32 3
  %sum = call float @llvm.vector.reduce.fadd.v4f32(float 10.0, <4x float> %v3)
  %mx = call float @llvm.vector.reduce.fmaximum.v4f32(<4x float> %v3)
  %tot = fadd float %sum, %mx
  %res = fptosi float %tot to i32
  ret i32 %res
}
]

theorem test_fp_round_exec :
    runModuleFunction fpRoundingModule (.name "test_fp_round") =
      .ok (.bv 32 (.value (14 : BitVec 32))) := by
  decide +kernel

theorem test_fp_vec_reduce_exec :
    runModuleFunction fpRoundingModule (.name "test_fp_vec_reduce") =
      .ok (.bv 32 (.value (24 : BitVec 32))) := by
  decide +kernel

def loadMetadataModule : AST.TopLevel := [llvm|
define i32 @load_range_ok() {
entry:
  %p = alloca i32, align 4
  store i32 5, ptr %p, align 4
  %v = load i32, ptr %p, align 4, !range(0, 10), !noundef
  ret i32 %v
}

define i32 @load_range_poison() {
entry:
  %p = alloca i32, align 4
  store i32 15, ptr %p, align 4
  %v = load i32, ptr %p, align 4, !range(0, 10)
  ret i32 %v
}

define i32 @load_range_noundef_ub() {
entry:
  %p = alloca i32, align 4
  store i32 15, ptr %p, align 4
  %v = load i32, ptr %p, align 4, !range(0, 10), !noundef
  ret i32 %v
}

define ptr @load_nonnull_poison() {
entry:
  %p = alloca ptr, align 8
  store ptr null, ptr %p, align 8
  %v = load ptr, ptr %p, align 8, !nonnull
  ret ptr %v
}
]

theorem test_load_range_ok :
    runModuleFunction loadMetadataModule (.name "load_range_ok") =
      .ok (.bv 32 (.value (5 : BitVec 32))) := by
  decide +kernel

theorem test_load_range_poison :
    runModuleFunction loadMetadataModule (.name "load_range_poison") =
      .ok (.bv 32 .poison) := by
  decide +kernel

theorem test_load_range_noundef_ub :
    (match runModuleFunction loadMetadataModule (.name "load_range_noundef_ub") with
     | .error (.immediateUB _) => true
     | _ => false) = true := by
  decide +kernel

theorem test_load_nonnull_poison :
    runModuleFunction loadMetadataModule (.name "load_nonnull_poison") =
      .ok (.ptr 0 .poison) := by
  decide +kernel

def byvalModule : AST.TopLevel := [llvm|
define i32 @mutate_copy(ptr byval(i32) align 4 %p) {
entry:
  %old = load i32, ptr %p, align 4
  store i32 99, ptr %p, align 4
  %after = load i32, ptr %p, align 4
  %sum = add i32 %old, %after
  ret i32 %sum
}

define i32 @caller_byval_isolated() {
entry:
  %x = alloca i32, align 4
  store i32 7, ptr %x, align 4
  %r = call i32 @mutate_copy(ptr byval(i32) %x)
  %orig = load i32, ptr %x, align 4
  -- r = 7 + 99 = 106, orig must still be 7 => 113
  %tot = add i32 %r, %orig
  ret i32 %tot
}

define i32 @caller_byval_poison_ub() {
entry:
  %r = call i32 @mutate_copy(ptr byval(i32) poison)
  ret i32 %r
}
]

theorem test_byval_isolated :
    runModuleFunction byvalModule (.name "caller_byval_isolated") =
      .ok (.bv 32 (.value (113 : BitVec 32))) := by
  decide +kernel

theorem test_byval_poison_ub :
    (match runModuleFunction byvalModule (.name "caller_byval_poison_ub") with
     | .error (.immediateUB _) => true
     | _ => false) = true := by
  decide +kernel

-- Under LLVM's default data layout (`i64:32:64`) the `i64` field sits at offset 4.
def namedStructModule : AST.TopLevel := [llvm|
%Pair = type { i32, i64 }
define i64 @use_pair() {
entry:
  %p = alloca %Pair, align 8
  %f0 = getelementptr inbounds %Pair, ptr %p, i64 0, i32 0
  %f1 = getelementptr inbounds %Pair, ptr %p, i64 0, i32 1
  store i32 12, ptr %f0, align 4
  store i64 30, ptr %f1, align 4
  %a = load i32, ptr %f0, align 4
  %a64 = zext i32 %a to i64
  %b = load i64, ptr %f1, align 4
  %res = add i64 %a64, %b
  ret i64 %res
}
]

theorem test_named_struct_exec :
    runModuleFunction namedStructModule (.name "use_pair") =
      .ok (.bv 64 (.value (42 : BitVec 64))) := by
  decide +kernel

end
