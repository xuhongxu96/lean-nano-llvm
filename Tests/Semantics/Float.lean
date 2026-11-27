import LeanNanoLlvm.AST
import LeanNanoLlvm.Tactic
import LeanNanoLlvm.Semantics
import Tests.Semantics.Helpers

/-! Semantics tests: IEEE-754 floating-point operations, formats, FMF, casts and intrinsics. -/

open LeanNanoLlvm
open AST.Syntax
open Semantics

section

open scoped LeanNanoLlvm.AST.Syntax

/-! ### IEEE-754 Floating-Point Operations, Formats, FMF, FCmp, Casts & Intrinsics -/

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
  decide +kernel

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
  decide +kernel

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
  decide +kernel

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
  decide +kernel

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
  decide +kernel

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
  decide +kernel

theorem fp_fmf_ninf_produces_poison :
    runDefinitionRet [llvm-definition|
      define float @f() {
      entry:
        %inf = fdiv float 1.0, 0.0
        %r = fadd ninf float %inf, 1.0
        ret float %r
      }
    ] [] = .ok (.float .float .poison) := by
  decide +kernel

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
  decide +kernel

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
  decide +kernel

theorem fp_fptosi_oob_is_poison :
    runDefinitionRet [llvm-definition|
      define i8 @f() {
      entry:
        %i = fptosi float 200.0 to i8
        ret i8 %i
      }
    ] [] = .ok (.bv 8 .poison) := by
  decide +kernel

theorem fp_uitofp_nneg_negative_is_poison :
    runDefinitionRet [llvm-definition|
      define float @f() {
      entry:
        %r = uitofp nneg i32 -1 to float
        ret float %r
      }
    ] [] = .ok (.float .float .poison) := by
  decide +kernel

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
  decide +kernel

/-- Rounding mode test: `1.0f / 3.0f` rounds down (`0x3EAAAAAB` in RNE vs `0x3EAAAAAA` in RTZ). -/
def oneThirdDef : AST.Definition :=
  [llvm-definition|
    define i32 @f() {
    entry:
      %q = fdiv float 1.0, 3.0
      %b = bitcast float %q to i32
      ret i32 %b
    }
  ]

theorem fp_rounding_rne_vs_rtz :
    runDefinitionRet oneThirdDef [] { roundingMode := .RNE } =
      .ok (.bv 32 (.value (0x3EAAAAAB : BitVec 32))) ∧
    runDefinitionRet oneThirdDef [] { roundingMode := .RTZ } =
      .ok (.bv 32 (.value (0x3EAAAAAA : BitVec 32))) := by
  decide +kernel

end
