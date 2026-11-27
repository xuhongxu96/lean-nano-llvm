; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i32 38

declare float @llvm.ceil.f32(float)
declare float @llvm.floor.f32(float)
declare float @llvm.trunc.f32(float)
declare float @llvm.round.f32(float)
declare float @llvm.roundeven.f32(float)
declare float @llvm.sqrt.f32(float)
declare float @llvm.ldexp.f32.i32(float, i32)
declare float @llvm.vector.reduce.fadd.v4f32(float, <4 x float>)
declare float @llvm.vector.reduce.fmaximum.v4f32(<4 x float>)

define i32 @main() {
entry:
  %c = call float @llvm.ceil.f32(float 1.25)
  %f = call float @llvm.floor.f32(float -1.25)
  %t = call float @llvm.trunc.f32(float -1.75)
  %r1 = call float @llvm.round.f32(float 2.5)
  %r2 = call float @llvm.roundeven.f32(float 2.5)
  %s = call float @llvm.sqrt.f32(float 9.0)
  %l = call float @llvm.ldexp.f32.i32(float 1.5, i32 2)
  ; c=2, f=-2, t=-1, r1=3, r2=2, s=3, l=6 => 13
  %s1 = fadd float %c, %f
  %s2 = fadd float %s1, %t
  %s3 = fadd float %s2, %r1
  %s4 = fadd float %s3, %r2
  %s5 = fadd float %s4, %s
  %s6 = fadd float %s5, %l
  %v0 = insertelement <4 x float> zeroinitializer, float 1.0, i32 0
  %v1 = insertelement <4 x float> %v0, float 2.0, i32 1
  %v2 = insertelement <4 x float> %v1, float 3.0, i32 2
  %v3 = insertelement <4 x float> %v2, float 4.0, i32 3
  ; sum = 10 + 1 + 2 + 3 + 4 = 20, max = 4 => 24; 13 + 24 + 1 = 38
  %sum = call float @llvm.vector.reduce.fadd.v4f32(float 10.0, <4 x float> %v3)
  %mx = call float @llvm.vector.reduce.fmaximum.v4f32(<4 x float> %v3)
  %tot1 = fadd float %s6, %sum
  %tot2 = fadd float %tot1, %mx
  %tot3 = fadd float %tot2, 1.0
  %res = fptosi float %tot3 to i32
  ret i32 %res
}
