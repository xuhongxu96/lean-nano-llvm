; EXPECT_EXIT: 0
; EXPECT_OUT: i32 22

declare i32 @llvm.vector.reduce.add.v4i32(<4 x i32>)
declare <4 x i32> @llvm.stepvector.v4i32()
declare <4 x i32> @llvm.vector.reverse.v4i32(<4 x i32>)
declare <4 x i1> @llvm.mask.beforefirst.v4i1(<4 x i1>)
declare void @llvm.masked.store.v4i32.p0(<4 x i32>, ptr, <4 x i1>)
declare <4 x i32> @llvm.masked.load.v4i32.p0(ptr, <4 x i1>, <4 x i32>)

define i32 @main() {
entry:
  %buf = alloca [4 x i32], align 16
  %sv = call <4 x i32> @llvm.stepvector.v4i32()
  %rev = call <4 x i32> @llvm.vector.reverse.v4i32(<4 x i32> %sv)
  ; rev = <3, 2, 1, 0>, sum = 6
  %s1 = call i32 @llvm.vector.reduce.add.v4i32(<4 x i32> %rev)

  ; store <5, 7, 99, 99> with mask <T, T, F, F> (beforefirst of <F, F, T, F>)
  %m = call <4 x i1> @llvm.mask.beforefirst.v4i1(<4 x i1> <i1 false, i1 false, i1 true, i1 false>)
  call void @llvm.masked.store.v4i32.p0(<4 x i32> <i32 5, i32 7, i32 99, i32 99>, ptr align 4 %buf, <4 x i1> %m)
  %ld = call <4 x i32> @llvm.masked.load.v4i32.p0(ptr align 4 %buf, <4 x i1> %m, <4 x i32> <i32 0, i32 0, i32 2, i32 2>)
  ; ld = <5, 7, 2, 2>, sum = 16
  %s2 = call i32 @llvm.vector.reduce.add.v4i32(<4 x i32> %ld)

  %tot = add i32 %s1, %s2
  ret i32 %tot
}
