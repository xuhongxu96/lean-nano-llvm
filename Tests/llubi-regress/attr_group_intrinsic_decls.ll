; difftest (phase 2), P2: intrinsic declarations carry LLVM's implicit attribute sets (smax and umin share one), which the slot tracker numbers before call-site groups.

declare void @llvm.memset.p0.i64(ptr writeonly, i8, i64, i1 immarg)
declare i32 @llvm.smax.i32(i32, i32)
declare i32 @llvm.umin.i32(i32, i32)
define i32 @g() {
  ret i32 1
}
define i32 @main() {
  %f = getelementptr i8, ptr @g, i64 0
  %a = call i32 %f() #0
  ret i32 %a
}
attributes #0 = { convergent }
