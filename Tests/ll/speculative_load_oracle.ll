; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i32 9
; Regression test: llvm.speculative.load with user-defined oracle callback function

@arr = global [6 x i32] [i32 0, i32 1, i32 2, i32 3, i32 4, i32 5]

define internal i64 @oracle(ptr %p, ptr %end) {
entry:
  %pi = ptrtoaddr ptr %p to i64
  %ei = ptrtoaddr ptr %end to i64
  %d = sub i64 %ei, %pi
  ret i64 %d
}

define i32 @main() {
entry:
  %p = getelementptr i32, ptr @arr, i64 4
  %end = getelementptr i32, ptr @arr, i64 6
  %v = call <4 x i32> (ptr, i1, ...) @llvm.speculative.load.v4i32.p0(ptr %p, i1 false, ptr @oracle, ptr %p, ptr %end)
  %e0 = extractelement <4 x i32> %v, i64 0
  %e1 = extractelement <4 x i32> %v, i64 1
  %sum = add i32 %e0, %e1
  ret i32 %sum
}
