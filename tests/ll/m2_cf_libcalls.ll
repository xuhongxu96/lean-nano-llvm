; EXPECT_EXIT: 0
; EXPECT_OUT: i32 135

@.fmt = private unnamed_addr constant [7 x i8] c"ok:%d\0A\00"

declare i32 @printf(ptr, ...)
declare ptr @_Znwm(i64)
declare void @_ZdlPv(ptr)

define i32 @helper(i32 %x) {
entry:
  %y = add i32 %x, 100
  ret i32 %y
}

define i32 @main() {
entry:
  %buf = call ptr @_Znwm(i64 8)
  store i32 35, ptr %buf, align 4
  %v = load i32, ptr %buf, align 4
  call void @_ZdlPv(ptr %buf)
  %res = invoke i32 @helper(i32 %v) to label %ok unwind label %lpad

ok:
  %p = call i32 (ptr, ...) @printf(ptr @.fmt, i32 %res)
  %dst = select i1 true, ptr blockaddress(@main, %done), ptr blockaddress(@main, %lpad)
  indirectbr ptr %dst, [label %done, label %lpad]

lpad:
  ret i32 -1

done:
  ret i32 %res
}
