; EXPECT_EXIT: 0
; EXPECT_OUT: i32 42

target datalayout = "e-p:64:64:64-i32:32:32-i64:64:64"

declare void @llvm.assume(i1)

define i32 @check_ptr(ptr dereferenceable(4) %p) {
entry:
  call void @llvm.assume(i1 true) [ "align"(ptr %p, i64 4), "nonnull"(ptr %p) ]
  %v = load i32, ptr %p, align 4, !range !0
  ret i32 %v
}

define i32 @main() {
entry:
  %a = alloca i32, align 4
  store i32 42, ptr %a, align 4
  %r = call i32 @check_ptr(ptr %a)
  ret i32 %r
}

!0 = !{i32 0, i32 100}
