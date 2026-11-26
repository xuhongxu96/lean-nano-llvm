; EXPECT_EXIT: 1
; EXPECT_ERR: UB:

!0 = !{ i32 0, i32 10 }

define i32 @main() {
entry:
  %p = alloca i32, align 4
  store i32 15, ptr %p, align 4
  %v = load i32, ptr %p, align 4, !range !0, !noundef !{}
  ret i32 %v
}
