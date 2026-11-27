; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i32 113

define i32 @mutate_byval(ptr byval(i32) align 4 %p) {
entry:
  %old = load i32, ptr %p, align 4
  store i32 99, ptr %p, align 4
  %after = load i32, ptr %p, align 4
  %sum = add i32 %old, %after
  ret i32 %sum
}

define i32 @main() {
entry:
  %x = alloca i32, align 4
  store i32 7, ptr %x, align 4
  %r = call i32 @mutate_byval(ptr byval(i32) %x)
  %orig = load i32, ptr %x, align 4
  %tot = add i32 %r, %orig
  ret i32 %tot
}
