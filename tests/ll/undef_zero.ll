; ARGS: --zero-undef
; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i32 7

define i32 @main() {
entry:
  %u = add i32 undef, 7
  ret i32 %u
}
