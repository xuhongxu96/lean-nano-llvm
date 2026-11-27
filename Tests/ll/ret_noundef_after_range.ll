; EXPECT_EXIT: 1
; EXPECT_ERR: UB: The value poison violates noundef attribute.
; XFAIL: difftest bug B1 (return attributes: noundef is checked before range)
;
; difftest (phase 2): the same ordering for return attributes. The returned 5 is outside
; range [0, 2), so the return value is poison, which violates noundef.

define noundef range(i8 0, 2) i8 @f(i8 %x) {
  ret i8 %x
}

define i32 @main() {
  %r = call i8 @f(i8 5)
  ret i32 0
}
