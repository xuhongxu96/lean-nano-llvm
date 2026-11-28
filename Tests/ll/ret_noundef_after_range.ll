; EXPECT_EXIT: 1
; EXPECT_ERR: UB: The value poison violates noundef attribute.
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

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: Entering function: main
; LLUBI-ERR: Entering function: f
; LLUBI-ERR:   i8 %x = i8 5
; LLUBI-ERR:   ret i8 %x
; LLUBI-ERR: Exiting function: f
; LLUBI-ERR: Stacktrace:
; LLUBI-ERR: #0   %r = call i8 @f(i8 5) at @main <stdin>:12
; LLUBI-ERR: Immediate UB detected: The value poison violates noundef attribute.
; LLUBI-ERR: error: Execution of function 'main' failed.
