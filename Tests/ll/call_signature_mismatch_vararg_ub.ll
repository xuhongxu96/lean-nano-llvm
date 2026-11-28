; EXPECT_EXIT: 1
; EXPECT_ERR: UB: Indirect call through a function pointer with mismatched signature.
;
; difftest bug B3: without an explicit type a call's function type is the non-variadic type
; of its arguments, i32 (i32, i32), which differs from the variadic callee's i32 (i32, ...).
; Minimized from case 030a6452c37ef4c3.

define i32 @g(i32 %x, ...) {
  ret i32 %x
}
define i32 @main() {
  %r = call i32 @g(i32 7, i32 2)
  ret i32 %r
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: Entering function: main
; LLUBI-ERR: Stacktrace:
; LLUBI-ERR: #0   %r = call i32 @g(i32 7, i32 2) at @main <stdin>:12
; LLUBI-ERR: Immediate UB detected: Indirect call through a function pointer with mismatched signature. Expected: i32 (i32, i32), Actual: i32 (i32, ...)
; LLUBI-ERR: error: Execution of function 'main' failed.
