; EXPECT_EXIT: 1
; EXPECT_ERR: UB: Indirect call through a function pointer with mismatched signature.
;
; difftest (phase 2): as call_signature_mismatch_arg_ub.ll, with an extra argument.

define i32 @g(i32 %x) {
  ret i32 %x
}

define i32 @main() {
  %r = call i32 @g(i32 1, i32 2)
  ret i32 0
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: Entering function: main
; LLUBI-ERR: Stacktrace:
; LLUBI-ERR: #0   %r = call i32 @g(i32 1, i32 2) at @main <stdin>:11
; LLUBI-ERR: Immediate UB detected: Indirect call through a function pointer with mismatched signature. Expected: i32 (i32, i32), Actual: i32 (i32)
; LLUBI-ERR: error: Execution of function 'main' failed.
