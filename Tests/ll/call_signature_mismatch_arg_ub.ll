; EXPECT_EXIT: 1
; EXPECT_ERR: UB: Indirect call through a function pointer with mismatched signature.
;
; difftest (phase 2): "If the function signature does not match the function type of the
; call, the behavior is undefined" (LangRef `call`); llubi reports immediate UB. We stop with
; a static error, which the refinement relation does not treat as UB.

define i8 @g(i8 %x) {
  ret i8 %x
}

define i32 @main() {
  %r = call i8 @g(i32 1)
  ret i32 0
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: Entering function: main
; LLUBI-ERR: Stacktrace:
; LLUBI-ERR: #0   %r = call i8 @g(i32 1) at @main <stdin>:13
; LLUBI-ERR: Immediate UB detected: Indirect call through a function pointer with mismatched signature. Expected: i8 (i32), Actual: i8 (i8)
; LLUBI-ERR: error: Execution of function 'main' failed.
