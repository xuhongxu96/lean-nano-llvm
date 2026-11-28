;
; difftest (phase 2), output of `lean-nano-llvm llubi --verbose` against the pinned llubi
; (golden `signature_mismatch_message.expected`): the mismatched-signature UB message has no trailing `.`.

define i64 @g(i32 %x) {
  ret i64 5
}
define i32 @main() {
  %r = call i32 @g(i32 1)
  ret i32 %r
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: Entering function: main
; LLUBI-ERR: Stacktrace:
; LLUBI-ERR: #0   %r = call i32 @g(i32 1) at @main <stdin>:9
; LLUBI-ERR: Immediate UB detected: Indirect call through a function pointer with mismatched signature. Expected: i32 (i32), Actual: i64 (i32)
; LLUBI-ERR: error: Execution of function 'main' failed.
