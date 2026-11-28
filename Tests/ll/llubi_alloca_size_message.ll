;
; difftest (phase 2), output of `lean-nano-llvm llubi --verbose` against the pinned llubi
; (golden `alloca_size_message.expected`): the alloca-size UB message has no trailing `.`.

define i32 @main() {
  %a = alloca i8, i64 -3
  ret i32 0
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: Entering function: main
; LLUBI-ERR: Stacktrace:
; LLUBI-ERR: #0   %a = alloca i8, i64 -3, align 1 at @main <stdin>:6
; LLUBI-ERR: Immediate UB detected: Alloca with allocation size that exceeds the maximum object size. Size: 18446744073709551613
; LLUBI-ERR: error: Execution of function 'main' failed.
