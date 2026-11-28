;
; difftest (phase 2), output of `lean-nano-llvm llubi --verbose` against the pinned llubi
; (golden `srem_overflow_operands.expected`): the signed-division-overflow UB message names `LHS` and `RHS` (also for srem).

define i32 @main() {
  %r = srem i32 -2147483648, -1
  ret i32 %r
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: Entering function: main
; LLUBI-ERR: Stacktrace:
; LLUBI-ERR: #0   %r = srem i32 -2147483648, -1 at @main <stdin>:6
; LLUBI-ERR: Immediate UB detected: Signed division overflow. LHS: -2147483648, RHS: -1
; LLUBI-ERR: error: Execution of function 'main' failed.
