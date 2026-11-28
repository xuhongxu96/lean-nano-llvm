;
; difftest (phase 2), output of `lean-nano-llvm llubi --verbose` against the pinned llubi
; (golden `srem_overflow_operands.expected`): the signed-division-overflow UB message names `LHS` and `RHS` (also for srem).

define i32 @main() {
  %r = srem i32 -2147483648, -1
  ret i32 %r
}
