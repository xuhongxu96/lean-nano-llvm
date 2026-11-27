; XFAIL: difftest bug P8 (llubi output differs: the mismatched-signature UB message has no trailing `.`)
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
