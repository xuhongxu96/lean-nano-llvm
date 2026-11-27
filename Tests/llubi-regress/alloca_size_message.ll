; XFAIL: difftest bug P12 (llubi output differs: the alloca-size UB message has no trailing `.`)
;
; difftest (phase 2), output of `lean-nano-llvm llubi --verbose` against the pinned llubi
; (golden `alloca_size_message.expected`): the alloca-size UB message has no trailing `.`.

define i32 @main() {
  %a = alloca i8, i64 -3
  ret i32 0
}
