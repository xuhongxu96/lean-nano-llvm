; XFAIL: difftest bug P6 (llubi output differs: `captures(address)` is printed with its components)
;
; difftest (phase 2), output of `lean-nano-llvm llubi --verbose` against the pinned llubi
; (golden `captures_components.expected`): `captures(address)` is printed with its components.

declare void @ext(ptr)
define i32 @main() {
  %a = alloca i32
  call void @ext(ptr captures(address) %a)
  ret i32 0
}
