;
; difftest (phase 2), output of `lean-nano-llvm llubi --verbose` against the pinned llubi
; (golden `alloca_addrspace_spacing.expected`): `alloca ..., addrspace(1)` is printed without spaces inside the parentheses.

target datalayout = "A1"
define i32 @main() {
  %a = alloca i32, align 4, addrspace(1)
  ret i32 0
}
