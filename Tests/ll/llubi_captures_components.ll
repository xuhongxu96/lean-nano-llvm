;
; difftest (phase 2), output of `lean-nano-llvm llubi --verbose` against the pinned llubi
; (golden `captures_components.expected`): `captures(address)` is printed with its components.

declare void @ext(ptr)
define i32 @main() {
  %a = alloca i32
  call void @ext(ptr captures(address) %a)
  ret i32 0
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   %a = alloca i32, align 4 => ptr 0x8 [a]
; LLUBI-ERR: Unrecognized instruction:   call void @ext(ptr captures(address) %a)
; LLUBI-ERR: error: Execution of function 'main' failed.
