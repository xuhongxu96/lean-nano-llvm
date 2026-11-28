;
; difftest (phase 2), output of `lean-nano-llvm llubi --verbose` against the pinned llubi
; (golden `alloca_addrspace_spacing.expected`): `alloca ..., addrspace(1)` is printed without spaces inside the parentheses.

target datalayout = "A1"
define i32 @main() {
  %a = alloca i32, align 4, addrspace(1)
  ret i32 0
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 0
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   %a = alloca i32, align 4, addrspace(1) => ptr 0x8 [a]
; LLUBI-ERR:   ret i32 0
; LLUBI-ERR: Exiting function: main
