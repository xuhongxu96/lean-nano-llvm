;
; difftest (phase 2), output of `lean-nano-llvm llubi --verbose` against the pinned llubi
; (golden `assume_dereferenceable_signed_size.expected`): the size of a `dereferenceable` assume bundle is printed signed.

define i32 @main() {
  %a = alloca i32
  call void @llvm.assume(i1 true) [ "dereferenceable"(ptr %a, i64 -1) ]
  ret i32 0
}
declare void @llvm.assume(i1)

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   %a = alloca i32, align 4 => ptr 0x8 [a]
; LLUBI-ERR: Stacktrace:
; LLUBI-ERR: #0   call void @llvm.assume(i1 true) [ "dereferenceable"(ptr %a, i64 -1) ] at @main <stdin>:7
; LLUBI-ERR: Immediate UB detected: The pointer ptr 0x8 [a] violates dereferenceable(-1) assumption.
; LLUBI-ERR: error: Execution of function 'main' failed.
