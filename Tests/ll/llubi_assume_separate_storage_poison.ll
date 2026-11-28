; difftest: an assume bundle on a pointer (separate_storage) with a poison pointer is UB, as in
; llubi ("Assume on poison pointer."). From case 05ed3e95eda581be.

define i32 @main() {
  %a = alloca i8
  call void @llvm.assume(i1 true) [ "separate_storage"(ptr poison, ptr %a) ]
  ret i32 0
}
declare void @llvm.assume(i1)

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   %a = alloca i8, align 1 => ptr 0x8 [a]
; LLUBI-ERR: Stacktrace:
; LLUBI-ERR: #0   call void @llvm.assume(i1 true) [ "separate_storage"(ptr poison, ptr %a) ] at @main <stdin>:6
; LLUBI-ERR: Immediate UB detected: Assume on poison pointer.
; LLUBI-ERR: error: Execution of function 'main' failed.
