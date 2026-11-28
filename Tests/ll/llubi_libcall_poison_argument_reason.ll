;
; difftest (phase 2), output of `lean-nano-llvm llubi --verbose` against the pinned llubi
; (golden `libcall_poison_argument_reason.expected`): a poison argument of a library call (`memset`) is reported as "Poison argument passed to a library call at argument index N.".

target datalayout = "p:32:32"
declare ptr @memset(ptr, i32, i32)
define i32 @main() {
  %a = alloca [4 x i8]
  %r = call ptr @memset(ptr %a, i32 0, i32 poison)
  ret i32 0
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   %a = alloca [4 x i8], align 1 => ptr 0x8 [a]
; LLUBI-ERR: Stacktrace:
; LLUBI-ERR: #0   %r = call ptr @memset(ptr %a, i32 0, i32 poison) at @main <stdin>:9
; LLUBI-ERR: Immediate UB detected: Poison argument passed to a library call at argument index 2.
; LLUBI-ERR: error: Execution of function 'main' failed.
