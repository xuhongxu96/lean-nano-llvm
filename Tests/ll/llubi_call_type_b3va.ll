; difftest (phase 2), B3: a call's function type is its explicit type, or the non-variadic type of its arguments; it must equal the callee's (a variadic callee called without an explicit variadic type is UB). Variadic arguments are printed on entry (vaarg[i]).

declare void @use(i32, ...)
define i32 @main() {
  call void @use(i32 1, i32 2)
  ret i32 0
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: Entering function: main
; LLUBI-ERR: Stacktrace:
; LLUBI-ERR: #0   call void @use(i32 1, i32 2) at @main <stdin>:5
; LLUBI-ERR: Immediate UB detected: Indirect call through a function pointer with mismatched signature. Expected: void (i32, i32), Actual: void (i32, ...)
; LLUBI-ERR: error: Execution of function 'main' failed.
