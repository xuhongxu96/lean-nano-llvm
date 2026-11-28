; difftest (phase 2), B3: a call's function type is its explicit type, or the non-variadic type of its arguments; it must equal the callee's (a variadic callee called without an explicit variadic type is UB). Variadic arguments are printed on entry (vaarg[i]).

define i32 @g(i32 %x, ...) {
  ret i32 %x
}
define i32 @main() {
  %r = call i32 @g(i32 7, i32 2)
  ret i32 %r
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: Entering function: main
; LLUBI-ERR: Stacktrace:
; LLUBI-ERR: #0   %r = call i32 @g(i32 7, i32 2) at @main <stdin>:7
; LLUBI-ERR: Immediate UB detected: Indirect call through a function pointer with mismatched signature. Expected: i32 (i32, i32), Actual: i32 (i32, ...)
; LLUBI-ERR: error: Execution of function 'main' failed.
