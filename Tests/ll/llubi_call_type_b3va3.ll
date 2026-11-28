; difftest (phase 2), B3: a call's function type is its explicit type, or the non-variadic type of its arguments; it must equal the callee's (a variadic callee called without an explicit variadic type is UB). Variadic arguments are printed on entry (vaarg[i]).

define i32 @g(i32 %x, ...) {
  ret i32 %x
}
define i32 @main() {
  %r = call i32 (i32, ...) @g(i32 7, i32 2)
  ret i32 %r
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 7
; LLUBI-ERR: Entering function: main
; LLUBI-ERR: Entering function: g
; LLUBI-ERR:   i32 %x = i32 7
; LLUBI-ERR:   vaarg[0] = i32 2
; LLUBI-ERR:   ret i32 %x
; LLUBI-ERR: Exiting function: g
; LLUBI-ERR:   %r = call i32 (i32, ...) @g(i32 7, i32 2) => i32 7
; LLUBI-ERR:   ret i32 %r
; LLUBI-ERR: Exiting function: main
