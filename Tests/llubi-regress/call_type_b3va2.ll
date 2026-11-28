; difftest (phase 2), B3: a call's function type is its explicit type, or the non-variadic type of its arguments; it must equal the callee's (a variadic callee called without an explicit variadic type is UB). Variadic arguments are printed on entry (vaarg[i]).

define i32 @g(i32 %x, ...) {
  ret i32 %x
}
define i32 @main() {
  %r = call i32 @g(i32 7, i32 2)
  ret i32 %r
}
