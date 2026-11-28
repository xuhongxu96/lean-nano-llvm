; difftest (phase 2), B3: a call's function type is its explicit type, or the non-variadic type of its arguments; it must equal the callee's (a variadic callee called without an explicit variadic type is UB). Variadic arguments are printed on entry (vaarg[i]).

declare void @use(i32, ...)
define i32 @main() {
  call void @use(i32 1, i32 2)
  ret i32 0
}
