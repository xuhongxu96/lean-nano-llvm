; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i32 1
;
; difftest (phase 2): `denormal_fpenv(float: preservesign)` sets the mode of 32-bit floats only
; (LangRef `denormal_fpenv`); doubles keep the default ieee|ieee, so the subnormal double input
; is kept and the low bits of the result are 1. We apply the override to double as well.

define double @f(double %x) denormal_fpenv(float: preservesign) {
  %r = fadd double %x, 0.0
  ret double %r
}

define i32 @main() {
  %r = call double @f(double 0x0000000000000001)
  %b = bitcast double %r to i64
  %t = trunc i64 %b to i32
  ret i32 %t
}
