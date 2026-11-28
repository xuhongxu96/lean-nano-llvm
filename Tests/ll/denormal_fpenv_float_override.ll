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

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: Entering function: main
; LLUBI-ERR: Entering function: f
; LLUBI-ERR:   double %x = double 4.940660e-324
; LLUBI-ERR:   %r = fadd double %x, 0.000000e+00 => double 4.940660e-324
; LLUBI-ERR:   ret double %r
; LLUBI-ERR: Exiting function: f
; LLUBI-ERR:   %r = call double @f(double 4.940660e-324) => double 4.940660e-324
; LLUBI-ERR:   %b = bitcast double %r to i64 => i64 1
; LLUBI-ERR:   %t = trunc i64 %b to i32 => i32 1
; LLUBI-ERR:   ret i32 %t
; LLUBI-ERR: Exiting function: main
