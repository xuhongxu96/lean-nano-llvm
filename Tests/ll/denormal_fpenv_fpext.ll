; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i32 0
;
; difftest bug B4: `fpext`/`fptrunc` used the module's default config, not the function's
; denormal_fpenv: with input mode preservesign the subnormal bfloat input is treated as zero.
; Minimized from case 00c39af2b347dcde.

define float @f(bfloat %x) #0 {
  %r = fpext bfloat %x to float
  ret float %r
}
define i32 @main() {
  %r = call float @f(bfloat 0xR0001)
  %b = bitcast float %r to i32
  %t = lshr i32 %b, 16
  ret i32 %t
}
attributes #0 = { denormal_fpenv(ieee|preservesign) }
