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

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 0
; LLUBI-ERR: Entering function: main
; LLUBI-ERR: Entering function: f
; LLUBI-ERR:   bfloat %x = bfloat 9.183550e-41
; LLUBI-ERR:   %r = fpext bfloat %x to float => float 0.000000e+00
; LLUBI-ERR:   ret float %r
; LLUBI-ERR: Exiting function: f
; LLUBI-ERR:   %r = call float @f(bfloat 9.183550e-41) => float 0.000000e+00
; LLUBI-ERR:   %b = bitcast float %r to i32 => i32 0
; LLUBI-ERR:   %t = lshr i32 %b, 16 => i32 0
; LLUBI-ERR:   ret i32 %t
; LLUBI-ERR: Exiting function: main
