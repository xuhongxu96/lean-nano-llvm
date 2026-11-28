; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i32 0
;
; difftest (phase 2): with input mode `preservesign`, "a floating-point operation must treat
; any input denormal value as zero" (LangRef `denormal_fpenv`), so x + 0.0 is +0.0 for the
; smallest subnormal x. LLVM prints function attributes through attribute groups (`#0`), and
; our parser only reads denormal_fpenv when it is written inline, so the mode is lost.
; Minimized from case 05b86a79e6a6f83c.

define float @f(float %x) #0 {
  %r = fadd float %x, 0.0
  ret float %r
}

define i32 @main() {
  %r = call float @f(float 0x36A0000000000000)
  %b = bitcast float %r to i32
  ret i32 %b
}

attributes #0 = { denormal_fpenv(preservesign) }

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 0
; LLUBI-ERR: Entering function: main
; LLUBI-ERR: Entering function: f
; LLUBI-ERR:   float %x = float 1.401300e-45
; LLUBI-ERR:   %r = fadd float %x, 0.000000e+00 => float 0.000000e+00
; LLUBI-ERR:   ret float %r
; LLUBI-ERR: Exiting function: f
; LLUBI-ERR:   %r = call float @f(float 1.401300e-45) => float 0.000000e+00
; LLUBI-ERR:   %b = bitcast float %r to i32 => i32 0
; LLUBI-ERR:   ret i32 %b
; LLUBI-ERR: Exiting function: main
