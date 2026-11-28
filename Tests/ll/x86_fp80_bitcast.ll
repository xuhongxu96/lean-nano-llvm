; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i32 3
; difftest bug B10: bitcast between i80 and x86_fp80 (80 bits each) was rejected as a size
; mismatch (79 bits). The pattern is 3.0 (exponent 0x4000, explicit integer bit set).
; From case 0186273033072fd2.

define i32 @main() {
  %f = bitcast i80 302245289961712575840256 to x86_fp80
  %d = fptrunc x86_fp80 %f to double
  %i = fptosi double %d to i32
  ret i32 %i
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 3
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   %f = bitcast i80 302245289961712575840256 to x86_fp80 => x86_fp80 3.000000e+00
; LLUBI-ERR:   %d = fptrunc x86_fp80 %f to double => double 3.000000e+00
; LLUBI-ERR:   %i = fptosi double %d to i32 => i32 3
; LLUBI-ERR:   ret i32 %i
; LLUBI-ERR: Exiting function: main
