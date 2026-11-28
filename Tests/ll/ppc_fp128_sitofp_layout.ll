; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i32 63
;
; difftest (phase 2): as ppc_fp128_fpext_layout.ll, for sitofp.

define i32 @main() {
  %p = sitofp i32 1 to ppc_fp128
  %b = bitcast ppc_fp128 %p to i128
  %h = lshr i128 %b, 56
  %t = trunc i128 %h to i32
  ret i32 %t
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 63
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   %p = sitofp i32 1 to ppc_fp128 => ppc_fp128 1.000000e+00
; LLUBI-ERR:   %b = bitcast ppc_fp128 %p to i128 => i128 4607182418800017408
; LLUBI-ERR:   %h = lshr i128 %b, 56 => i128 63
; LLUBI-ERR:   %t = trunc i128 %h to i32 => i32 63
; LLUBI-ERR:   ret i32 %t
; LLUBI-ERR: Exiting function: main
