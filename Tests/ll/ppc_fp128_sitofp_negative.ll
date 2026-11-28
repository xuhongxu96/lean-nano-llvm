; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i32 128
;
; difftest bug B8: an exact conversion to ppc_fp128 leaves a zero low double carrying the sign
; of the high double: sitofp -5 gives (-5.0, -0.0), so the top byte of the i128 is 0x80.

define i32 @main() {
  %p = sitofp i32 -5 to ppc_fp128
  %b = bitcast ppc_fp128 %p to i128
  %h = lshr i128 %b, 120
  %t = trunc i128 %h to i32
  ret i32 %t
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 128
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   %p = sitofp i32 -5 to ppc_fp128 => ppc_fp128 0x8000000000000000C014000000000000
; LLUBI-ERR:   %b = bitcast ppc_fp128 %p to i128 => i128 -170141183460469231717846616161067728896
; LLUBI-ERR:   %h = lshr i128 %b, 120 => i128 128
; LLUBI-ERR:   %t = trunc i128 %h to i32 => i32 128
; LLUBI-ERR:   ret i32 %t
; LLUBI-ERR: Exiting function: main
