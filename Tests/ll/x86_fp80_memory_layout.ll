; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i32 4194432
;
; difftest bug B10: x86_fp80 is 80 bits in memory and for bitcast, with an explicit integer bit
; (bit 63); our 79-bit semantic format left it out and the type was 79 bits wide. 2.0 has
; exponent 0x4000, so bits 56-87 of the stored value are 0x400080 (0x80: the integer bit).

define i32 @main() {
  %p = alloca x86_fp80
  store x86_fp80 0xK40008000000000000000, ptr %p
  %b = load i80, ptr %p
  %h = lshr i80 %b, 56
  %t = trunc i80 %h to i32
  ret i32 %t
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 128
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   %p = alloca x86_fp80, align 16 => ptr 0x10 [p]
; LLUBI-ERR:   store x86_fp80 2.000000e+00, ptr %p, align 16
; LLUBI-ERR:   %b = load i80, ptr %p, align 4 => i80 302240678275694148452352
; LLUBI-ERR:   %h = lshr i80 %b, 56 => i80 4194432
; LLUBI-ERR:   %t = trunc i80 %h to i32 => i32 4194432
; LLUBI-ERR:   ret i32 %t
; LLUBI-ERR: Exiting function: main
