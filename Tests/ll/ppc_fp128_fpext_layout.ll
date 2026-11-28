; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i32 63
;
; difftest (phase 2): ppc_fp128 is a pair of doubles (LangRef "Floating-Point Types"); in its
; i128 bit pattern the high-order double occupies the low 64 bits (LLVM APInt order, used by
; our own ppc_fp128 arithmetic). fpext double 1.0 must give the double 1.0 (0x3FF0...) in bits
; 0-63, so bits 56-63 are 0x3F. Our fpext/sitofp into ppc_fp128 produce a different encoding
; (bits 56-63 are 0), e.g. 0x4058C725... (an IEEE binary128 exponent) for float 0x6C639285.
; Minimized from case 119345dd3c3ce39f (InstCombine signbit_bitcast_fpext_ppc_fp128).

define i32 @main() {
  %p = fpext double 1.0 to ppc_fp128
  %b = bitcast ppc_fp128 %p to i128
  %h = lshr i128 %b, 56
  %t = trunc i128 %h to i32
  ret i32 %t
}
