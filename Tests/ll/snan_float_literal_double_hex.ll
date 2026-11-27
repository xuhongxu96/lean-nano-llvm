; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i32 0
; XFAIL: difftest bug B5 (a signaling-NaN float literal in double-hex form is quieted)
;
; difftest (phase 2): a `float` constant written in 64-bit hex denotes the double value
; converted to float exactly; for NaNs LLVM keeps the payload and the signaling bit, so
; 0xFFF3B1E500000000 is the float signaling NaN 0xFF9D8F28 (llubi prints it as such). We
; produce 0xFFDD8F28: the quiet bit (bit 22) is set. Returns that bit.
; Minimized from case 06c03a5727e3cf70.

define i32 @main() {
  %b = bitcast float 0xFFF3B1E500000000 to i32
  %s = lshr i32 %b, 22
  %q = and i32 %s, 1
  ret i32 %q
}
