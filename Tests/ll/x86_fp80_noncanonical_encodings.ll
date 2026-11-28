; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i32 7
;
; difftest bug B10 (follow-up): x86_fp80 is the x87 extended format, not an IEEE interchange
; format: the integer bit is explicit, so some encodings have no IEEE counterpart. LLVM's APFloat
; (and llubi) decode an unnormal (exponent != 0, integer bit 0) and a pseudo-infinity (exponent
; 0x7FFF, integer bit 0) as NaN, and a pseudo-denormal (exponent 0, integer bit 1) as the number
; with exponent 1. Returns 1 + 2 + 4 when all three are decoded so.
; (No llubi expectations: llubi prints these NaNs with their raw non-canonical bits, which our
; 79-bit format does not keep.)

define i32 @main() {
  %unnormal = bitcast i80 302236066589675721064448 to x86_fp80
  %pinf = bitcast i80 604444463063240877801472 to x86_fp80
  %pden = bitcast i80 9223372036854775813 to x86_fp80
  %c1 = fcmp uno x86_fp80 %unnormal, %unnormal
  %c2 = fcmp uno x86_fp80 %pinf, %pinf
  %c3 = fcmp oeq x86_fp80 %pden, 0xK00018000000000000005
  %z1 = zext i1 %c1 to i32
  %z2 = zext i1 %c2 to i32
  %z3 = zext i1 %c3 to i32
  %s2 = shl i32 %z2, 1
  %s3 = shl i32 %z3, 2
  %a = or i32 %z1, %s2
  %r = or i32 %a, %s3
  ret i32 %r
}
