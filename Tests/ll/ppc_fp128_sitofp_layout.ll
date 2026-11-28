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
