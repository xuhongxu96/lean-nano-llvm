; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i32 1
; Regression test: denormal_fpenv(positivezero|positivezero) flushing & ppc_fp128 double-double arithmetic

define i32 @main() denormal_fpenv(positivezero|positivezero) {
entry:
  %in_flush = fadd float 1.434929627468612680625899e-42, 0.0
  %out_flush = fmul float 5.421010862427522170037264e-20, 5.421010862427522170037264e-20
  %c1 = fcmp oeq float %in_flush, 0.0
  %c2 = fcmp oeq float %out_flush, 0.0
  %padd = fadd ppc_fp128 0xM3FF80000000000000000000000000000, 0xM40040000000000000000000000000000
  %pb = bitcast ppc_fp128 %padd to i128
  %lo64 = trunc i128 %pb to i64
  %c3 = icmp eq i64 %lo64, 4616189618054758400
  %a1 = and i1 %c1, %c2
  %ok = and i1 %a1, %c3
  %res = zext i1 %ok to i32
  ret i32 %res
}
