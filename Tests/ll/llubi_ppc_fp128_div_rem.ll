; difftest bug B8 (follow-up): ppc_fp128 fdiv and frem are computed as APFloat does, in the 106-bit
; semPPCDoubleDoubleLegacy format, then split into a double pair; decimal literals are the
; nearest double-double (not an IEEE binary128 encoding). From case 191037cc66438eaa.

define i32 @main() {
  %a = sitofp i32 1000003 to ppc_fp128
  %b = fdiv ppc_fp128 %a, 3.0
  %c = frem ppc_fp128 %a, 7.5
  %d = frem ppc_fp128 %b, 0.1
  %e = fdiv ppc_fp128 %d, %b
  ret i32 0
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 0
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   %a = sitofp i32 1000003 to ppc_fp128 => ppc_fp128 0x0000000000000000412E848600000000
; LLUBI-ERR:   %b = fdiv ppc_fp128 %a, 3.000000e+00 => ppc_fp128 0x3DB55555555555564114585955555555
; LLUBI-ERR:   %c = frem ppc_fp128 %a, 7.500000e+00 => ppc_fp128 5.500000e+00
; LLUBI-ERR:   %d = frem ppc_fp128 %b, f0xBC5999999999999A3FB999999999999A => ppc_fp128 0x3C211111130929303FA1111111111111
; LLUBI-ERR:   %e = fdiv ppc_fp128 %d, %b => ppc_fp128 0x3B1C38C23BFE82863E7AD7ED53A9455C
; LLUBI-ERR:   ret i32 0
; LLUBI-ERR: Exiting function: main
