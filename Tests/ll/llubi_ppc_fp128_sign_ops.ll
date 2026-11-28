; difftest B8 (follow-up): `llvm.fabs` and `llvm.copysign` on `ppc_fp128`: the value's sign is its high
; double's, and a sign change flips both doubles (`DoubleAPFloat::changeSign`); we treated the pair as
; one IEEE binary128 value. The constant writer prints a double-double decimal when the decimal's
; value is equal (a low double of -0.0 counts as zero). From case 6357d1590901c055.

define i32 @main() {
  %n = fneg ppc_fp128 f0x00000000000000010000000000000000
  %n2 = fneg ppc_fp128 f0x80000000000000013FF0000000000000
  %a = call ppc_fp128 @llvm.fabs.ppcf128(ppc_fp128 f0x0000000000000001BFF0000000000000)
  %a2 = call ppc_fp128 @llvm.fabs.ppcf128(ppc_fp128 f0x8000000000000001BFF0000000000000)
  %a3 = call ppc_fp128 @llvm.fabs.ppcf128(ppc_fp128 f0x80000000000000013FF0000000000000)
  %c = call ppc_fp128 @llvm.copysign.ppcf128(ppc_fp128 f0x80000000000000013FF0000000000000, ppc_fp128 f0x0000000000000000BFF0000000000000)
  %c2 = call ppc_fp128 @llvm.copysign.ppcf128(ppc_fp128 f0x80000000000000013FF0000000000000, ppc_fp128 f0x80000000000000003FF0000000000000)
  ret i32 0
}
declare ppc_fp128 @llvm.fabs.ppcf128(ppc_fp128)
declare ppc_fp128 @llvm.copysign.ppcf128(ppc_fp128, ppc_fp128)

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 0
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   %n = fneg ppc_fp128 f0x00000000000000010000000000000000 => ppc_fp128 0x80000000000000018000000000000000
; LLUBI-ERR:   %n2 = fneg ppc_fp128 f0x80000000000000013FF0000000000000 => ppc_fp128 0x0000000000000001BFF0000000000000
; LLUBI-ERR:   %a = call ppc_fp128 @llvm.fabs.ppcf128(ppc_fp128 f0x0000000000000001BFF0000000000000) => ppc_fp128 0x80000000000000013FF0000000000000
; LLUBI-ERR:   %a2 = call ppc_fp128 @llvm.fabs.ppcf128(ppc_fp128 f0x8000000000000001BFF0000000000000) => ppc_fp128 0x00000000000000013FF0000000000000
; LLUBI-ERR:   %a3 = call ppc_fp128 @llvm.fabs.ppcf128(ppc_fp128 f0x80000000000000013FF0000000000000) => ppc_fp128 0x80000000000000013FF0000000000000
; LLUBI-ERR:   %c = call ppc_fp128 @llvm.copysign.ppcf128(ppc_fp128 f0x80000000000000013FF0000000000000, ppc_fp128 -1.000000e+00) => ppc_fp128 0x0000000000000001BFF0000000000000
; LLUBI-ERR:   %c2 = call ppc_fp128 @llvm.copysign.ppcf128(ppc_fp128 f0x80000000000000013FF0000000000000, ppc_fp128 1.000000e+00) => ppc_fp128 0x80000000000000013FF0000000000000
; LLUBI-ERR:   ret i32 0
; LLUBI-ERR: Exiting function: main
