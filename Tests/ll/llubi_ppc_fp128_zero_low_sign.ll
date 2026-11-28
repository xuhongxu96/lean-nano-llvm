; difftest bug B8 (follow-up): conversions into ppc_fp128 leave a zero low double that is -0 only for
; integer conversions of negative values (APFloat convertFromAPInt); literals and fpext give +0;
; fneg negates both halves.

define i32 @main() {
  %a = fadd ppc_fp128 -1.0, 0.0
  %b = fpext double -2.0 to ppc_fp128
  %c = sitofp i32 -3 to ppc_fp128
  %d = fpext float -4.0 to ppc_fp128
  %f = fneg ppc_fp128 0xM3FF00000000000000000000000000000
  ret i32 0
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 0
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   %a = fadd ppc_fp128 -1.000000e+00, 0.000000e+00 => ppc_fp128 -1.000000e+00
; LLUBI-ERR:   %b = fpext double -2.000000e+00 to ppc_fp128 => ppc_fp128 -2.000000e+00
; LLUBI-ERR:   %c = sitofp i32 -3 to ppc_fp128 => ppc_fp128 0x8000000000000000C008000000000000
; LLUBI-ERR:   %d = fpext float -4.000000e+00 to ppc_fp128 => ppc_fp128 -4.000000e+00
; LLUBI-ERR:   %f = fneg ppc_fp128 1.000000e+00 => ppc_fp128 0x8000000000000000BFF0000000000000
; LLUBI-ERR:   ret i32 0
; LLUBI-ERR: Exiting function: main
