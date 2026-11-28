; `f0x<hex>` floating-point literals (the bit pattern of the type, as an APInt; for `ppc_fp128`
; the high double is the low word). The parser rejected them, so 3,859 corpus cases were
; unsupported.

define i32 @main() {
  %h = fadd half f0x3C00, f0x4000
  %b = fadd bfloat f0x3F80, f0x4000
  %f = fadd float f0x3F800000, f0x40000000
  %d = fadd double f0x3FF0000000000000, f0x4000000000000000
  %x = fadd x86_fp80 f0x3FFF8000000000000000, f0x40008000000000000000
  %q = fadd fp128 f0x3FFF0000000000000000000000000000, f0x40000000000000000000000000000000
  %p = fadd ppc_fp128 f0x00000000000000003FF0000000000000, f0x00000000000000004000000000000000
  %v = fadd <2 x float> <float f0x3F800000, float f0x7F800000>, <float f0x3F800000, float f0xFF800000>
  ret i32 0
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 0
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   %h = fadd half 1.000000e+00, 2.000000e+00 => half 3.000000e+00
; LLUBI-ERR:   %b = fadd bfloat 1.000000e+00, 2.000000e+00 => bfloat 3.000000e+00
; LLUBI-ERR:   %f = fadd float 1.000000e+00, 2.000000e+00 => float 3.000000e+00
; LLUBI-ERR:   %d = fadd double 1.000000e+00, 2.000000e+00 => double 3.000000e+00
; LLUBI-ERR:   %x = fadd x86_fp80 1.000000e+00, 2.000000e+00 => x86_fp80 3.000000e+00
; LLUBI-ERR:   %q = fadd fp128 1.000000e+00, 2.000000e+00 => fp128 3.000000e+00
; LLUBI-ERR:   %p = fadd ppc_fp128 1.000000e+00, 2.000000e+00 => ppc_fp128 3.000000e+00
; LLUBI-ERR:   %v = fadd <2 x float> <float 1.000000e+00, float +inf>, <float 1.000000e+00, float -inf> => { float 2.000000e+00, float NaN }
; LLUBI-ERR:   ret i32 0
; LLUBI-ERR: Exiting function: main
