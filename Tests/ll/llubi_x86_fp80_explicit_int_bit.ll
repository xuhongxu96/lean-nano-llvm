; difftest B10 (follow-up): `x86_fp80` values keep their x87 encoding, explicit integer bit included
; (`FloatFormat.explicitInt`). LLVM's `APFloat` reads an unnormal as a NaN with the maximal exponent
; and a pseudo-denormal with exponent 1, and keeps a NaN's integer bit through `bitcast`, NaN
; propagation, `fneg`, `fabs`, `select`, `freeze` and memory. Our 79-bit format used to lose it.

define i32 @probe1() {
  %a = bitcast i80 604453046008047722168320 to x86_fp80
  %u = bitcast i80 302231454903657293676544 to x86_fp80
  %b = fadd x86_fp80 %a, 0xK3FFF8000000000000000
  %c = bitcast x86_fp80 %b to i80
  %d = fptrunc x86_fp80 %a to double
  %e = fneg x86_fp80 %a
  %f = bitcast x86_fp80 %e to i80
  %g = fadd x86_fp80 %u, 0xK3FFF8000000000000000
  %h = bitcast x86_fp80 %u to i80
  %m = alloca x86_fp80
  store x86_fp80 %a, ptr %m
  %l = load x86_fp80, ptr %m
  %li = load i80, ptr %m
  %s = select i1 true, x86_fp80 %a, x86_fp80 %u
  %fr = freeze x86_fp80 %a
  %ab = call x86_fp80 @llvm.fabs.f80(x86_fp80 %a)
  ret i32 0
}
declare x86_fp80 @llvm.fabs.f80(x86_fp80)
define i32 @probe2() {
  %a = fadd x86_fp80 0xK40000000000000000000, 0xK00000000000000000000
  %b = fadd x86_fp80 0xK00008000000000000001, 0xK00000000000000000000
  %pd = bitcast i80 9223372036854775809 to x86_fp80
  %pdi = bitcast x86_fp80 %pd to i80
  %m = alloca x86_fp80
  store i80 302231454903657293676544, ptr %m
  %l = load x86_fp80, ptr %m
  store x86_fp80 %l, ptr %m
  %li = load i80, ptr %m
  ret i32 0
}
define i32 @main() {
  %a = call i32 @probe1()
  %b = call i32 @probe2()
  ret i32 0
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 0
; LLUBI-ERR: Entering function: main
; LLUBI-ERR: Entering function: probe1
; LLUBI-ERR:   %a = bitcast i80 604453046008047722168320 to x86_fp80 => x86_fp80 0x7FFF771CBED3D2BE0000
; LLUBI-ERR:   %u = bitcast i80 302231454903657293676544 to x86_fp80 => x86_fp80 0x7FFF0000000000000000
; LLUBI-ERR:   %b = fadd x86_fp80 %a, 1.000000e+00 => x86_fp80 0x7FFF771CBED3D2BE0000
; LLUBI-ERR:   %c = bitcast x86_fp80 %b to i80 => i80 604453046008047722168320
; LLUBI-ERR:   %d = fptrunc x86_fp80 %a to double => double 0xFFF8000000000000
; LLUBI-ERR:   %e = fneg x86_fp80 %a => x86_fp80 0xFFFF771CBED3D2BE0000
; LLUBI-ERR:   %f = bitcast x86_fp80 %e to i80 => i80 -9863799266865184768
; LLUBI-ERR:   %g = fadd x86_fp80 %u, 1.000000e+00 => x86_fp80 0x7FFF0000000000000000
; LLUBI-ERR:   %h = bitcast x86_fp80 %u to i80 => i80 604444463063240877801472
; LLUBI-ERR:   %m = alloca x86_fp80, align 16 => ptr 0x10 [m]
; LLUBI-ERR:   store x86_fp80 %a, ptr %m, align 16
; LLUBI-ERR:   %l = load x86_fp80, ptr %m, align 16 => x86_fp80 0x7FFF771CBED3D2BE0000
; LLUBI-ERR:   %li = load i80, ptr %m, align 4 => i80 604453046008047722168320
; LLUBI-ERR:   %s = select i1 true, x86_fp80 %a, x86_fp80 %u => x86_fp80 0x7FFF771CBED3D2BE0000
; LLUBI-ERR:   %fr = freeze x86_fp80 %a => x86_fp80 0x7FFF771CBED3D2BE0000
; LLUBI-ERR:   %ab = call x86_fp80 @llvm.fabs.f80(x86_fp80 %a) => x86_fp80 0x7FFF771CBED3D2BE0000
; LLUBI-ERR:   ret i32 0
; LLUBI-ERR: Exiting function: probe1
; LLUBI-ERR:   %a = call i32 @probe1() => i32 0
; LLUBI-ERR: Entering function: probe2
; LLUBI-ERR:   %a = fadd x86_fp80 +snan(0x0), 0.000000e+00 => x86_fp80 0xFFFFC000000000000000
; LLUBI-ERR:   %b = fadd x86_fp80 f0x00018000000000000001, 0.000000e+00 => x86_fp80 0x00018000000000000001
; LLUBI-ERR:   %pd = bitcast i80 9223372036854775809 to x86_fp80 => x86_fp80 0x00018000000000000001
; LLUBI-ERR:   %pdi = bitcast x86_fp80 %pd to i80 => i80 27670116110564327425
; LLUBI-ERR:   %m = alloca x86_fp80, align 16 => ptr 0x30 [m]
; LLUBI-ERR:   store i80 302231454903657293676544, ptr %m, align 4
; LLUBI-ERR:   %l = load x86_fp80, ptr %m, align 16 => x86_fp80 0x7FFF0000000000000000
; LLUBI-ERR:   store x86_fp80 %l, ptr %m, align 16
; LLUBI-ERR:   %li = load i80, ptr %m, align 4 => i80 604444463063240877801472
; LLUBI-ERR:   ret i32 0
; LLUBI-ERR: Exiting function: probe2
; LLUBI-ERR:   %b = call i32 @probe2() => i32 0
; LLUBI-ERR:   ret i32 0
; LLUBI-ERR: Exiting function: main
