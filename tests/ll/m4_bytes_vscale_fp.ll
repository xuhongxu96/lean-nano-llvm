; EXPECT_EXIT: 0
; EXPECT_OUT: i32 94

target datalayout = "e-p:64:64:64-i8:8:8-i32:32:32-i64:64:64"

declare i32 @llvm.vscale.i32()

define i32 @main() {
entry:
  ; 1. Byte type b32 + bitextract + bitinsert
  %ex = bitextract i8, b32 u0x12345678, i32 8
  ; ex = 0x56 = 86
  %ex32 = zext i8 %ex to i32

  ; 2. Pointer provenance roundtrip through b128 bitinsert/bitextract
  %slot = alloca i32, align 4
  store i32 4, ptr %slot, align 4
  %bp = bitinsert b128 0, ptr %slot, i32 32
  %p2 = bitextract ptr, b128 %bp, i32 32
  %v_ptr = load i32, ptr %p2, align 4

  ; 3. Scalable vector + vscale (default vscale = 4)
  %vs = call i32 @llvm.vscale.i32()
  ; vs = 4

  ; 4. x86_fp80 and ppc_fp128 arithmetic
  %f80 = fadd x86_fp80 0xK40008000000000000000, 0xK40008000000000000000
  %f80_ok = fcmp oeq x86_fp80 %f80, 0xK40018000000000000000
  %ppc = fadd ppc_fp128 0xM40000000000000000000000000000000, 0xM40000000000000000000000000000000
  %ppc_ok = fcmp oeq ppc_fp128 %ppc, 0xM40100000000000000000000000000000

  ; Check both FP results (if either fails, return 0)
  %both_ok = and i1 %f80_ok, %ppc_ok
  %sum1 = add i32 %ex32, %v_ptr
  %sum2 = add i32 %sum1, %vs
  %final = select i1 %both_ok, i32 %sum2, i32 0
  ret i32 %final
}
