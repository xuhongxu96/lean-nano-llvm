; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i32 1
; XFAIL: difftest bug B6 (a datalayout pointer spec with flags, `pe1:...`, is read as address space 0)
;
; difftest (phase 2): `p[<flags>][<as>]:...` (LangRef "Data Layout"): in `pe1:64:64:64:32`, `e`
; is a flag and the spec (32-bit index width) applies to address space 1. Address space 0
; keeps 64-bit indices, so the GEP by 2^32 changes the high half of the address. We apply the
; 32-bit index width to address space 0 and the offset is lost.
; Minimized from case 039442c10d75342e (InstCombine sub_ptrtoint_ptrtoaddr).

target datalayout = "pe1:64:64:64:32"

define i32 @main() {
  %a = alloca i8
  %g = getelementptr i8, ptr %a, i64 4294967296
  %d = ptrtoaddr ptr %g to i64
  %s = lshr i64 %d, 32
  %t = trunc i64 %s to i32
  ret i32 %t
}
