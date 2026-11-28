; difftest P15: load metadata is checked in llubi's order: poison-generating metadata (!align makes
; the unaligned pointer poison), then !noundef, then !dereferenceable; so the violation reported is
; !noundef (we used to report !dereferenceable first). From case 02d64bc074a0df6a.

define i32 @main() {
  %m = alloca i64
  store i64 42, ptr %m
  %p = load ptr, ptr %m, !dereferenceable !0, !align !0, !noundef !1
  ret i32 0
}
!0 = !{i64 8}
!1 = !{}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   %m = alloca i64, align 8 => ptr 0x8 [m]
; LLUBI-ERR:   store i64 42, ptr %m, align 4
; LLUBI-ERR: Stacktrace:
; LLUBI-ERR: #0   %p = load ptr, ptr %m, align 8, !dereferenceable !2, !align !2, !noundef !3 at @main <stdin>:8
; LLUBI-ERR: Immediate UB detected: The value poison violates !noundef metadata.
; LLUBI-ERR: error: Execution of function 'main' failed.
