; difftest (phase 2), P1: metadata numbers are the IR parser's MDNode creation order (forward references create a temporary node; inline nodes are uniqued).

define i32 @main() {
  %p = alloca i32
  store i32 1, ptr %p
  %a = load i32, ptr %p, !range !1
  %b = load i32, ptr %p, !range !0
  ret i32 0
}
!0 = !{i32 0, i32 10}
!1 = !{i32 0, i32 5}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 0
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   %p = alloca i32, align 4 => ptr 0x8 [p]
; LLUBI-ERR:   store i32 1, ptr %p, align 4
; LLUBI-ERR:   %a = load i32, ptr %p, align 4, !range !3 => i32 1
; LLUBI-ERR:   %b = load i32, ptr %p, align 4, !range !2 => i32 1
; LLUBI-ERR:   ret i32 0
; LLUBI-ERR: Exiting function: main
