; difftest (phase 2), P1: metadata numbers are the IR parser's MDNode creation order (forward references create a temporary node; inline nodes are uniqued).

!0 = !{!1, !1, i64 0}
!1 = !{!"int", !2, i64 0}
!2 = !{!"omnipotent char", !3, i64 0}
!3 = !{!"Simple C/C++ TBAA"}
!4 = !{i32 0, i32 10}
define i32 @main() {
  %p = alloca i32
  store i32 1, ptr %p, !tbaa !0
  %a = load i32, ptr %p, !range !4
  ret i32 0
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 0
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   %p = alloca i32, align 4 => ptr 0x8 [p]
; LLUBI-ERR:   store i32 1, ptr %p, align 4, !tbaa !1
; LLUBI-ERR:   %a = load i32, ptr %p, align 4, !range !7 => i32 1
; LLUBI-ERR:   ret i32 0
; LLUBI-ERR: Exiting function: main
