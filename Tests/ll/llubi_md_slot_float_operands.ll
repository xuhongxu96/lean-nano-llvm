; difftest P1 (follow-up): metadata nodes differing only in float operands are distinct nodes
; (they were uniqued because the node key ignored float literals). From case 0410cd347422c221.

define i32 @main() {
  %a = fneg double 1.0, !fpmath !0
  %b = fneg double 2.0, !fpmath !1
  ret i32 0
}
!0 = !{float 5.000000e+00}
!1 = !{float 2.500000e+00}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 0
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   %a = fneg double 1.000000e+00, !fpmath !2 => double -1.000000e+00
; LLUBI-ERR:   %b = fneg double 2.000000e+00, !fpmath !3 => double -2.000000e+00
; LLUBI-ERR:   ret i32 0
; LLUBI-ERR: Exiting function: main
