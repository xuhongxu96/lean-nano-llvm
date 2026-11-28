;
; difftest (phase 2), output of `lean-nano-llvm llubi --verbose` against the pinned llubi
; (golden `switch_metadata.expected`): `switch` is printed with its metadata attachments (`!prof`).

define i32 @main() {
  switch i32 1, label %d [ i32 1, label %a ], !prof !0
a:
  ret i32 0
d:
  ret i32 1
}
!0 = !{!"branch_weights", i32 1, i32 9}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 0
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   switch i32 1, label %d [
; LLUBI-ERR:     i32 1, label %a
; LLUBI-ERR:   ], !prof !1 jump to %a
; LLUBI-ERR:   ret i32 0
; LLUBI-ERR: Exiting function: main
