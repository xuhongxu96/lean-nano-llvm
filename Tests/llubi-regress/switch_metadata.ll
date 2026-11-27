; XFAIL: difftest bug P3 (llubi output differs: `switch` is printed with its metadata attachments)
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
