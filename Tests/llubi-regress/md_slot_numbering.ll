; XFAIL: difftest bug P1 (llubi output differs: metadata nodes are numbered in LLVM SlotTracker order)
;
; difftest (phase 2), output of `lean-nano-llvm llubi --verbose` against the pinned llubi
; (golden `md_slot_numbering.expected`): metadata nodes are numbered in LLVM SlotTracker order (first use), not source order.

define i32 @main() {
  %p = alloca i32
  store i32 1, ptr %p
  %a = load i32, ptr %p, !range !1
  %b = load i32, ptr %p, !range !0
  ret i32 0
}
!0 = !{i32 0, i32 10}
!1 = !{i32 0, i32 5}
