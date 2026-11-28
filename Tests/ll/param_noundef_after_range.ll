; EXPECT_EXIT: 1
; EXPECT_ERR: UB: The value poison violates noundef attribute.
;
; difftest (phase 2): poison-generating parameter attributes (range, nofpclass, nonnull, align)
; must be applied before noundef is checked, whatever their order in the source (LangRef
; "Parameter Attributes"; llubi `handleAttributes`). 5 is outside range [0, 2), so %x is
; poison, and poison for a noundef parameter is immediate UB.
; Minimized from mutant case 000680558bc02fc9 (test_logical_and_trunc_nuw_vec).

define i8 @f(i8 noundef range(i8 0, 2) %x) {
  ret i8 %x
}

define i32 @main() {
  %r = call i8 @f(i8 5)
  ret i32 0
}
