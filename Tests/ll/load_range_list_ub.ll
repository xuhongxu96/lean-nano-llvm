; EXPECT_EXIT: 1
; EXPECT_ERR: UB: The value poison violates !noundef metadata.
; XFAIL: difftest bug B7 (!range metadata with several ranges is ignored)
;
; difftest (phase 2): `!range !{i32 1, i32 6, i32 8, i32 10}` allows [1,6) and [8,10) (LangRef
; `range` metadata); 7 is outside both, so the load is poison and !noundef makes it UB. We
; ignore range lists with more than one pair.
; Minimized from case 000dfa1d6aca104d (InstCombine test_multi_range2).

!0 = !{i32 1, i32 6, i32 8, i32 10}

define i32 @main() {
  %p = alloca i32
  store i32 7, ptr %p
  %x = load i32, ptr %p, !range !0, !noundef !{}
  ret i32 %x
}
