; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i32 7
;
; difftest (phase 2): as phi_unnamed_entry_block.ll, with an unnamed parameter: the parameter
; is %0, so the unlabeled entry block is %1.

define i32 @f(i32, i1 %c) {
  br i1 %c, label %a, label %join
a:
  br label %join
join:
  %r = phi i32 [ %0, %1 ], [ 2, %a ]
  ret i32 %r
}

define i32 @main() {
  %r = call i32 @f(i32 7, i1 false)
  ret i32 %r
}
