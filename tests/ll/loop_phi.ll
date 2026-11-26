; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i32 45

define i32 @main() {
entry:
  br label %loop

loop:
  %i = phi i32 [ 0, %entry ], [ %next_i, %loop ]
  %acc = phi i32 [ 0, %entry ], [ %next_acc, %loop ]
  %next_acc = add i32 %acc, %i
  %next_i = add i32 %i, 1
  %cond = icmp slt i32 %next_i, 10
  br i1 %cond, label %loop, label %done

done:
  ret i32 %next_acc
}
