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

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 7
; LLUBI-ERR: Entering function: main
; LLUBI-ERR: Entering function: f
; LLUBI-ERR:   i32 %0 = i32 7
; LLUBI-ERR:   i1 %c = F
; LLUBI-ERR:   br i1 %c, label %a, label %join jump to %join
; LLUBI-ERR:   %r = phi i32 [ %0, %1 ], [ 2, %a ] => i32 7
; LLUBI-ERR:   ret i32 %r
; LLUBI-ERR: Exiting function: f
; LLUBI-ERR:   %r = call i32 @f(i32 7, i1 false) => i32 7
; LLUBI-ERR:   ret i32 %r
; LLUBI-ERR: Exiting function: main
