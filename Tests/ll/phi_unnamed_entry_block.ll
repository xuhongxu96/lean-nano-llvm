; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i32 1
;
; difftest (phase 2): an unlabeled entry block takes the next unnamed slot number, here %0
; (LangRef "Functions": "If the first basic block ... has no label, it is assigned %N"), so the
; phi's incoming block %0 is the entry block. We name the block `entry`, the phi finds no
; incoming value for it, and execution stops with a static error.
; Minimized from case 0177023a2f4d1cdc (InstCombine cmp_sgt_phi_node_cant_fold_2).

define i32 @f(i1 %c) {
  br i1 %c, label %a, label %join
a:
  br label %join
join:
  %r = phi i32 [ 1, %0 ], [ 2, %a ]
  ret i32 %r
}

define i32 @main() {
  %r = call i32 @f(i1 false)
  ret i32 %r
}
