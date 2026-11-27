; EXPECT_EXIT: 1
; EXPECT_ERR: UB: Indirect call through a function pointer with mismatched signature.
; XFAIL: difftest bug B3 (argument count mismatch at a call is a static error, not UB)
;
; difftest (phase 2): as call_signature_mismatch_arg_ub.ll, with an extra argument.

define i32 @g(i32 %x) {
  ret i32 %x
}

define i32 @main() {
  %r = call i32 @g(i32 1, i32 2)
  ret i32 0
}
