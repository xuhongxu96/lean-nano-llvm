; EXPECT_EXIT: 1
; EXPECT_ERR: UB: Indirect call through a function pointer with mismatched signature.
;
; difftest (phase 2): "If the function signature does not match the function type of the
; call, the behavior is undefined" (LangRef `call`); llubi reports immediate UB. We stop with
; a static error, which the refinement relation does not treat as UB.

define i8 @g(i8 %x) {
  ret i8 %x
}

define i32 @main() {
  %r = call i8 @g(i32 1)
  ret i32 0
}
