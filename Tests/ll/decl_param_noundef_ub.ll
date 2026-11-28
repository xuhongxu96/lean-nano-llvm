; EXPECT_EXIT: 1
; EXPECT_ERR: UB: The value poison violates noundef attribute.
;
; difftest bug B1: the parameter attributes of a declared callee apply to the arguments of a call
; (llubi handleAttributes), before the call is found to have no body. Minimized from case
; 042841b8febeac04.

declare ptr @ext(ptr noundef)
define i32 @main() {
  %r = call ptr @ext(ptr poison)
  ret i32 0
}
