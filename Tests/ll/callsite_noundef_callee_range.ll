; EXPECT_EXIT: 1
; EXPECT_ERR: UB: The value poison violates noundef attribute.
; XFAIL: difftest bug B1 (call-site and callee parameter attributes are applied in separate passes)
;
; difftest (phase 2): call-site and callee parameter attributes form one set (llubi
; `handleAttributes(Ty, V, AttrsAtCallSite, AttrsAtCallee)`): the callee's range makes 5
; poison, then the call site's noundef makes that immediate UB. We check the call site's
; noundef before applying the callee's range.

define i8 @f(i8 range(i8 0, 2) %x) {
  ret i8 %x
}

define i32 @main() {
  %r = call i8 @f(i8 noundef 5)
  ret i32 0
}
