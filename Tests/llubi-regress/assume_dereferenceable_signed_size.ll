;
; difftest (phase 2), output of `lean-nano-llvm llubi --verbose` against the pinned llubi
; (golden `assume_dereferenceable_signed_size.expected`): the size of a `dereferenceable` assume bundle is printed signed.

define i32 @main() {
  %a = alloca i32
  call void @llvm.assume(i1 true) [ "dereferenceable"(ptr %a, i64 -1) ]
  ret i32 0
}
declare void @llvm.assume(i1)
