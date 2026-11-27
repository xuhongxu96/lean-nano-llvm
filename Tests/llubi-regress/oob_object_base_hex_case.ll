; XFAIL: difftest bug P9 (llubi output differs: `Object base:` of out-of-bounds reports is lowercase hex)
;
; difftest (phase 2), output of `lean-nano-llvm llubi --verbose` against the pinned llubi
; (golden `oob_object_base_hex_case.expected`): `Object base:` of out-of-bounds reports is lowercase hex (llubi Twine::utohexstr).

define i32 @main() {
  %pad = alloca [168 x i8]
  %a = alloca [64 x i8]
  call void @llvm.memset.p0.i64(ptr %a, i8 0, i64 -1, i1 false)
  ret i32 0
}
declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)
