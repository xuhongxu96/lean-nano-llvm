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

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   %pad = alloca [168 x i8], align 1 => ptr 0x8 [pad]
; LLUBI-ERR:   %a = alloca [64 x i8], align 1 => ptr 0xB1 [a]
; LLUBI-ERR: Stacktrace:
; LLUBI-ERR: #0   call void @llvm.memset.p0.i64(ptr %a, i8 0, i64 -1, i1 false) at @main <stdin>:8
; LLUBI-ERR: Immediate UB detected: Memory access is out of bounds. Accessed size: 18446744073709551615, Address: 0xB1, Object base: 0xb1, Object size: 64.
; LLUBI-ERR: error: Execution of function 'main' failed.
