; difftest P2 (follow-up): intrinsic declarations carry LLVM's implicit attribute sets, for every
; intrinsic of the pinned LLVM. The table used to cover only the corpus's intrinsics and guessed others
; from a neighbour sharing a prefix: `llvm.coro.align` (`nounwind memory(none)`) got the set of
; `llvm.coro.done` (`nounwind memory(argmem: readwrite)`), merging two attribute groups, so the
; group number llubi prints for `@main`'s call was one too small.

declare i1 @llvm.coro.done(ptr)
declare i64 @llvm.coro.align.i64()
declare void @ext()

define i32 @main() {
  call void @ext() #0
  ret i32 0
}

attributes #0 = { cold }

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: Entering function: main
; LLUBI-ERR: Unrecognized instruction:   call void @ext() #2
; LLUBI-ERR: error: Execution of function 'main' failed.
