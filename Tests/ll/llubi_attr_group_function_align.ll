; difftest P2 (follow-up): `align 2` after a function's attributes is the function's alignment, not
; an attribute, so it does not form a separate attribute set. From case 34cd75a628f5856f.

declare ptr @ext(i64)
define void @f() #0 align 2 {
  %p = tail call ptr @ext(i64 1) #0
  ret void
}
define i32 @main() {
  call void @f()
  ret i32 0
}
attributes #0 = { nounwind }

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: Entering function: main
; LLUBI-ERR: Entering function: f
; LLUBI-ERR: Unrecognized instruction:   %p = tail call ptr @ext(i64 1) #0
; LLUBI-ERR: error: Execution of function 'main' failed.
