; difftest P14 (follow-up): `personality ptr @f` is a constant use of `@f`, which takes its address:
; llubi allocates a function object for it, which shifts later stack addresses. From case
; 04dafade1e28b70f.

declare i32 @__gxx_personality_v0(...)
declare void @g()

define i32 @f() personality ptr @__gxx_personality_v0 {
  %a = alloca i32
  store i32 1, ptr %a
  invoke void @g() to label %ok unwind label %lp
ok:
  ret i32 0
lp:
  %e = landingpad { ptr, i32 } cleanup
  ret i32 1
}

define i32 @main() {
  %p = alloca i64
  %r = call i32 @f()
  ret i32 %r
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   %p = alloca i64, align 8 => ptr 0x10 [p]
; LLUBI-ERR: Entering function: f
; LLUBI-ERR:   %a = alloca i32, align 4 => ptr 0x1C [a]
; LLUBI-ERR:   store i32 1, ptr %a, align 4
; LLUBI-ERR: Unrecognized instruction:   invoke void @g()
; LLUBI-ERR:           to label %ok unwind label %lp
; LLUBI-ERR: error: Execution of function 'main' failed.
