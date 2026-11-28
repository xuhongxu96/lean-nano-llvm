; difftest: function objects are not constant memory: a store to a function pointer is reported as
; an out-of-bounds access (the object has size 0), as in llubi. From case 0735f2f62d43e5ba.

declare void @f()
define i32 @main() {
  store i32 1, ptr @f
  ret i32 0
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: Entering function: main
; LLUBI-ERR: Stacktrace:
; LLUBI-ERR: #0   store i32 1, ptr @f, align 4 at @main <stdin>:6
; LLUBI-ERR: Immediate UB detected: Memory access is out of bounds. Accessed size: 4, Address: 0x8, Object base: 0x8, Object size: 0.
; LLUBI-ERR: error: Execution of function 'main' failed.
