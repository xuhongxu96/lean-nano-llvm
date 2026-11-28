; difftest: an unnamed (numbered) global has an empty name: llubi prints pointers to it as [@].

@0 = global i32 5

define i32 @main() {
  %p = getelementptr i8, ptr @0, i64 0
  %v = load i32, ptr %p
  ret i32 %v
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 5
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   %p = getelementptr i8, ptr @0, i64 0 => ptr 0x8 [@]
; LLUBI-ERR:   %v = load i32, ptr %p, align 4 => i32 5
; LLUBI-ERR:   ret i32 %v
; LLUBI-ERR: Exiting function: main
