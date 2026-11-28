; EXPECT_EXIT: 1
; EXPECT_ERR: UB: The value poison violates !noundef metadata.
;
; difftest (phase 2): `!range !{i32 1, i32 6, i32 8, i32 10}` allows [1,6) and [8,10) (LangRef
; `range` metadata); 7 is outside both, so the load is poison and !noundef makes it UB. We
; ignore range lists with more than one pair.
; Minimized from case 000dfa1d6aca104d (InstCombine test_multi_range2).

!0 = !{i32 1, i32 6, i32 8, i32 10}

define i32 @main() {
  %p = alloca i32
  store i32 7, ptr %p
  %x = load i32, ptr %p, !range !0, !noundef !{}
  ret i32 %x
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   %p = alloca i32, align 4 => ptr 0x8 [p]
; LLUBI-ERR:   store i32 7, ptr %p, align 4
; LLUBI-ERR: Stacktrace:
; LLUBI-ERR: #0   %x = load i32, ptr %p, align 4, !range !0, !noundef !1 at @main <stdin>:14
; LLUBI-ERR: Immediate UB detected: The value poison violates !noundef metadata.
; LLUBI-ERR: error: Execution of function 'main' failed.
