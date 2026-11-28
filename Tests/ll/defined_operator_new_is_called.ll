; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i32 42
;
; difftest (phase 2): as defined_allocator_is_called.ll, for `operator new(unsigned)` (@_Znwj).
; Minimized from case 1aa3170c73369178.

define ptr @_Znwj(i32 %n) {
  ret ptr inttoptr (i64 42 to ptr)
}

define i32 @main() {
  %p = call ptr @_Znwj(i32 4)
  %i = ptrtoint ptr %p to i64
  %t = trunc i64 %i to i32
  ret i32 %t
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 42
; LLUBI-ERR: Entering function: main
; LLUBI-ERR: Entering function: _Znwj
; LLUBI-ERR:   i32 %n = i32 4
; LLUBI-ERR:   ret ptr inttoptr (i64 42 to ptr)
; LLUBI-ERR: Exiting function: _Znwj
; LLUBI-ERR:   %p = call ptr @_Znwj(i32 4) => ptr 0x2A [nullary]
; LLUBI-ERR:   %i = ptrtoint ptr %p to i64 => i64 42
; LLUBI-ERR:   %t = trunc i64 %i to i32 => i32 42
; LLUBI-ERR:   ret i32 %t
; LLUBI-ERR: Exiting function: main
