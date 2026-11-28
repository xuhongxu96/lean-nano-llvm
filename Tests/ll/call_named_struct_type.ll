; difftest bug B3 (regression of its fix, found by campaign run 2): a call's recorded function type
; must have its named types resolved like the callee's prototype, otherwise `%s` and the
; structure it names compare unequal and the call is wrongly reported as a signature mismatch.
; From case 2dc29b66bffd60ab (InstCombine test70).

%s = type { i32, i32, i16 }

define %s @f(i32 %x) {
  %a = insertvalue %s zeroinitializer, i32 %x, 0
  ret %s %a
}

define i32 @main() {
  %r = call %s @f(i32 7)
  %v = extractvalue %s %r, 0
  ret i32 %v
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 7
; LLUBI-ERR: Entering function: main
; LLUBI-ERR: Entering function: f
; LLUBI-ERR:   i32 %x = i32 7
; LLUBI-ERR:   %a = insertvalue %s zeroinitializer, i32 %x, 0 => { i32 7, i32 0, i16 0 }
; LLUBI-ERR:   ret %s %a
; LLUBI-ERR: Exiting function: f
; LLUBI-ERR:   %r = call %s @f(i32 7) => { i32 7, i32 0, i16 0 }
; LLUBI-ERR:   %v = extractvalue %s %r, 0 => i32 7
; LLUBI-ERR:   ret i32 %v
; LLUBI-ERR: Exiting function: main
