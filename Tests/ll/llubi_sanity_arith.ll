; Sanity check of the runner: identical output to the pinned llubi.
define i32 @main() {
  %a = add nsw i32 40, 2
  %b = mul i32 %a, 3
  %c = udiv i32 %b, 2
  ret i32 %c
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 63
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   %a = add nsw i32 40, 2 => i32 42
; LLUBI-ERR:   %b = mul i32 %a, 3 => i32 126
; LLUBI-ERR:   %c = udiv i32 %b, 2 => i32 63
; LLUBI-ERR:   ret i32 %c
; LLUBI-ERR: Exiting function: main
