;
; difftest (phase 2), output of `lean-nano-llvm llubi --verbose` against the pinned llubi
; (golden `attr_group_numbering.expected`): attribute groups are numbered as LLVM prints them.

declare double @sin(double) #0
define double @f() {
  %s = call double @sin(double 1.0) #0
  ret double %s
}
attributes #0 = { nounwind memory(none) }
define i32 @main() {
  %r = call double @f()
  ret i32 0
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: Entering function: main
; LLUBI-ERR: Entering function: f
; LLUBI-ERR: Unrecognized instruction:   %s = call double @sin(double 1.000000e+00) #0
; LLUBI-ERR: error: Execution of function 'main' failed.
