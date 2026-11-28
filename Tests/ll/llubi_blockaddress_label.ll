; difftest P (printing): a blockaddress pointer prints with its block label, as llubi does (ptr 0x8 [L1]).

define i32 @main(i1 %c) {
entry:
  %d = select i1 true, ptr blockaddress(@main, %L1), ptr blockaddress(@main, %L2)
  indirectbr ptr %d, [label %L1, label %L2]
L1:
  ret i32 1
L2:
  ret i32 2
}

; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)
; LLUBI-EXIT: 1
; LLUBI-ERR: warning: The signature of function 'main' does not match 'int main(int, char**)', passing null values for all arguments.
; LLUBI-ERR: Entering function: main
; LLUBI-ERR:   i1 %c = F
; LLUBI-ERR:   %d = select i1 true, ptr blockaddress(@main, %L1), ptr blockaddress(@main, %L2) => ptr 0x8 [L1]
; LLUBI-ERR:   indirectbr ptr %d, [label %L1, label %L2] jump to %L1
; LLUBI-ERR:   ret i32 1
; LLUBI-ERR: Exiting function: main
