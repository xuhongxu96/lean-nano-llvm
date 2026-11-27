; XFAIL: difftest bug P10 (llubi output differs: a poison argument of a library call)
;
; difftest (phase 2), output of `lean-nano-llvm llubi --verbose` against the pinned llubi
; (golden `libcall_poison_argument_reason.expected`): a poison argument of a library call (`memset`) is reported as "Poison argument passed to a library call at argument index N.".

target datalayout = "p:32:32"
declare ptr @memset(ptr, i32, i32)
define i32 @main() {
  %a = alloca [4 x i8]
  %r = call ptr @memset(ptr %a, i32 0, i32 poison)
  ret i32 0
}
