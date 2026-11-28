;
; difftest (phase 2), output of `lean-nano-llvm llubi --verbose` against the pinned llubi
; (golden `quoted_name_escape.expected`): escapes in quoted names are decoded when parsed (`@"\01x"` is printed as `@"\01x"`).

@"\01x" = global i32 3
define i32 @main() {
  %v = load i32, ptr @"\01x"
  ret i32 %v
}
