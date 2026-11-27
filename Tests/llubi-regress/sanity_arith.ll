; Sanity check of the runner: identical output to the pinned llubi.
define i32 @main() {
  %a = add nsw i32 40, 2
  %b = mul i32 %a, 3
  %c = udiv i32 %b, 2
  ret i32 %c
}
