; EXPECT_EXIT: 1
; EXPECT_ERR: UB:

define void @main() {
entry:
  br i1 poison, label %a, label %b
a:
  ret void
b:
  ret void
}
