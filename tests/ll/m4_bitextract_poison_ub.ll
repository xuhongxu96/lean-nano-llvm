; EXPECT_EXIT: 1
; EXPECT_ERR: UB:

define void @main() {
entry:
  %b = bitinsert b32 0, i16 poison, i32 4
  %c = bitextract i1, b32 %b, i32 8
  br i1 %c, label %t, label %f
t:
  ret void
f:
  ret void
}
