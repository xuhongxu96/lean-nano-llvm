; EXPECT_EXIT: 1
; EXPECT_ERR: UB:
; Regression test: wildcard provenance narrowing across multiple exposed objects

target datalayout = "e-p:64:64:64"

define void @main() {
entry:
  %a1 = alloca i32
  %a2 = alloca i32
  %i1 = ptrtoint ptr %a1 to i64
  %i2 = ptrtoint ptr %a2 to i64
  %diff = sub i64 %i2, %i1
  %p = inttoptr i64 %i1 to ptr
  %g = getelementptr i8, ptr %p, i64 %diff
  store i32 0, ptr %p
  store i32 0, ptr %g
  ret void
}
