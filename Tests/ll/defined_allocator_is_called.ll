; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i32 84
;
; difftest (phase 2): a function the module defines is executed as defined, whatever its
; name; llubi runs the bodies of @malloc and @calloc here and returns 42 + 42. We intercept
; calls to functions named malloc/calloc as the C allocator even when the module defines
; them (a defined @strlen is executed correctly).
; Minimized from case 120366743a24e201 (InstCombine, a module defining @calloc).

define ptr @malloc(i64 %n) {
  ret ptr inttoptr (i64 42 to ptr)
}

define ptr @calloc(i64 %n, i64 %s) {
  ret ptr inttoptr (i64 42 to ptr)
}

define i32 @main() {
  %p = call ptr @malloc(i64 1)
  %q = call ptr @calloc(i64 1, i64 1)
  %i = ptrtoint ptr %p to i64
  %j = ptrtoint ptr %q to i64
  %s = add i64 %i, %j
  %t = trunc i64 %s to i32
  ret i32 %t
}
