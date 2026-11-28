; difftest (phase 2), P1: metadata numbers are the IR parser's MDNode creation order (forward references create a temporary node; inline nodes are uniqued).

define i32 @main() {
  %p = alloca i32
  store i32 1, ptr %p
  %a = load i32, ptr %p, !range !1
  %b = load i32, ptr %p, !range !0
  ret i32 0
}
!0 = !{i32 0, i32 10}
!1 = !{i32 0, i32 5}
