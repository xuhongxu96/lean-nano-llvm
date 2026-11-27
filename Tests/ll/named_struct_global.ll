; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i64 42

target datalayout = "e-p:64:64:64"

; LLVM's default layout (`i64:32:64`) places the i64 field at offset 4.
%Pair = type { i32, i64 }

@g_pair = global %Pair { i32 12, i64 30 }, align 8

define i64 @main() {
entry:
  %p0 = getelementptr inbounds %Pair, ptr @g_pair, i64 0, i32 0
  %p1 = getelementptr inbounds %Pair, ptr @g_pair, i64 0, i32 1
  %a = load i32, ptr %p0, align 4
  %a64 = zext i32 %a to i64
  %b = load i64, ptr %p1, align 4
  %sum = add i64 %a64, %b
  ret i64 %sum
}
