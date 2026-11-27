; EXPECT_EXIT: 0
; EXPECT_OUT: OK: i32 55

target datalayout = "e-p:64:64:64"

define i32 @fib(i32 %n) {
entry:
  %c = icmp sle i32 %n, 1
  br i1 %c, label %base, label %rec

base:
  ret i32 %n

rec:
  %n1 = sub i32 %n, 1
  %n2 = sub i32 %n, 2
  %f1 = call i32 @fib(i32 %n1)
  %f2 = call i32 @fib(i32 %n2)
  %sum = add i32 %f1, %f2
  ret i32 %sum
}

define i32 @main() {
  %r = call i32 @fib(i32 10)
  ret i32 %r
}
