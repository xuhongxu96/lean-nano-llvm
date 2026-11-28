; difftest (phase 2), P1: specialized metadata nodes (!DICompileUnit, !DIFile) are MDNodes and take numbers in the parser's creation order. From case 01568adf0d398abc.

define i32 @range_metadata_constant_passthru(i1 %cond, ptr %p) {
entry:
  br i1 %cond, label %if.end, label %if.true

if.true:                                          ; preds = %entry
  %v = load i32, ptr %p, align 4, !range !5
  br label %if.end

if.end:                                           ; preds = %if.true, %entry
  %res = phi i32 [ %v, %if.true ], [ 1000, %entry ]
  ret i32 %res
}

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!2, !3}
!llvm.ident = !{!4}

!0 = distinct !DICompileUnit(language: DW_LANG_C, file: !1, producer: "clang", isOptimized: false, runtimeVersion: 0, emissionKind: NoDebug)
!1 = !DIFile(filename: "foo.c", directory: "/tmp")
!2 = !{i32 2, !"Dwarf Version", i32 4}
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{!"clang"}
!5 = !{i32 0, i32 10}

define i32 @main() {
  %dt.p1 = alloca [64 x i8], align 16
  call void @llvm.memset.p0.i64(ptr %dt.p1, i8 34, i64 64, i1 false)
  %dt.r = call i32 @range_metadata_constant_passthru(i1 false, ptr %dt.p1)
  ret i32 0
}

declare void @llvm.memset.p0.i64(ptr writeonly, i8, i64, i1 immarg)
