import LeanNanoLlvm.AST

section
open LeanNanoLlvm.AST

set_option pp.rawOnError true

/-
define i32 @f() {
B:
  %i0 = add i32 0, 1
  ret i32 %i0
} -/
def llvm_0_plus_1 : TopLevel 0 := ⟨[
  .definition {
    prototype := {
      name := .name "f",
      type := .function (.ret .i32) []
    },
    args := [],
    blocks := [{
      id := .name "B",
      code := [
        ⟨.id (.name "i0"), .intBinaryOp (.add Bool.false Bool.false) .i32 (.int 0) (.int 1)⟩
      ],
      terminator := ⟨.void 0, .ret ⟨.i32, (.identifier (.local_id (.name "i0")))⟩⟩
    }]
  }
]⟩

#eval llvm_0_plus_1.print
end

section
open LeanNanoLlvm.AST.Syntax
open scoped LeanNanoLlvm.AST.Syntax

#check [llvm-rawid| 1]
#check [llvm-rawid| a]

#check [llvm-identifier| @1]
#check [llvm-identifier| %19]
#check [llvm-identifier| @abc]
#check [llvm-identifier| %xyz]

#check [llvm-instruction-id| %a]
#check [llvm-instruction-id| %2]
#check [llvm-instruction-id| void (3)]

#check [llvm-type| i8]
#check [llvm-type| half]
#check [llvm-type| bfloat]
#check [llvm-type| float]
#check [llvm-type| double]
#check [llvm-type| fp128]
#check [llvm-type| ptr]
#check [llvm-type| ptr addrspace(1)]
#check [llvm-type| <4 x i32>]
#check [llvm-type| [2 x float]]
#check [llvm-type| { i32, i64 }]
#check [llvm-type| <{ i8, i32 }>]
#check [llvm-64-type| i$0]
#check [llvm-64-type| i8()]
#check [llvm-64-type| i8(i32, i16)]
#check [llvm-64-type| void(i32, i16)]

#check [llvm-exp| %1]
#check [llvm-exp| %a]
#check [llvm-exp| true]
#check [llvm-exp| false]
#check [llvm-exp| 123]
#check [llvm-exp| -42]
#check [llvm-exp| 1.5]
#check [llvm-exp| -2.25]
#check [llvm-exp| fbits(0x3F800000)]
#check [llvm-exp| null]
#check [llvm-exp| zeroinitializer]
#check [llvm-exp| undef]
#check [llvm-exp| poison]
#check [llvm-exp| <i32 1, i32 2>]
#check [llvm-exp| [i32 10, i32 20]]
#check [llvm-exp| { i32 1, float 2.0 }]

#check let temp := 10; [llvm-exp| <temp:int>]

#check [llvm-int-bin-op| add]
#check [llvm-int-bin-op| add nuw]
#check [llvm-int-bin-op| add nsw]
#check [llvm-int-bin-op| add nuw nsw]
#check [llvm-int-bin-op| xor]
#check [llvm-int-bin-op| or disjoint]

#check [llvm-conversion-op| sext]
#check [llvm-conversion-op| trunc nuw]
#check [llvm-conversion-op| trunc]
#check [llvm-conversion-op| bitcast]
#check [llvm-conversion-op| ptrtoint]
#check [llvm-conversion-op| inttoptr]
#check [llvm-conversion-op| fptosi]
#check [llvm-conversion-op| sitofp]

#check [llvm-instruction| add i8 %1, %3]
#check [llvm-64-0-instruction| add nuw i8 %1, %a]
#check [llvm-64-0-instruction| trunc nuw i32 %b to i8]
#check [llvm-64-0-instruction| zext i8 %b to i16]
#check [llvm-64-0-instruction| freeze i8 %1]
#check [llvm-64-10-instruction| add i8 undef, undef]
#check [llvm-instruction| fadd nnan ninf float 1.5, 2.5]
#check [llvm-instruction| fneg nsz double -0.0]
#check [llvm-instruction| icmp slt i32 %a, 10]
#check [llvm-instruction| fcmp oeq float %a, %b]
#check [llvm-instruction| select i1 %c, i32 %a, i32 %b]
#check [llvm-instruction| alloca i32, align 4]
#check [llvm-instruction| alloca i32, i64 4, align 8]
#check [llvm-instruction| load i32, ptr %p, align 4, !noundef]
#check [llvm-instruction| load i32, ptr %p, !noundef]
#check [llvm-instruction| store i32 42, ptr %p, align 4]
#check [llvm-instruction| getelementptr inbounds { i32, i64 }, ptr %p, i64 0, i32 1]
#check [llvm-instruction| extractvalue { i32, i64 } %s, 1]
#check [llvm-instruction| insertvalue { i32, i64 } %s, i64 9, 1]
#check [llvm-instruction| extractelement <4 x i32> %v, i32 2]
#check [llvm-instruction| insertelement <4 x i32> %v, i32 7, i32 1]
#check [llvm-instruction| shufflevector <2 x i32> %v1, <2 x i32> %v2, <2 x i32> <i32 1, i32 2>]
#check [llvm-instruction| call i32 @helper(i32 %a, ptr %p)]

#check [llvm-terminator| ret void]
#check [llvm-64-terminator| ret i8 %1]
#check [llvm-terminator| br label %next]
#check [llvm-terminator| br i1 %c, label %t, label %f]
#check [llvm-terminator| switch i32 %v, label %dflt [ i32 0, label %l0 i32 1, label %l1 ]]
#check [llvm-terminator| unreachable]

#check [llvm-declaration| declare i32 @puts(i8, i32)]

#check [llvm-codeline| %1 = add i8 %0, %a]
#check [llvm-64-1-codeline| freeze i8 %a]

#check [llvm-64-1-code|
%1 = add i8 %0, %a
%d = add i8 %2, %b
freeze i8 %1
]

#check [llvm-64-1-block|
entry:
  %1 = add i8 %0, %a
  %d = add i8 %2, %b
  freeze i8 %1
  ret void
]

#check [llvm-64-definition|
define void @f() {
entry:
  %1 = add i8 %0, %a
  %d = add i8 %2, %b
  freeze i8 %1
  ret void
}
]

#check [llvm-1-definition|
define i$0 @f(i$0 %a) {
entry:
  %1 = add i$0 %a, 0
  ret i$0 %1
}
]

#check [llvm-definition|
define i32 @multi_block(i1 %c) {
entry:
  br i1 %c, label %left, label %right
left:
  br label %merge
right:
  br label %merge
merge:
  %r = phi i32 [ 1, %left ], [ 2, %right ]
  ret i32 %r
}
]

#check [llvm|
@g = global i32 42, align 4
@c = constant float 1.5
declare i32 @puts(i8, i32)
define i32 @f(i8 %a) {
B:
  %i0 = add i32 0, 1
  freeze i32 %i0
  %y = add i32 undef, poison
  %y2 = add i32 undef, undef
  %x = add nsw i32 %i0, %i0
  ret i32 %x
}
]

open LeanNanoLlvm.AST in
theorem example_syntax_correct : TopLevel.print [llvm|
  define i32 @f() {
  B:
    %i0 = add i32 0, 1
    ret i32 %i0
  }
] = llvm_0_plus_1.print := by
  simp [TopLevel.print, llvm_0_plus_1]
  rfl

end
