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
    body := {
      id := .name "B",
      code := [
        ⟨.id (.name "i0"), .intBinaryOp (.add Bool.false Bool.false) .i32 (.int 0) (.int 1)⟩
      ],
      terminator := ⟨.void 0, .ret ⟨.i32, (.identifier (.local_id (.name "i0")))⟩⟩
    }
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
#check [llvm-64-type| i$0]
#check [llvm-64-type| i8()]
#check [llvm-64-type| i8(i32, i16)]
#check [llvm-64-type| void(i32, i16)]

#check [llvm-exp| %1]
#check [llvm-exp| %a]
#check [llvm-exp| true]
#check [llvm-exp| false]
#check [llvm-exp| 123]
#check [llvm-exp| null]
#check [llvm-exp| undef]
#check [llvm-exp| poison]

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

#check [llvm-instruction| add i8 %1, %3]
#check [llvm-64-0-instruction| add nuw i8 %1, %a]
#check [llvm-64-0-instruction| trunc nuw i32 %b to i8]
#check [llvm-64-0-instruction| zext i8 %b to i16]
#check [llvm-64-0-instruction| freeze i8 %1]
#check [llvm-64-10-instruction| add i8 undef, undef]

#check [llvm-terminator| ret void]
#check [llvm-64-terminator| ret i8 %1]

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

#check [llvm-entity| declare i32 @puts(i8, i32)]

#check [llvm-64-entity|
define void @f() {
entry:
  %1 = add i8 %0, %a
  %d = add i8 %2, %b
  freeze i8 %1
  ret void
}
]

#check [llvm-2|
declare i32 @puts(i8, i32)
define void @g(i8 %a) {
entry:
  %1 = add i8 %0, %a
  %d = add i8 %2, %b
  freeze i8 %1
  ret void
}
declare i32 @gets(i8, i32)
define void @f() {
entry:
  %1 = add i8 %0, %a
  %d = add i8 %2, %b
  freeze i8 %1
  ret void
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

#check [llvm|
declare i32 @g(i32, i8)
]

#check [llvm|
declare i32 @g(i32, i8)
declare i32 @g(i32, i8)
declare i32 @g2(i32, i8)
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


end
