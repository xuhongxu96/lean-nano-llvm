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
def llvm_0_plus_1 : TopLevel := ⟨[
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
#check fun (w : Nat) => [llvm-type| i$(w)]
#check fun (w : Nat) => [llvm-type| i$(w + 1)]
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
#check [llvm-type| i8()]
#check [llvm-type| i8(i32, i16)]
#check [llvm-type| void(i32, i16)]
#check [llvm-type| i32(ptr, ...)]

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

#check fun (temp : Int) => [llvm-exp| <temp:int>]

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
#check [llvm-instruction| add nuw i8 %1, %a]
#check [llvm-instruction| trunc nuw i32 %b to i8]
#check [llvm-instruction| zext i8 %b to i16]
#check [llvm-instruction| freeze i8 %1]
#check [llvm-instruction| add i8 undef, undef]
#check [llvm-instruction| fadd nnan ninf float 1.5, 2.5]
#check [llvm-instruction| fneg nsz double -0.0]
#check [llvm-instruction| icmp slt i32 %a, 10]
#check [llvm-instruction| fcmp oeq float %a, %b]
#check [llvm-instruction| select i1 %c, i32 %a, i32 %b]
#check [llvm-instruction| alloca i32, align 4]
#check [llvm-instruction| alloca i32, i64 4, align 8]
#check [llvm-instruction| load i32, ptr %p, align 4, !noundef]
#check [llvm-instruction| load volatile i32, ptr %p, !noundef]
#check [llvm-instruction| store volatile i32 42, ptr %p, align 4]
#check [llvm-instruction| getelementptr inbounds { i32, i64 }, ptr %p, i64 0, i32 1]
#check [llvm-instruction| extractvalue { i32, i64 } %s, 1]
#check [llvm-instruction| insertvalue { i32, i64 } %s, i64 9, 1]
#check [llvm-instruction| extractelement <4 x i32> %v, i32 2]
#check [llvm-instruction| insertelement <4 x i32> %v, i32 7, i32 1]
#check [llvm-instruction| shufflevector <2 x i32> %v1, <2 x i32> %v2, <2 x i32> <i32 1, i32 2>]
#check [llvm-instruction| call noundef i32 @helper(i32 noundef %a, ptr nonnull align 4 %p)]

#check [llvm-terminator| ret void]
#check [llvm-terminator| ret i8 %1]
#check [llvm-terminator| br label %next]
#check [llvm-terminator| br i1 %c, label %t, label %f]
#check [llvm-terminator| switch i32 %v, label %dflt [ i32 0, label %l0 i32 1, label %l1 ]]
#check [llvm-terminator| unreachable]

#check [llvm-declaration| declare i32 @puts(i8, i32)]
#check [llvm-declaration| declare noundef i32 @printf(ptr nonnull, ...)]

#check [llvm-codeline| %1 = add i8 %0, %a]
#check [llvm-codeline| freeze i8 %a]

#check [llvm-code|
%1 = add i8 %0, %a
%d = add i8 %2, %b
freeze i8 %1
]

#check [llvm-block|
entry:
  %1 = add i8 %0, %a
  %d = add i8 %2, %b
  freeze i8 %1
  ret void
]

#check [llvm-definition|
define void @f() {
entry:
  %1 = add i8 %0, %a
  %d = add i8 %2, %b
  freeze i8 %1
  ret void
}
]

#check fun (w : Nat) => [llvm-definition|
define i$(w) @f(i$(w) %a) {
entry:
  %1 = add i$(w) %a, 0
  ret i$(w) %1
}
]

#check [llvm-definition|
define noundef i32 @with_attrs(ptr nonnull dereferenceable(4) %p, i32 range(0, 10) %x) {
entry:
  ret i32 %x
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

-- Phase 2 syntax tests: named struct types, load metadata, sret/noalias/readonly, constexprs
#check [llvm-type| %Pair]
#check [llvm-instruction| load ptr, ptr %p, align 8, !nonnull]
#check [llvm-instruction| load i32, ptr %p, align 4, !range(0, 10), !noundef]
#check [llvm-exp| getelementptr inbounds (i32, ptr @g, i64 2)]
#check [llvm-exp| ptrtoint (ptr @g to i64)]
#check [llvm-exp| add (i32 1, i32 2)]
#check [llvm-definition|
define void @use_attrs(ptr sret(i32) noalias readonly %out) {
entry:
  ret void
}
]
#check [llvm|
%Pair = type { i32, i64 }
define i64 @get_snd(ptr %p) {
entry:
  %q = getelementptr inbounds %Pair, ptr %p, i64 0, i32 1
  %v = load i64, ptr %q, align 8
  ret i64 %v
}
]

end
