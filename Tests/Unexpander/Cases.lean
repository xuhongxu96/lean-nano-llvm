import Lean
import LeanNanoLlvm.AST
import Tests.Unexpander.Harness

/-! Unexpander round-trip cases and formatting snapshots (harness in `Tests.Unexpander.Harness`). -/

namespace Tests.Unexpander

open Lean Elab Command Term Meta PrettyPrinter
open LeanNanoLlvm.AST

open scoped LeanNanoLlvm.AST.Syntax

/-! ### Identifiers & RawIds -/

#test_unexpand [llvm-rawid| 0]
#test_unexpand [llvm-rawid| 42]
#test_unexpand [llvm-rawid| entry]
#test_unexpand [llvm-rawid| ".fmt"]
#test_unexpand [llvm-rawid| "llvm.vscale.i32"]
#test_unexpand [llvm-rawid| "type"]

#test_unexpand [llvm-identifier| @1]
#test_unexpand [llvm-identifier| %19]
#test_unexpand [llvm-identifier| @abc]
#test_unexpand [llvm-identifier| %xyz]
#test_unexpand [llvm-identifier| @".fmt"]
#test_unexpand [llvm-identifier| %"a.b-c"]

#test_unexpand [llvm-instruction-id| %a]
#test_unexpand [llvm-instruction-id| %2]
#test_unexpand [llvm-instruction-id| void (3)]

/-! ### Types -/

#test_unexpand [llvm-type| i1]
#test_unexpand [llvm-type| i8]
#test_unexpand [llvm-type| i64]
#test_unexpand fun (w : Nat) => [llvm-type| i$(w)]
#test_unexpand fun (w : Nat) => [llvm-type| i$(w + 1)]
#test_unexpand [llvm-type| b8]
#test_unexpand [llvm-type| b32]
#test_unexpand [llvm-type| b128]
#test_unexpand fun (w : Nat) => [llvm-type| b$(w)]
#test_unexpand [llvm-type| half]
#test_unexpand [llvm-type| bfloat]
#test_unexpand [llvm-type| float]
#test_unexpand [llvm-type| double]
#test_unexpand [llvm-type| x86_fp80]
#test_unexpand [llvm-type| fp128]
#test_unexpand [llvm-type| ppc_fp128]
#test_unexpand [llvm-type| ptr]
#test_unexpand [llvm-type| ptr addrspace(1)]
#test_unexpand [llvm-type| <4 x i32>]
#test_unexpand [llvm-type| [2 x float]]
#test_unexpand [llvm-type| { i32, i64 }]
#test_unexpand [llvm-type| <{ i8, i32 }>]
#test_unexpand [llvm-type| %Pair]
#test_unexpand [llvm-type| i8()]
#test_unexpand [llvm-type| i8(i32, i16)]
#test_unexpand [llvm-type| void(i32, i16)]
#test_unexpand [llvm-type| i32(ptr, ...)]

/-! ### Expressions & Constants -/

#test_unexpand [llvm-exp| %1]
#test_unexpand [llvm-exp| %a]
#test_unexpand [llvm-exp| @g]
#test_unexpand [llvm-exp| true]
#test_unexpand [llvm-exp| false]
#test_unexpand [llvm-exp| 0]
#test_unexpand [llvm-exp| 123]
#test_unexpand [llvm-exp| -42]
#test_unexpand [llvm-exp| 1.5]
#test_unexpand [llvm-exp| -2.25]
#test_unexpand [llvm-exp| -0.0]
#test_unexpand [llvm-exp| 1.434929627468612680625899e-42]
#test_unexpand [llvm-exp| fbits(0x3F800000)]
#test_unexpand [llvm-exp| fspecial(+inf)]
#test_unexpand [llvm-exp| fspecial(-inf)]
#test_unexpand [llvm-exp| fspecial(+qnan)]
#test_unexpand [llvm-exp| fspecial(-qnan(42))]
#test_unexpand [llvm-exp| fspecial(+snan)]
#test_unexpand [llvm-exp| fspecial(-snan(7))]
#test_unexpand [llvm-exp| blockaddress(@main, %target)]
#test_unexpand [llvm-exp| null]
#test_unexpand [llvm-exp| zeroinitializer]
#test_unexpand [llvm-exp| undef]
#test_unexpand [llvm-exp| poison]
#test_unexpand [llvm-exp| <i32 1, i32 2>]
#test_unexpand [llvm-exp| [i32 10, i32 20]]
#test_unexpand [llvm-exp| { i32 1, float 2.0 }]
#test_unexpand [llvm-exp| <{ i8 1, i32 2 }>]
#test_unexpand [llvm-exp| splat (i32 7)]
#test_unexpand [llvm-exp| getelementptr inbounds (i32, ptr @g, i64 2)]
#test_unexpand [llvm-exp| getelementptr nusw nuw (i32, ptr @g, i64 1, i32 0)]
#test_unexpand [llvm-exp| ptrtoint (ptr @g to i64)]
#test_unexpand [llvm-exp| ptrtoaddr (ptr @g to i64)]
#test_unexpand [llvm-exp| inttoptr (i64 16 to ptr)]
#test_unexpand [llvm-exp| bitcast (i32 1 to float)]
#test_unexpand [llvm-exp| add (i32 1, i32 2)]
#test_unexpand [llvm-exp| sub nuw nsw (i32 5, i32 3)]
#test_unexpand [llvm-exp| insertelement (<2 x i32> zeroinitializer, i32 9, i32 1)]
#test_unexpand [llvm-exp| extractelement (<2 x i32> <i32 1, i32 2>, i32 0)]
#test_unexpand [llvm-exp| shufflevector (<2 x i32> <i32 1, i32 2>, <2 x i32> poison, <2 x i32> <i32 1, i32 poison>)]
#test_unexpand fun (temp : Int) => [llvm-exp| <temp:int>]

/-! ### Operators -/

#test_unexpand [llvm-int-bin-op| add]
#test_unexpand [llvm-int-bin-op| add nuw]
#test_unexpand [llvm-int-bin-op| add nsw]
#test_unexpand [llvm-int-bin-op| add nuw nsw]
#test_unexpand [llvm-int-bin-op| sub nuw]
#test_unexpand [llvm-int-bin-op| mul nsw]
#test_unexpand [llvm-int-bin-op| shl nuw nsw]
#test_unexpand [llvm-int-bin-op| udiv]
#test_unexpand [llvm-int-bin-op| udiv exact]
#test_unexpand [llvm-int-bin-op| sdiv exact]
#test_unexpand [llvm-int-bin-op| lshr exact]
#test_unexpand [llvm-int-bin-op| ashr exact]
#test_unexpand [llvm-int-bin-op| urem]
#test_unexpand [llvm-int-bin-op| srem]
#test_unexpand [llvm-int-bin-op| and]
#test_unexpand [llvm-int-bin-op| or]
#test_unexpand [llvm-int-bin-op| or disjoint]
#test_unexpand [llvm-int-bin-op| xor]

#test_unexpand [llvm-conversion-op| trunc]
#test_unexpand [llvm-conversion-op| trunc nuw]
#test_unexpand [llvm-conversion-op| trunc nsw]
#test_unexpand [llvm-conversion-op| trunc nuw nsw]
#test_unexpand [llvm-conversion-op| zext]
#test_unexpand [llvm-conversion-op| zext nneg]
#test_unexpand [llvm-conversion-op| sext]
#test_unexpand [llvm-conversion-op| fptrunc]
#test_unexpand [llvm-conversion-op| fptrunc nnan ninf]
#test_unexpand [llvm-conversion-op| fpext fast]
#test_unexpand [llvm-conversion-op| fptoui]
#test_unexpand [llvm-conversion-op| fptosi]
#test_unexpand [llvm-conversion-op| uitofp]
#test_unexpand [llvm-conversion-op| uitofp nneg nsz]
#test_unexpand [llvm-conversion-op| sitofp contract]
#test_unexpand [llvm-conversion-op| ptrtoint]
#test_unexpand [llvm-conversion-op| ptrtoaddr]
#test_unexpand [llvm-conversion-op| inttoptr]
#test_unexpand [llvm-conversion-op| bitcast]
#test_unexpand [llvm-conversion-op| addrspacecast]

/-! ### Instructions -/

#test_unexpand [llvm-instruction| add i8 %1, %3]
#test_unexpand [llvm-instruction| add nuw i8 %1, %a]
#test_unexpand [llvm-instruction| trunc nuw i32 %b to i8]
#test_unexpand [llvm-instruction| zext i8 %b to i16]
#test_unexpand [llvm-instruction| freeze i8 %1]
#test_unexpand [llvm-instruction| add i8 undef, undef]
#test_unexpand [llvm-instruction| fadd nnan ninf float 1.5, 2.5]
#test_unexpand [llvm-instruction| fsub fast double %a, %b]
#test_unexpand [llvm-instruction| fmul arcp contract float %a, %b]
#test_unexpand [llvm-instruction| fdiv afn reassoc float %a, %b]
#test_unexpand [llvm-instruction| frem float %a, %b]
#test_unexpand [llvm-instruction| fneg nsz double -0.0]
#test_unexpand [llvm-instruction| icmp slt i32 %a, 10]
#test_unexpand [llvm-instruction| icmp samesign ult i32 %a, %b]
#test_unexpand [llvm-instruction| fcmp oeq float %a, %b]
#test_unexpand [llvm-instruction| fcmp nnan ugt float %a, %b]
#test_unexpand [llvm-instruction| select i1 %c, i32 %a, i32 %b]
#test_unexpand [llvm-instruction| select fast i1 %c, float %a, float %b]
#test_unexpand [llvm-instruction| phi i32 [ 1, %left ], [ 2, %right ]]
#test_unexpand [llvm-instruction| phi nnan float [ 1.5, %left ], [ 2.5, %right ], !nonnull]
#test_unexpand [llvm-instruction| alloca i32, align 4]
#test_unexpand [llvm-instruction| alloca i32, i64 4, align 8, addrspace(1)]
#test_unexpand [llvm-instruction| load i32, ptr %p, align 4, !noundef]
#test_unexpand [llvm-instruction| load volatile i32, ptr %p, !noundef]
#test_unexpand [llvm-instruction| load ptr, ptr %p, align 8, !nonnull]
#test_unexpand [llvm-instruction| load i32, ptr %p, align 4, !range(0, 10), !noundef]
#test_unexpand [llvm-instruction| load i32, ptr %p, !range_list(0, 5, 10, 20)]
#test_unexpand [llvm-instruction| store volatile i32 42, ptr %p, align 4]
#test_unexpand [llvm-instruction| getelementptr inbounds { i32, i64 }, ptr %p, i64 0, i32 1]
#test_unexpand [llvm-instruction| getelementptr nusw nuw %Pair, ptr %p, i64 0, i32 1]
#test_unexpand [llvm-instruction| extractvalue { i32, i64 } %s, 1]
#test_unexpand [llvm-instruction| insertvalue { i32, i64 } %s, i64 9, 1]
#test_unexpand [llvm-instruction| extractelement <4 x i32> %v, i32 2]
#test_unexpand [llvm-instruction| insertelement <4 x i32> %v, i32 7, i32 1]
#test_unexpand [llvm-instruction| shufflevector <2 x i32> %v1, <2 x i32> %v2, <2 x i32> <i32 1, i32 poison>]
#test_unexpand [llvm-instruction| call noundef i32 @helper(i32 noundef %a, ptr nonnull align 4 %p)]
#test_unexpand [llvm-instruction| tail call fast cc "fastcc" i32 @callee(i32 %x) ["align"(ptr %p, i64 4)] noreturn]
#test_unexpand [llvm-instruction| bitinsert b128 0, ptr %slot, i32 32]
#test_unexpand [llvm-instruction| bitextract i8, b32 %b, i32 8]

/-! ### Terminators -/

#test_unexpand [llvm-terminator| ret void]
#test_unexpand [llvm-terminator| ret i8 %1]
#test_unexpand [llvm-terminator| br label %next]
#test_unexpand [llvm-terminator| br i1 %c, label %t, label %f]
#test_unexpand [llvm-terminator| switch i32 %v, label %dflt [ i32 -1, label %l0 i32 1, label %l1 ]]
#test_unexpand [llvm-terminator| indirectbr ptr %addr, [ label %l0, label %l1 ]]
#test_unexpand [llvm-terminator| unreachable]

/-! ### Declarations, Blocks, Definitions, Globals & Modules -/

#test_unexpand [llvm-declaration| declare i32 @puts(i8, i32)]
#test_unexpand [llvm-declaration| declare noundef i32 @printf(ptr nonnull, ...)]
#test_unexpand [llvm-declaration| declare cc "fastcc" void @die(i32) noreturn nobuiltin denormal_fpenv(positivezero|preservesign)]

#test_unexpand [llvm-code|
%1 = add i8 %0, %a
%d = add i8 %2, %b
freeze i8 %1
]

#test_unexpand [llvm-block|
entry:
  %1 = add i8 %0, %a
  %d = add i8 %2, %b
  freeze i8 %1
  ret void
]

#test_unexpand [llvm-definition|
define void @f() {
entry:
  %1 = add i8 %0, %a
  %d = add i8 %2, %b
  freeze i8 %1
  ret void
}
]

#test_unexpand fun (w : Nat) => [llvm-definition|
define i$(w) @f(i$(w) %a) {
entry:
  %1 = add i$(w) %a, 0
  ret i$(w) %1
}
]

#test_unexpand [llvm-definition|
define noundef i32 @with_attrs(ptr nonnull dereferenceable(4) %p, i32 range(0, 10) %x) {
entry:
  ret i32 %x
}
]

#test_unexpand [llvm-definition|
define void @use_attrs(ptr sret(i32) noalias readonly %out, ptr byval(i64) dereferenceable_or_null(8) %inp, float nofpclass(3) %f) {
entry:
  ret void
}
]

#test_unexpand [llvm-definition|
define cc "fastcc" i32 @multi_block(i1 %c) denormal_fpenv(positivezero|positivezero) {
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

#test_unexpand [llvm|
%Pair = type { i32, i64 }
@g = global i32 42, align 4
@c = addrspace(1) constant float 1.5
declare i32 @puts(i8, i32)
define i64 @get_snd(ptr %p) {
entry:
  %q = getelementptr inbounds %Pair, ptr %p, i64 0, i32 1
  %v = load i64, ptr %q, align 8
  ret i64 %v
}
]

/-! ### Direct Lean AST Construction (Proof-State / Default-Field Shapes) -/

#test_unexpand (LlvmType.i32)
#test_unexpand (LlvmType.f64)
#test_unexpand (Exp.int (Int.negSucc 41))
#test_unexpand (Instruction.fcmp FastMathFlags.none .oeq .f32 (.identifier (.local_id (.name "a"))) (.identifier (.local_id (.name "b"))))
#test_unexpand (Instruction.select FastMathFlags.fast .i1 (.bool true) .i32 (.int 1) (.int 2))
#test_unexpand (Instruction.getelementptr GEPFlags.mkInbounds .i32 (.ptr 0) (.identifier (.local_id (.name "p"))) [(.i64, .int 0)])
#test_unexpand (Instruction.call (.ret .i32) {} (.identifier (.global_id (.name "f"))) [] [] [] false
  { fnTy? := some (.function (.ret .i32) [] false) })
#test_unexpand (Instruction.call (.ret .i32) {} (.identifier (.global_id (.name "printf")))
  [(.ptr 0, .identifier (.local_id (.name "s")), []), (.i32, .int 1, [])] [] [] false
  { fnTy? := some (.function (.ret .i32) [.ptr 0] true) })
#test_unexpand_canon (TopLevel.mk [
  .definition {
    prototype := {
      name := .name "f",
      «type» := .function (.ret .i32) []
    },
    args := [],
    blocks := [{
      id := .name "B",
      code := [
        ⟨.id (.name "i0"), .intBinaryOp (.add false false) .i32 (.int 0) (.int 1)⟩
      ],
      terminator := ⟨.void 0, .ret ⟨.i32, (.identifier (.local_id (.name "i0")))⟩⟩
    }]
  }
])

/-! ### Parsed `.ll` Regression Suite Round-Trips -/

#test_unexpand_ll_file "Tests/ll/attrs_assume.ll"
#test_unexpand_ll_file "Tests/ll/bitextract_poison_ub.ll"
#test_unexpand_ll_file "Tests/ll/br_poison_ub.ll"
#test_unexpand_ll_file "Tests/ll/bytes_vscale_fp.ll"
#test_unexpand_ll_file "Tests/ll/byval_copy.ll"
#test_unexpand_ll_file "Tests/ll/cf_libcalls.ll"
#test_unexpand_ll_file "Tests/ll/fib.ll"
#test_unexpand_ll_file "Tests/ll/fp_denorm_ppc128.ll"
#test_unexpand_ll_file "Tests/ll/fp_intrinsics.ll"
#test_unexpand_ll_file "Tests/ll/load_range_ub.ll"
#test_unexpand_ll_file "Tests/ll/loop_phi.ll"
#test_unexpand_ll_file "Tests/ll/named_struct_global.ll"
#test_unexpand_ll_file "Tests/ll/speculative_load_oracle.ll"
#test_unexpand_ll_file "Tests/ll/undef_zero.ll"
#test_unexpand_ll_file "Tests/ll/vec_intrinsics.ll"
#test_unexpand_ll_file "Tests/ll/wildcard_multiobj_ub.ll"

/-! ### Formatting & Hygiene Snapshots (`#guard_msgs`) -/

/-- info: [llvm-type|ptr addrspace(1)] : LlvmType -/
#guard_msgs in
#check [llvm-type| ptr addrspace(1)]

/-- info: [llvm-type|<4 x i32>] : LlvmType -/
#guard_msgs in
#check [llvm-type| <4 x i32>]

/-- info: [llvm-exp|true] : Exp -/
#guard_msgs in
#check [llvm-exp| true]

/-- info: [llvm-exp|false] : Exp -/
#guard_msgs in
#check [llvm-exp| false]

/-- info: [llvm-int-bin-op|add nuw] : IntBinaryOp -/
#guard_msgs in
#check [llvm-int-bin-op| add nuw]

/-- info: [llvm-instruction|getelementptr inbounds {i32, i64}, ptr %p, i64 0, i32 1] : Instruction -/
#guard_msgs in
#check [llvm-instruction| getelementptr inbounds { i32, i64 }, ptr %p, i64 0, i32 1]

/--
info: fun w =>
  [llvm-definition|define i$(w) @f(i$(w) %a) {
  entry:
      %1 = add i$(w) %a, 0
      ret i$(w) %1
  }] : Nat → Definition
-/
#guard_msgs in
#check fun (w : Nat) => [llvm-definition|
define i$(w) @f(i$(w) %a) {
entry:
  %1 = add i$(w) %a, 0
  ret i$(w) %1
}
]

end Tests.Unexpander
