import LeanNanoLlvm.AST

section
open LeanNanoLlvm.AST

/-
define i32 @f() {
B:
  %i0 = add i32 0, 1
  ret i32 %i0
} -/
def llvm_0_plus_1 : TopLevel 32 := ⟨[
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

elab "test_elabNanoLlvmRawId " e:nanollvm_rawid : term => elabNanoLlvmRawId e
#reduce test_elabNanoLlvmRawId 1
#reduce test_elabNanoLlvmRawId a

elab "test_elabNanoLlvmIdentifier " e:nanollvm_identifier : term => elabNanoLlvmIdentifier e
#reduce test_elabNanoLlvmIdentifier @1
#reduce test_elabNanoLlvmIdentifier %19
#reduce test_elabNanoLlvmIdentifier @abc
#reduce test_elabNanoLlvmIdentifier %xyz

elab "test_elabNanoLlvmType " e:nanollvm_type : term => elabNanoLlvmType 64 e
#reduce test_elabNanoLlvmType i8
#reduce test_elabNanoLlvmType i8()
#reduce test_elabNanoLlvmType i8(i32, i16)
#reduce test_elabNanoLlvmType void(i32, i16)

elab "test_elabNanoLlvmExp " e:nanollvm_exp : term => elabNanoLlvmExp e
#reduce test_elabNanoLlvmExp %1
#reduce test_elabNanoLlvmExp %a
#reduce test_elabNanoLlvmExp true
#reduce test_elabNanoLlvmExp false
#reduce test_elabNanoLlvmExp 123
#reduce test_elabNanoLlvmExp null
#reduce test_elabNanoLlvmExp undef
#reduce test_elabNanoLlvmExp poison

elab "test_elabNanoLlvmIntBinOp " e:nanollvm_int_bin_op : term => elabNanoLlvmIntBinOp e
#reduce test_elabNanoLlvmIntBinOp add
#reduce test_elabNanoLlvmIntBinOp add nuw
#reduce test_elabNanoLlvmIntBinOp add nsw
#reduce test_elabNanoLlvmIntBinOp add nuw nsw
#reduce test_elabNanoLlvmIntBinOp xor
#reduce test_elabNanoLlvmIntBinOp or disjoint

elab "test_elabNanoLlvmConversionOp" e:nanollvm_conversion_op : term => elabNanoLlvmConversionOp e
#reduce test_elabNanoLlvmConversionOp sext
#reduce test_elabNanoLlvmConversionOp trunc nuw
#reduce test_elabNanoLlvmConversionOp trunc

elab "test_elabNanoLlvmInstruction" e:nanollvm_instruction : term => elabNanoLlvmInstruction 64 e
#reduce test_elabNanoLlvmInstruction add i8 %1, %3
#reduce test_elabNanoLlvmInstruction add nuw i8 %1, %a
#reduce test_elabNanoLlvmInstruction trunc nuw i32 %b to i8
#reduce test_elabNanoLlvmInstruction zext i8 %b to i16
#reduce test_elabNanoLlvmInstruction freeze i8 %1

elab "test_elabNanoLlvmTerminator" e:nanollvm_terminator : term => elabNanoLlvmTerminator 64 e
#reduce test_elabNanoLlvmTerminator ret void
#reduce test_elabNanoLlvmTerminator ret i8 %1

elab "test_elabNanoLlvmDeclaration" e:nanollvm_declaration : term => elabNanoLlvmDeclaration 64 e
#reduce test_elabNanoLlvmDeclaration declare i32 @puts(i8, i32)

elab "test_elabNanoLlvmCodeline" e:nanollvm_codeline : term => elabNanoLlvmCodeline 64 1 e
#reduce test_elabNanoLlvmCodeline %1 = add i8 %0, %a
#reduce test_elabNanoLlvmCodeline freeze i8 %a

elab "test_elabNanoLlvmCode " e:nanollvm_code: term => do pure (← elabNanoLlvmCode 64 1 e).fst
#reduce test_elabNanoLlvmCode %1 = add i8 %0, %a
                              %d = add i8 %2, %b
                              freeze i8 %1

elab "test_elabNanoLlvmBlock " e:nanollvm_block: term => elabNanoLlvmBlock 64 1 e
#reduce test_elabNanoLlvmBlock entry:
                                %1 = add i8 %0, %a
                                %d = add i8 %2, %b
                                freeze i8 %1
                                ret void

elab "test_elabNanoLlvmDefinition " e:nanollvm_definition: term => elabNanoLlvmDefinition 64 e
#reduce test_elabNanoLlvmDefinition
define void @f() {
entry:
  %1 = add i8 %0, %a
  %d = add i8 %2, %b
  freeze i8 %1
  ret void
}

elab "test_elabNanoLlvm " e:nanollvm : term => elabNanoLlvm 64 e
#reduce test_elabNanoLlvm
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
