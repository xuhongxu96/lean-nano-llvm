import LeanNanoLlvm.AST

section
open LeanNanoLlvm.AST

/-
define i32 f() {
  %i0 = add i32 0, 1
  ret i32 %i0
} -/
def llvm_0_plus_1 : TopLevel 32 := [
  .definition {
    prototype := {
      name := .name "f",
      type := .function (.ret .i32) []
    },
    args := [],
    body := {
      id := .name "B",
      code := [
        ⟨.id (.name "i0"), .intBinaryOp (.add false false) .i32 (.int 0) (.int 1)⟩
      ],
      terminator := ⟨.void 0, .ret ⟨.i32, (.identifier (.local_id (.name "i0")))⟩⟩
    }
  }
]

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

end
