import LeanNanoLlvm.Syntax
import LeanNanoLlvm.Print

open LeanNanoLlvm.Syntax

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
