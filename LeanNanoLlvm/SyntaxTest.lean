import LeanNanoLlvm.Syntax

open LeanNanoLlvm.Syntax

#check ([.global {
  id := .name "G",
  type := .int 8,
  isConstant := true,
  exp := .none
}] : TopLevel)

#check ([
  .definition {
    prototype := {
      name := .name "f",
      type := .function .void []
    },
    args := [],
    body := {
      id := .name "B",
      code := [],
      terminator := ⟨.void 0, .retVoid⟩
    }
  }
] : TopLevel)
