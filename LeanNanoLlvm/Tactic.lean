import Lean.Meta.Tactic.Simp.RegisterCommand

/-! ### Layered `simp` Attributes for LLVM Formalization

- `simp_llvm`     : Pure LLVM value, poison, bitvector, and integer-operation algebra.
- `simp_wellform` : AST, definition, and argument well-formedness predicates.
- `simp_step`     : Small-step machine, frame, register-map, and leaf-expression reductions
                    (intentionally excludes `initCallConfig` / `mkEntryFrame` so call-entry
                    rewrite lemmas apply cleanly).
-/

register_simp_attr simp_llvm
register_simp_attr simp_wellform
register_simp_attr simp_step

/-! ### Convenience Tactics -/

/-- Simplify pure LLVM value, poison, and integer-operation expressions using `simp_llvm`. -/
syntax "llvm_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| llvm_simp) =>
    `(tactic| simp [simp_llvm])
  | `(tactic| llvm_simp [$ls,*]) =>
    `(tactic| simp [simp_llvm, $ls,*])
  | `(tactic| llvm_simp $loc:location) =>
    `(tactic| simp [simp_llvm] $loc:location)
  | `(tactic| llvm_simp [$ls,*] $loc:location) =>
    `(tactic| simp [simp_llvm, $ls,*] $loc:location)

/-- Simplify well-formedness obligations (`WellFormed`, `ArgValuesWellFormed`, etc.) using `simp_wellform`. -/
syntax "llvm_wf" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| llvm_wf) =>
    `(tactic| simp [simp_wellform])
  | `(tactic| llvm_wf [$ls,*]) =>
    `(tactic| simp [simp_wellform, $ls,*])
  | `(tactic| llvm_wf $loc:location) =>
    `(tactic| simp [simp_wellform] $loc:location)
  | `(tactic| llvm_wf [$ls,*] $loc:location) =>
    `(tactic| simp [simp_wellform, $ls,*] $loc:location)

/-- Simplify small-step machine, frame, register-map, and leaf-evaluation terms using `simp_step`. -/
syntax "llvm_step" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| llvm_step) =>
    `(tactic| simp [simp_step])
  | `(tactic| llvm_step [$ls,*]) =>
    `(tactic| simp [simp_step, $ls,*])
  | `(tactic| llvm_step $loc:location) =>
    `(tactic| simp [simp_step] $loc:location)
  | `(tactic| llvm_step [$ls,*] $loc:location) =>
    `(tactic| simp [simp_step, $ls,*] $loc:location)
