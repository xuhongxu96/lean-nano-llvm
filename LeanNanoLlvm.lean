import LeanNanoLlvm.Util
import LeanNanoLlvm.AST
import LeanNanoLlvm.Semantics
import LeanNanoLlvm.Tactic
import LeanNanoLlvm.Refinement
import LeanNanoLlvm.Run
import LeanNanoLlvm.Llubi

/-!
# LeanNanoLlvm

A formal semantics of LLVM IR in Lean 4: the syntax (`AST`), a relational small-step semantics
with a kernel-reducible interpreter proven sound against it (`Semantics`), program refinement
(`Refinement`), and two executable frontends, `lean-nano-llvm run` (`Run`) and the
`llubi`-compatible `lean-nano-llvm llubi` (`Llubi`). See `README.md` for the module layout.
-/
