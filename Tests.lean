import Tests.AST
import Tests.Unexpander
import Tests.Semantics
import Tests.Refinement

/-!
# Test suites

Kernel-checked tests (`decide +kernel`, `#guard`, and proofs), kept out of the `LeanNanoLlvm`
library. `lake build` builds them as a default target.

* `Tests.AST`: parser, syntax elaborators, and printer.
* `Tests.Unexpander`: round-trip unexpander checks (DSL, direct AST, `.ll` files) and formatting snapshots.
* `Tests.Semantics`: execution of concrete programs and semantic lemmas.
* `Tests.Refinement`: refinement proofs between programs.
-/
