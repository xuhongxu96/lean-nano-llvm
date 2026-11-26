# lean-nano-llvm

Zero-dependency Lean 4 formalization of an executable, almost-complete LLVM IR subset with parsing, printing, unexpansion, data layouts, well-formedness, bit-level small-step operational semantics (aligned with LLVM's `llubi` reference interpreter), a proven-sound kernel-reducible interpreter, configurable `undef` support, and full behavioral refinement proofs.

At the core, this project lets you write LLVM IR programs directly in Lean using quasiquotations (including arbitrary bitwidth antiquotation `i$(w)`) and formally prove program optimizations and semantic properties inside Lean's kernel using only standard axioms.

```lean
theorem ret_add_x_0_is_refined_by_ret_x_generic (w : Nat) :
  [llvm-definition|
    define i$(w) @f(i$(w) %x) {
    entry:
      %x = add i$(w) %x, 0
      ret i$(w) %x
    }
  ] ⊒ [llvm-definition|
    define i$(w) @f(i$(w) %x) {
    entry:
      ret i$(w) %x
    }
  ] := by
  -- ...
```

## Highlights

- **Pure, Zero-Dependency Lean 4**:
  - Builds directly with Lean 4 (v4.28.0) and zero external package dependencies (no Mathlib required).
  - Every theorem and test in the repository uses only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) — zero `sorry`, zero `native_decide`.
- **Inductive Small-Step Specification + Proven-Sound Executable Interpreter**:
  - Primary semantics is a 3-tier indexed small-step relation `Step : Config → Option TraceEvent → Config → Prop` (`LeanNanoLlvm/Semantics/Step.lean`) with relational nondeterminism (`MemoryState.AllocSpec`, `FreezeRel`, `UndefValRel`, `BytesToValueRel`), observable volatile/external `TraceEvent`s, and no fuel or oracle artifacts in the specification.
  - A separate kernel-reducible executable driver (`LeanNanoLlvm/Semantics/Exec.lean`: `execStep`, `runSteps`, `runDefinition`, `runModuleFunction`, `runCode`) evaluates concrete LLVM IR inside Lean's kernel (`decide +kernel`) and is formally proven sound against `Step` / `StarStep` (`execStep_sound`, `runSteps_sound`).
- **Full Behavioral Refinement, Coinductive Simulation & Module-Aware Contexts**:
  - `Config.IsRefinedBy` (`LeanNanoLlvm/Refinement/Refinement.lean`) provides the core configuration-level refinement relation, plus reusable proof combinators: `of_simulation` (for arbitrary loops/CFGs via `PlusStep` progress and `MemoryInjection.Extends` monotonicity), `of_det_halted`, `of_step_left`, `of_starStep_left`, `of_det_step_right`, `of_det_step_both`, and `of_common_tail`.
  - `RefinementEnv` (`RefinementEnv.ofTopLevel`) and `Definition.IsRefinedByIn` (`x ⊒⟨env⟩ y`) support interprocedural refinement inside a module's helper definitions, declarations, and `DataLayout`, with `Definition.IsRefinedByWith` (`x ⊒[cfg] y`, defaulting to `x ⊒ y` under `SemanticsConfig.modern`) as a lightweight abbreviation.
  - Unconditional reflexivity (`refl`) and transitivity (`trans`, integrated with Lean's core `Trans` typeclass for native `calc` chaining), supported by three layered simp sets and tactics (`llvm_simp` / `simp_llvm`, `llvm_wf` / `simp_wellform`, `llvm_step` / `simp_step` in `LeanNanoLlvm/Tactic.lean`).
- **Optional, Switchable `undef` (`SemanticsConfig.undefMode`)**:
  - Defaults to `SemanticsConfig.modern` (`undefMode := .disabled`), matching LLVM's ongoing deprecation of `undef` (`Exp.undef` is rejected in well-formedness and execution, and uninitialized memory/padding is `poison`).
  - Explicitly opt into legacy `undef` with `SemanticsConfig.withUndef` (`undefMode := .nondet`), deterministic zero-fill with `SemanticsConfig.deterministic`, or `SemanticsConfig.legacyCompat`.
- **Bit-Level Memory & Provenance Model** (`LeanNanoLlvm/Semantics/Memory.lean`, `LeanNanoLlvm/AST/DataLayout.lean`):
  - Exact per-bit provenance (`MemBit`), little-endian & big-endian `DataLayout` (`default64LE`, `default64BE`, `default32LE`), unpacked/packed/named struct layouts (`%T = type { ... }`), sub-byte integer padding canonicalization, volatile memory events, and `load` metadata (`!noundef`, `!nonnull`, `!range`).
  - `alloca`, `load`, `store`, `getelementptr` (`inbounds`/`nusw`/`nuw`), `ptrtoint` vs `ptrtoaddr` exposed provenance generations, `inttoptr`, `addrspacecast`, `bitcast`.
  - Stack frame allocation & dangling-pointer detection, `byval(T)` callee stack-copy isolation, `llvm.lifetime.start`/`end`, heap `malloc`/`calloc`/`free`, `llvm.memcpy`/`memmove`/`memset`, and mutable/`constant` globals.
- **Kernel-Reducible IEEE-754 Floating-Point Engine** (`LeanNanoLlvm/Util/IEEEFloat.lean`, `LeanNanoLlvm/Semantics/FloatOps.lean`):
  - Pure bit-level arithmetic for `half`, `bfloat`, `float`, `double`, and `fp128` (`fneg`, `fadd`, `fsub`, `fmul`, `fdiv`, `frem`, `fcmp`, `fpext`, `fptrunc`, `sitofp`, `uitofp`, `fptosi`, `fptoui`).
  - Fast-math flags (`nnan`, `ninf`, `nsz`, `fast`, etc.), IEEE rounding modes (`RNE`, `RNA`, `RTP`, `RTN`, `RTZ`), denormal modes, NaN propagation modes, exact rounding/math FP intrinsics (`llvm.fabs`, `llvm.copysign`, `llvm.fma`, `llvm.minimum`/`maximum`, `llvm.is.fpclass`, `llvm.fptosi.sat`/`fptoui.sat`, `llvm.ceil`, `llvm.floor`, `llvm.trunc`, `llvm.round`, `llvm.roundeven`, `llvm.rint`, `llvm.nearbyint`, `llvm.canonicalize`, `llvm.sqrt`, `llvm.ldexp`), and FP vector reductions (`llvm.vector.reduce.fadd`/`fmul`/`fmaximum`/`fminimum`/`fmaximumnum`/`fminimumnum`/`fmax`/`fmin`).
- **Control Flow, Modules, Calls, Value Attributes, Varargs, Aggregates, Vectors & Standalone `.ll` Parser**:
  - Multi-block CFGs with `br`, conditional `br`, `switch`, `unreachable`, parallel `phi` nodes, and recursive/indirect function-pointer calls across module definitions and globals.
  - First-class `ValueAttr` (`noundef`, `nonnull`, `align`, `dereferenceable`, `dereferenceable_or_null`, `range`, `byval`, `sret`, `noalias`, `readonly`), `volatile` load/store, constant expressions (`getelementptr`, `ptrtoint`/`inttoptr`/`bitcast`, `add`/`sub`), and varargs (`...`) syntax, printing, unexpansion, and semantics.
  - Structs (including `%T = type ...` named types resolved via `TopLevel.resolveTypes`), arrays, fixed-width vectors (`extractvalue`, `insertvalue`, `extractelement`, `insertelement`, `shufflevector`, `select`, lane-wise vector operations), and integer intrinsics (`llvm.abs`, `llvm.smax`/`smin`/`umax`/`umin`, `llvm.ctlz`/`cttz`/`ctpop`/`bitreverse`/`bswap`, `llvm.fshl`/`fshr`, saturating & `.with.overflow` arithmetic, `llvm.assume`).
  - Standalone total pure-Lean `.ll` text parser (`LeanNanoLlvm/AST/Parser.lean`) and CLI runner (`lean-nano-llvm run <file.ll>`).

## Architecture

The project is organized into a clean four-layer acyclic architecture under `LeanNanoLlvm/`:

1. `LeanNanoLlvm/Util`: `AssocMap.lean` (kernel-reducible association map), `Config.lean` (`SemanticsConfig`, `UndefMode`, `ExecError`), `IEEEFloat.lean`, `Poison.lean`, `Undef.lean` (`NondetOracle`, `OracleState`).
2. `LeanNanoLlvm/AST`: `AST.lean` (plain `Nat` widths, named types, `TopLevel.resolveTypes`), `DataLayout.lean`, `Print.lean`, `Syntax.lean` (`[llvm-*| ...]` quasiquoters with `i$(w)` antiquotation), `Unexpander.lean`, `Parser.lean` (standalone `.ll` text parser).
3. `LeanNanoLlvm/Semantics`:
   - `IntOps.lean` (bitvector ops & `icmp`) → `FloatOps.lean` → `Memory.lean` (`MemoryState`, `AllocSpec`, `MemoryInjection`, `MemoryState.IsRefinedBy`) → `Value.lean` (`RegisterValue`, serialization, `FreezeRel`, `UndefValRel`, pure/oracle evaluators)
   - `Intrinsics.lean` (LLVM intrinsics & `AllocLibcallSpec`) & `Machine.lean` (`TraceEvent`, `CallFrame`, `MachineState`, `Config`, `applyByValCopies`)
   - `Step.lean` (primary indexed small-step relation `Step`, `StarStep`, `Terminates`, `Diverges`, `CanAbort`, inversion lemmas)
   - `Exec.lean` (kernel-reducible `execStep` / `runSteps` + `execStep_sound` / `runSteps_sound` + module runners) & `Wellformed.lean`.
4. `LeanNanoLlvm/Refinement`: `Refinement.lean` (`Config.IsRefinedBy`, `of_simulation`, `RefinementEnv`, `Definition.IsRefinedByIn`, `Definition.IsRefinedByWith`, `x ⊒ y`, `refl`, `trans`, and `Trans` instances).
5. `LeanNanoLlvm/Tactic.lean`: layered simp sets (`simp_llvm`, `simp_wellform`, `simp_step`) and tactics (`llvm_simp`, `llvm_wf`, `llvm_step`).

## Build, CLI & Tests

```bash
lake build
lake exe lean-nano-llvm                                # built-in demo
lake exe lean-nano-llvm run tests/ll/fib.ll            # parse & run a standalone .ll file
bash scripts/run_ll_tests.sh                           # run standalone .ll regression suite
lake env lean scripts/audit_axioms.lean                # verify standard-axioms-only audit
python3 scripts/run_llubi_tests.py <path/to/llubi>     # optional cross-check against LLVM llubi tests
```

Test suites (verified directly in Lean's kernel using only standard axioms — no `native_decide`):

- [LeanNanoLlvm/AST/Test.lean](LeanNanoLlvm/AST/Test.lean) — syntax quasiquoters (`i$(w)`, attributes, volatile, varargs, named structs, load metadata, constexprs), printing, and unexpansion
- [LeanNanoLlvm/Semantics/Test.lean](LeanNanoLlvm/Semantics/Test.lean) — toggleable `undef`, Immediate UB vs `poison`, memory/provenance/endianness/heap/globals, IEEE-754 floats & rounding/reduction intrinsics, CFG/parallel `phi`/recursion, aggregates, vectors, volatile `TraceEvent`s, `load` metadata, `byval` copies, named structs, varargs, and `runSteps_sound`
- [LeanNanoLlvm/Refinement/Test.lean](LeanNanoLlvm/Refinement/Test.lean) — width-generic (`i$(w)`) arithmetic & `undef` refinement, `poison`, Immediate UB, nondeterministic `freeze`, IEEE-754 `fneg` & FMF (`nnan`), `select`, arbitrary caller-memory store-to-load forwarding & dead `alloca` elimination, caller-memory dead-store elimination (+ negative bogus-store rejection test), `calc` transitivity chaining, loop simulation (`Config.IsRefinedBy.of_simulation`), and module-aware interprocedural refinement (`RefinementEnv.ofTopLevel` / `⊒⟨env⟩`)
- [tests/ll/](tests/ll/) — standalone `.ll` regression tests executed via `lean-nano-llvm run` in CI

## Acknowledgments

This project reuses and adapts some code from [Lean-MLIR](https://github.com/opencompl/lean-mlir) and uses upstream LLVM's `llubi` (`llvm/tools/llubi`) as a semantic reference alongside prior LLVM formalizations such as [Vellvm](https://github.com/vellvm/vellvm).
