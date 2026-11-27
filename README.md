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
  - A separate kernel-reducible executable driver (`LeanNanoLlvm/Semantics/Exec.lean`: `execStep`, `runSteps`; `LeanNanoLlvm/Semantics/Module.lean`: `runDefinition`, `runModuleFunction`, `runCode`) evaluates concrete LLVM IR inside Lean's kernel (`decide +kernel`) and is formally proven sound against `Step` / `StarStep` (`execStep_sound`, `runSteps_sound`).
- **Full Behavioral Refinement, Coinductive Simulation & Module-Aware Contexts**:
  - `Config.IsRefinedBy` (`LeanNanoLlvm/Refinement/Refinement.lean`) provides the core configuration-level refinement relation, plus reusable proof combinators: `of_simulation` (for arbitrary loops/CFGs via `PlusStep` progress and `MemoryInjection.Extends` monotonicity), `of_det_halted`, `of_step_left`, `of_starStep_left`, `of_det_step_right`, `of_det_step_both`, and `of_common_tail`.
  - `RefinementEnv` (`RefinementEnv.ofTopLevel`) and `Definition.IsRefinedByIn` (`x ⊒⟨env⟩ y`) support interprocedural refinement inside a module's helper definitions, declarations, and `DataLayout`, with `Definition.IsRefinedByWith` (`x ⊒[cfg] y`, defaulting to `x ⊒ y` under `SemanticsConfig.modern`) as a lightweight abbreviation.
  - Unconditional reflexivity (`refl`) and transitivity (`trans`, integrated with Lean's core `Trans` typeclass for native `calc` chaining), supported by three layered simp sets and tactics (`llvm_simp` / `simp_llvm`, `llvm_wf` / `simp_wellform`, `llvm_step` / `simp_step` in `LeanNanoLlvm/Tactic.lean`).
- **Optional, Switchable `undef` (`SemanticsConfig.undefMode`)**:
  - Defaults to `SemanticsConfig.modern` (`undefMode := .disabled`), matching LLVM's ongoing deprecation of `undef` (`Exp.undef` is rejected in well-formedness and execution, and uninitialized memory/padding is `poison`).
  - Explicitly opt into legacy `undef` with `SemanticsConfig.withUndef` (`undefMode := .nondet`), deterministic zero-fill with `SemanticsConfig.deterministic`, or `SemanticsConfig.legacyCompat`.
- **Bit-Level Memory, Provenance & Byte Types (`bN`)** (`LeanNanoLlvm/Semantics/Memory.lean`, `LeanNanoLlvm/AST/DataLayout.lean`):
  - Exact per-bit provenance (`MemBit`), little-endian & big-endian `DataLayout` (`default64LE`, `default64BE`, `default32LE`, custom integer alignments, all-ones null `po<n>`), unpacked/packed/named struct layouts (`%T = type { ... }`), sub-byte integer padding canonicalization, volatile memory events, and `load`/`phi`/`call` metadata (`!noundef`, `!nonnull`, `!range`).
  - First-class LLVM byte types (`bN`) with per-bit poison/provenance tracking and scalar/vector `bitinsert`/`bitextract`, `bitcast`, and `freeze` semantics.
  - `alloca`, `load`, `store`, `getelementptr` (`inbounds`/`nusw`/`nuw` + struct splat vector broadcast), `ptrtoint` vs `ptrtoaddr` exposed provenance generations, `inttoptr`, `addrspacecast`, `bitcast`.
  - Stack frame allocation & dangling-pointer detection, `byval(T)` callee stack-copy isolation, `llvm.lifetime.start`/`end`, heap `malloc`/`calloc`/`free`, C++ `operator new`/`delete` (`_Znwm`/`_Znam`/`_ZdlPv`/`_ZdaPv`), `llvm.memcpy`/`memmove`/`memset`, and mutable/`constant` globals.
- **Kernel-Reducible IEEE-754 Floating-Point Engine** (`LeanNanoLlvm/Util/IEEEFloat.lean`, `LeanNanoLlvm/Semantics/FloatOps.lean`):
  - Pure bit-level arithmetic for `half`, `bfloat`, `float`, `double`, `x86_fp80`, `fp128`, and `ppc_fp128` (`fneg`, `fadd`, `fsub`, `fmul`, `fdiv`, `frem`, `fcmp`, `fpext`, `fptrunc`, `sitofp`, `uitofp`, `fptosi`, `fptoui`).
  - Fast-math flags (`nnan`, `ninf`, `nsz`, `fast`, etc.), IEEE rounding modes (`RNE`, `RNA`, `RTP`, `RTN`, `RTZ`), denormal modes, NaN propagation modes, exact rounding/math FP intrinsics (`llvm.fabs`, `llvm.copysign`, `llvm.fma`/`fmuladd`, `llvm.minimum`/`maximum`, `llvm.is.fpclass`, `llvm.fptosi.sat`/`fptoui.sat`, `llvm.ceil`, `llvm.floor`, `llvm.trunc`, `llvm.round`, `llvm.roundeven`, `llvm.rint`, `llvm.nearbyint`, `llvm.canonicalize`, `llvm.sqrt`, `llvm.ldexp`), and FP vector reductions (`llvm.vector.reduce.fadd`/`fmul`/`fmaximum`/`fminimum`/`fmaximumnum`/`fminimumnum`/`fmax`/`fmin`).
- **Control Flow, Modules, Calls, Value Attributes, Vectors, Intrinsics & Standalone `.ll` Parser**:
  - Multi-block CFGs with `br`, conditional `br`, `switch`, `indirectbr`/`blockaddress`, `invoke`/`callbr`, `unreachable`, parallel `phi` nodes, recursive/indirect function-pointer calls, `nobuiltin`, and C/C++ libcalls (`printf`, `puts`, `putchar`, `exit`, `abort`, `_ZSt9terminatev`).
  - First-class `ValueAttr` (`noundef`, `nonnull`, `align`, `dereferenceable`, `dereferenceable_or_null`, `range`/`rangeList`, `nofpclass`, `byval`, `sret`, `noalias`, `readonly`), `noreturn`, `llvm.assume` operand bundles, `volatile` load/store, constant expressions (`getelementptr`, `ptrtoint`/`inttoptr`/`bitcast`, `add`/`sub`, `insertelement`), and varargs (`...`).
  - Structs (including `%T = type ...` named types resolved via `TopLevel.resolveTypes`), arrays, fixed-width and scalable vectors (`<vscale x N x T>`, `llvm.vscale`, `llvm.stepvector`, `extractvalue`, `insertvalue`, `extractelement`, `insertelement`, `shufflevector`, `select`), integer/bit intrinsics (`abs`, `smax`/`smin`/`umax`/`umin`, `ctlz`/`cttz`/`ctpop`/`bitreverse`/`bswap`, `fshl`/`fshr`, `sshl.sat`/`ushl.sat`, `scmp`/`ucmp`, `smulh`/`umulh`, `clmul`, `pdep`/`pext`, saturating & `.with.overflow`), and vector/masked/VP/matrix/histogram/speculative intrinsics (`vector.reduce.*`, `vector.reverse`/`extract`/`insert`/`interleave*`/`deinterleave*`/`splice.*`, `get.active.lane.mask`, `mask.beforefirst`, `masked.{load,store,gather,scatter,expandload,compressstore}`, `vp.{merge,load,store,gather,scatter}`, `experimental.vp.strided.{load,store}`, `matrix.{transpose,column.major.store}`, `speculative.load`, `experimental.vector.{compress,extract.last.active,match,histogram.*}`).
  - Standalone total pure-Lean `.ll` text parser (`LeanNanoLlvm/AST/Parser.lean`) and CLI runner (`lean-nano-llvm run <file.ll> --verbose ...`).
- **`llubi`-Compatible Frontend** (`LeanNanoLlvm/Llubi/`, `lean-nano-llvm llubi ...`): runs a module with the verified small-step semantics and reproduces LLVM `llubi`'s observable behaviour byte for byte — the same options, the same `--verbose` trace (instructions re-printed exactly as LLVM's `AsmWriter` prints them, values printed as `llubi`'s `AnyValue::print`), the same `Stacktrace:` / `Immediate UB detected:` / `Error:` diagnostics with `<stdin>:LINE` locations, program output, and exit codes. LLVM's own `llvm/test/tools/llubi` suite therefore runs unmodified under `lit` + `FileCheck`:
  - `AsmWriter.lean` re-prints each instruction from its source tokens (recorded by the parser's source map) with LLVM's canonicalizations: signed integer constants, `writeAPFloatInternal` float formatting, constant uniquing (`zeroinitializer`, `poison`, `undef`, `splat (...)`, `c"..."`), implicit `align`, intrinsic name re-mangling, attribute ordering, metadata slot numbering, `/* (fpclass) */` comments, and multi-line `switch`/`invoke`/`callbr`.
  - `AST/FloatLiteral.lean` is a bit-exact port of `APFloat::toString` / `toStringRoundTrip` and `writeAPFloatInternal`; `Driver.lean` holds the CLI, the trace loop over `execStep`, and an `std::mt19937_64` oracle seeded like `llubi`.
  - **Nondeterminism: universal in the specification, seeded in the frontend.** In `Step`, every nondeterministic choice is a relation or is quantified over all oracles: `undef` bits (`UndefValRel`), `freeze` (`FreezeRel`), uninitialized and `undef` bytes (`BytesToValueRel`), NaN sign and payload, `nsz` zero signs, denormal flushing, sNaN quieting in `maxnum`/`minnum`, the order of FP reductions, `get.vector.length`, and provenance tags. So a property proved about `Step` holds for *every* resolution. The executable `execStep` is proven sound for every `OracleState`. It draws from the oracle lazily, only where `llubi` calls its RNG, and in the same order and quantity: one word per 64 bits of a random `APInt`, one draw per `undef` logical byte (stopping at the first poison), per-byte draws when freezing bytes, NaN candidates deduplicated in `llubi`'s order, and one random tag word per 64 pointer bits the first time an object's pointer is serialized. Feeding it the `mt19937_64` stream seeded as `llubi --seed` does therefore reproduces `llubi`'s random choices exactly.
  - Call semantics follow `llubi`'s `enterCall`/`returnFromCallee`. A `tail`/`musttail` call makes the caller's stack objects (its allocas and byval copies) inaccessible until it returns, after the byval copies and before the argument attributes are checked. Calling conventions (`fastcc`, `cc N`, …) must match between the call site and a non-intrinsic callee. byval copies are allocated with the callee's, then the call site's, then the ABI alignment.

## Architecture

The library `LeanNanoLlvm/` is layered; each layer imports only the ones above it.

1. **`Util/`**: generic, kernel-reducible building blocks.
   - `AssocMap` (association map), `Poison` (`PoisonOr`), `Oracle` (`NondetOracle`, `OracleState`).
   - `IEEEFloat` (bit-exact IEEE-754 arithmetic), `CFormat` (`printf` conversions), `Hex`, `Text`.
   - `Config` (`SemanticsConfig`, the `undef`/`freeze`/NaN/denormal modes, `ExecError`).
2. **`AST/`**: the syntax of LLVM IR.
   - `AST` (the syntax tree), `DataLayout`, `Resolve` (named types `%T = type ...`).
   - `Print` (IR text) and `FloatLiteral` (LLVM's float literal formats).
   - `Lexer` and `Parser` (the `.ll` parser, which also records source ranges for the `llubi` frontend).
   - `Syntax` and `Unexpander` (`[llvm-*| ...]` quasiquoters with `i$(w)` antiquotation, and their delaborators).
3. **`Semantics/`**: the semantics, in dependency order.
   - Scalars and memory:
     - `IntOps` (bitvector operations and `icmp`) and `FloatOps` (FP operations and their lazily drawn choices).
     - `Memory` (`MemoryState`, `AllocSpec`, provenance, accessibility) and `MemoryRefinement` (`MemoryInjection` and refinement of bits, bytes and memory).
   - Values:
     - `Value` (`RegisterValue`, its debug rendering and refinement) and `Display` (provenance tags and `llubi`'s value format).
     - `Bytes` (`valueToBytes`/`bytesToValue`), `FreezeUndef` (`FreezeRel`, `UndefValRel` and their executable generators), `GEP`.
     - `Operations` (the deterministic operations shared by both semantics, including attributes).
   - Intrinsics: `Intrinsics/` holds `MemTransfer`, `Alloc` (`AllocLibcallSpec`), `Pure`, `Libc` and `VectorMemory`, and `Intrinsics` dispatches among them.
   - The machine and its steps:
     - `Machine` (`TraceEvent`, `CallFrame`, `MachineState`, `Config`, call entry and byval copies).
     - `Step` (the primary relation `Step`, `StarStep`, behaviours) and `StepLemmas` (inversion lemmas).
     - `Exec` (the kernel-reducible `execStep`/`runSteps`, proven sound against `Step`) and `Module` (module initialization and runners).
     - `Wellformed`.
4. **`Refinement/`**: `Refinement` provides:
   - `Config.IsRefinedBy`, `of_simulation`, `RefinementEnv`, `Definition.IsRefinedByIn` and `Definition.IsRefinedByWith`;
   - the notations `x ⊒ y`, `x ⊒[cfg] y` and `x ⊒⟨env⟩ y`;
   - `refl`, `trans` and `Trans` instances.
5. **`Tactic`**: the layered simp sets (`simp_llvm`, `simp_wellform`, `simp_step`) and tactics (`llvm_simp`, `llvm_wf`, `llvm_step`).
6. **Frontends**: these are executable code outside the verified core.
   - `Run` implements `lean-nano-llvm run`.
   - `Llubi/` is the `llubi`-compatible frontend: `AsmWriter` re-prints instructions as LLVM does, and `Driver` holds the CLI and the trace.

The proof suites are a separate library, `Tests/` (`Tests.AST`, `Tests.Semantics`, `Tests.Refinement`), which `lake build` builds as a default target. `Main.lean` only dispatches to `Run` and `Llubi`.

## Build, CLI & Tests

```bash
lake build
lake exe lean-nano-llvm --help                         # usage
lake exe lean-nano-llvm run tests/ll/fib.ll            # parse & run a standalone .ll file
bash scripts/run_ll_tests.sh                           # run standalone .ll regression suite
lake env lean scripts/audit_axioms.lean                # verify standard-axioms-only audit
bash scripts/run_llubi_tests.sh [llvm/test/tools/llubi] # LLVM's llubi suite via lit + FileCheck
lake exe lean-nano-llvm llubi --verbose < tests/ll/fib.ll  # llubi-compatible trace
```

`scripts/run_llubi_tests.sh` only invokes `lit` on [tests/llubi/lit.cfg.py](tests/llubi/lit.cfg.py), which substitutes `llubi` with `lean-nano-llvm llubi`; without a directory argument it fetches the tests from llvm-project at a pinned commit. It needs `lit` (`pip install lit`) and LLVM's `FileCheck` on `PATH` (e.g. Ubuntu's `llvm-18-tools`). All 246 tests pass. Any future known gap goes in [tests/llubi/xfail.txt](tests/llubi/xfail.txt), which is currently empty; lit reports an unexpected pass of a listed test as a failure.

Test suites (verified directly in Lean's kernel using only standard axioms — no `native_decide`):

- [Tests/AST.lean](Tests/AST.lean) — syntax quasiquoters (`i$(w)`, attributes, volatile, varargs, named structs, load metadata, constexprs), printing, and unexpansion
- [Tests/Semantics.lean](Tests/Semantics.lean) — toggleable `undef`, Immediate UB vs `poison`, memory/provenance/endianness/heap/globals, IEEE-754 floats & rounding/reduction intrinsics, CFG/parallel `phi`/recursion, aggregates, vectors, volatile `TraceEvent`s, `load` metadata, `byval` copies, named structs, varargs, and `runSteps_sound`
- [Tests/Refinement.lean](Tests/Refinement.lean) — width-generic (`i$(w)`) arithmetic & `undef` refinement, `poison`, Immediate UB, nondeterministic `freeze`, IEEE-754 `fneg` & FMF (`nnan`), `select`, arbitrary caller-memory store-to-load forwarding & dead `alloca` elimination, caller-memory dead-store elimination (+ negative bogus-store rejection test), `calc` transitivity chaining, loop simulation (`Config.IsRefinedBy.of_simulation`), and module-aware interprocedural refinement (`RefinementEnv.ofTopLevel` / `⊒⟨env⟩`)
- [tests/ll/](tests/ll/) — standalone `.ll` regression tests executed via `lean-nano-llvm run` in CI
- [tests/llubi/](tests/llubi/) — `lit` configuration running LLVM's `llvm/test/tools/llubi` suite against `lean-nano-llvm llubi` in CI

## Acknowledgments

This project reuses and adapts some code from [Lean-MLIR](https://github.com/opencompl/lean-mlir) and uses upstream LLVM's `llubi` (`llvm/tools/llubi`) as a semantic reference alongside prior LLVM formalizations such as [Vellvm](https://github.com/vellvm/vellvm).
