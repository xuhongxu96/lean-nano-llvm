# lean-nano-llvm

Zero-dependency Lean 4 formalization of an executable, almost-complete LLVM IR subset with parsing, printing, unexpansion, data layouts, well-formedness, bit-level small-step operational semantics (aligned with LLVM's `llubi` reference interpreter), a proven-sound kernel-reducible interpreter, configurable `undef` support, and full behavioral refinement proofs.

At the core, this project lets you write LLVM IR programs directly in Lean using quasiquotations (including arbitrary bitwidth antiquotation `i$(w)`) and formally prove program optimizations and semantic properties inside Lean's kernel using only standard axioms.

```lean
theorem ret_add_x_0_is_refined_by_ret_x_generic (w : Nat) :
  [llvm-definition|
    define i$(w) @f(i$(w) %x) {
    entry:
      ret i$(w) %x
    }
  ] ⊑ [llvm-definition|
    define i$(w) @f(i$(w) %x) {
    entry:
      %x = add i$(w) %x, 0
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
- **Full Behavioral Refinement with Reflexivity & Transitivity**:
  - `Definition.RefinesWith` (`y ⊑[cfg] x`, defaulting to `y ⊑ x` under `SemanticsConfig.modern`) quantifies over arbitrary well-formed caller memories `initMem` and relates return values (`RegisterValue.Refines`), caller-visible final memory (`MemoryState.Refines`), observable traces (`Trace.Refines`), divergence (`Diverges`), and abort/UB/OOM (`CanAbort`) via partial allocation bijections (`MemoryInjection`).
  - Unconditional reflexivity (`Definition.RefinesWith.refl`) and transitivity (`Definition.RefinesWith.trans`, integrated with Lean's core `Trans` typeclass for native `calc` chaining).
- **Optional, Switchable `undef` (`SemanticsConfig.undefMode`)**:
  - Defaults to `SemanticsConfig.modern` (`undefMode := .disabled`), matching LLVM's ongoing deprecation of `undef` (`Exp.undef` is rejected in well-formedness and execution, and uninitialized memory/padding is `poison`).
  - Explicitly opt into legacy `undef` with `SemanticsConfig.withUndef` (`undefMode := .nondet`), deterministic zero-fill with `SemanticsConfig.deterministic`, or `SemanticsConfig.legacyCompat`.
- **Bit-Level Memory & Provenance Model** (`LeanNanoLlvm/Semantics/Memory.lean`, `LeanNanoLlvm/AST/DataLayout.lean`):
  - Exact per-bit provenance (`MemBit`), little-endian & big-endian `DataLayout` (`default64LE`, `default64BE`, `default32LE`), unpacked/packed struct layouts, sub-byte integer padding canonicalization, volatile memory events, and `load ..., !noundef`.
  - `alloca`, `load`, `store`, `getelementptr` (`inbounds`/`nusw`/`nuw`), `ptrtoint` vs `ptrtoaddr` exposed provenance generations, `inttoptr`, `addrspacecast`, `bitcast`.
  - Stack frame allocation & dangling-pointer detection, `llvm.lifetime.start`/`end`, heap `malloc`/`calloc`/`free`, `llvm.memcpy`/`memmove`/`memset`, and mutable/`constant` globals.
- **Kernel-Reducible IEEE-754 Floating-Point Engine** (`LeanNanoLlvm/Util/IEEEFloat.lean`, `LeanNanoLlvm/Semantics/FloatOps.lean`):
  - Pure bit-level arithmetic for `half`, `bfloat`, `float`, `double`, and `fp128` (`fneg`, `fadd`, `fsub`, `fmul`, `fdiv`, `frem`, `fcmp`, `fpext`, `fptrunc`, `sitofp`, `uitofp`, `fptosi`, `fptoui`).
  - Fast-math flags (`nnan`, `ninf`, `nsz`, `fast`, etc.), IEEE rounding modes (`RNE`, `RNA`, `RTP`, `RTN`, `RTZ`), denormal modes, NaN propagation modes, and FP intrinsics (`llvm.fabs`, `llvm.copysign`, `llvm.fma`, `llvm.minimum`/`maximum`, `llvm.is.fpclass`, `llvm.fptosi.sat`, `llvm.fptoui.sat`).
- **Control Flow, Modules, Calls, Value Attributes, Varargs, Aggregates, Vectors & Intrinsics**:
  - Multi-block CFGs with `br`, conditional `br`, `switch`, `unreachable`, parallel `phi` nodes, and recursive/indirect function-pointer calls across module definitions and globals.
  - First-class `ValueAttr` (`noundef`, `nonnull`, `align`, `dereferenceable`, `range`, `signext`, `zeroext`), `volatile` load/store, and varargs (`...`) syntax, printing, unexpansion, and semantics.
  - Structs, arrays, fixed-width vectors (`extractvalue`, `insertvalue`, `extractelement`, `insertelement`, `shufflevector`, `select`, lane-wise vector operations), and integer intrinsics (`llvm.abs`, `llvm.smax`/`smin`/`umax`/`umin`, `llvm.ctlz`/`cttz`/`ctpop`/`bitreverse`/`bswap`, `llvm.fshl`/`fshr`, saturating & `.with.overflow` arithmetic, `llvm.assume`).

## Architecture

The project is organized into a clean four-layer acyclic architecture under `LeanNanoLlvm/`:

1. `LeanNanoLlvm/Util`: `AssocMap.lean` (kernel-reducible association map), `Config.lean` (`SemanticsConfig`, `UndefMode`, `ExecError`), `IEEEFloat.lean`, `Poison.lean`, `Undef.lean` (`NondetOracle`, `OracleState`).
2. `LeanNanoLlvm/AST`: `AST.lean` (plain `Nat` widths), `DataLayout.lean`, `Print.lean`, `Syntax.lean` (`[llvm-*| ...]` quasiquoters with `i$(w)` antiquotation), `Unexpander.lean`.
3. `LeanNanoLlvm/Semantics`:
   - `IntOps.lean` (bitvector ops & `icmp`) → `FloatOps.lean` → `Memory.lean` (`MemoryState`, `AllocSpec`, `MemoryInjection`, `MemoryState.Refines`) → `Value.lean` (`RegisterValue`, serialization, `FreezeRel`, `UndefValRel`, pure/oracle evaluators)
   - `Intrinsics.lean` (LLVM intrinsics & `AllocLibcallSpec`) & `Machine.lean` (`TraceEvent`, `CallFrame`, `MachineState`, `Config`)
   - `Step.lean` (primary indexed small-step relation `Step`, `StarStep`, `Terminates`, `Diverges`, `CanAbort`, inversion lemmas)
   - `Exec.lean` (kernel-reducible `execStep` / `runSteps` + `execStep_sound` / `runSteps_sound` + module runners) & `Wellformed.lean`.
4. `LeanNanoLlvm/Refinement`: `Refinement.lean` (`Definition.RefinesWith`, `y ⊑[cfg] x`, `y ⊑ x`, `refl`, `trans`, and `Trans` instances).

## Build & Test

```bash
lake build
lake exe lean-nano-llvm
```

Test suites (verified directly in Lean's kernel using only standard axioms — no `native_decide`):

- [LeanNanoLlvm/AST/Test.lean](LeanNanoLlvm/AST/Test.lean) — syntax quasiquoters (`i$(w)`, attributes, volatile, varargs), printing, and unexpansion
- [LeanNanoLlvm/Semantics/Test.lean](LeanNanoLlvm/Semantics/Test.lean) — toggleable `undef`, Immediate UB vs `poison`, memory/provenance/endianness/heap/globals, IEEE-754 floats, CFG/parallel `phi`/recursion, aggregates, vectors, intrinsics, volatile `TraceEvent`s, single-block param attributes, varargs, and `runSteps_sound`
- [LeanNanoLlvm/Refinement/Test.lean](LeanNanoLlvm/Refinement/Test.lean) — width-generic (`i$(w)`) arithmetic & `undef` refinement, `poison`, Immediate UB, nondeterministic `freeze`, IEEE-754 `fneg` & FMF (`nnan`), `select`, arbitrary caller-memory store-to-load forwarding & dead `alloca` elimination, caller-memory dead-store elimination (+ negative bogus-store rejection test), and `calc` transitivity chaining

## Acknowledgments

This project reuses and adapts some code from [Lean-MLIR](https://github.com/opencompl/lean-mlir) and uses upstream LLVM's `llubi` (`llvm/tools/llubi`) as a semantic reference alongside prior LLVM formalizations such as [Vellvm](https://github.com/vellvm/vellvm).
