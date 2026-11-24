# lean-nano-llvm

Lean 4 formalization of an executable, almost-complete LLVM IR subset with parsing, printing, data layouts, well-formedness, bit-level operational semantics (aligned with LLVM's `llubi` reference interpreter), configurable `undef` support, and formal refinement proofs.

At the core, this project lets you write LLVM IR programs directly in Lean using quasiquotations and formally prove program optimizations and semantic properties inside Lean's kernel.

```lean
theorem ret_add_x_0_is_refined_by_ret_x :
  [llvm-definition|
    define i8 @f(i8 %x) {
    entry:
      ret i8 %x
    }
  ] ⊑ [llvm-definition|
    define i8 @f(i8 %x) {
    entry:
      %x = add i8 %x, 0
      ret i8 %x
    }
  ] := by
  -- ...
```

## Highlights

- **Optional, switchable `undef` (`SemanticsConfig.undefMode`)**:
  - Defaults to `SemanticsConfig.modern` (`undefMode := .disabled`), matching LLVM's ongoing deprecation of `undef` (`Exp.undef` is rejected in well-formedness and execution, and uninitialized memory/padding is `poison`).
  - Explicitly opt into legacy `undef` with `SemanticsConfig.withUndef` (`undefMode := .nondet`), deterministic zero-fill with `SemanticsConfig.deterministic` (`undefMode := .zero, freezeMode := .zero`), or `SemanticsConfig.legacyCompat`.
  - Refinement supports explicit configurations via `y ⊑[cfg] x` (with `y ⊑ x` defaulting to `SemanticsConfig.modern`).
- **Bit-level Memory & Provenance Model** (`LeanNanoLlvm/Semantics/Memory.lean`, `LeanNanoLlvm/AST/DataLayout.lean`):
  - Exact per-bit provenance (`MemBit`), little-endian & big-endian `DataLayout` (`default64LE`, `default64BE`, `default32LE`), unpacked/packed struct layouts, sub-byte integer padding canonicalization, and `load ..., !noundef`.
  - `alloca`, `load`, `store`, `getelementptr` (`inbounds`/`nusw`/`nuw`), `ptrtoint` vs `ptrtoaddr` exposed provenance generations, `inttoptr`, `addrspacecast`, `bitcast`.
  - Stack frame allocation & dangling-pointer detection, `llvm.lifetime.start`/`end`, heap `malloc`/`calloc`/`free` (with use-after-free, double-free, and non-heap free Immediate UB), `llvm.memcpy`/`memmove`/`memset`, and mutable/`constant` globals.
- **Kernel-Reducible IEEE-754 Floating-Point Engine** (`LeanNanoLlvm/Util/IEEEFloat.lean`, `LeanNanoLlvm/Semantics/FloatOps.lean`):
  - Pure bit-level arithmetic for `half`, `bfloat`, `float`, `double`, and `fp128` (`fneg`, `fadd`, `fsub`, `fmul`, `fdiv`, `frem`, `fcmp`, `fpext`, `fptrunc`, `sitofp`, `uitofp`, `fptosi`, `fptoui`).
  - Fast-math flags (`nnan`, `ninf`, `nsz`, `fast`, etc.), IEEE rounding modes (`RNE`, `RNA`, `RTP`, `RTN`, `RTZ`), denormal modes, NaN propagation modes, and FP intrinsics (`llvm.fabs`, `llvm.copysign`, `llvm.fma`, `llvm.minimum`/`maximum`, `llvm.is.fpclass`, `llvm.fptosi.sat`, `llvm.fptoui.sat`).
- **Control Flow, Modules, Calls, Aggregates, Vectors & Intrinsics**:
  - Multi-block CFGs with `br`, conditional `br`, `switch`, `unreachable`, parallel `phi` nodes, and fuel-bounded loops/recursion.
  - Direct and indirect function-pointer `call`s across module definitions and global variables.
  - Structs, arrays, fixed-width vectors (`extractvalue`, `insertvalue`, `extractelement`, `insertelement`, `shufflevector`, `select`, lane-wise vector operations), and integer intrinsics (`llvm.abs`, `llvm.smax`/`smin`/`umax`/`umin`, `llvm.ctlz`/`cttz`/`ctpop`/`bitreverse`/`bswap`, `llvm.fshl`/`fshr`, saturating & `.with.overflow` arithmetic, `llvm.assume`).
- **UB-Aware Refinement & Arbitrary-Width Proofs**:
  - Total nondeterminism oracle (`NondetOracle := Nat → Nat`) for `freeze`, `undef` (when enabled), and FP nondeterminism.
  - Explicit separation of `ExecError.immediateUB` from `staticError` / resource limits, so Immediate UB refines to any behavior.
  - Symbolic integer widths (`i$0`, `ConcreteOrMVar`) enabling single width-generic refinement proofs over all bitwidths `w`.

## Architecture

The project preserves a clean four-layer architecture under `LeanNanoLlvm/`:

1. `LeanNanoLlvm/Util`: `Config.lean` (`SemanticsConfig`, `UndefMode`, `ExecError`), `IEEEFloat.lean`, `Poison.lean`, `ConcreteOrMVar.lean`, `Undef.lean` (`NondetOracle`, `SupplyState`).
2. `LeanNanoLlvm/AST`: `AST.lean`, `DataLayout.lean`, `Print.lean`, `Syntax.lean` (`[llvm-*| ...]` quasiquoters), `Unexpander.lean`.
3. `LeanNanoLlvm/Semantics`: `Semantics.lean` (bitvector ops & `icmp`), `FloatOps.lean`, `Memory.lean`, `State.lean` (`RegisterValue`, serialization, `NanoLlvmState`), `Eval.lean` (total interpreter + intrinsics/libcalls), `Wellformed.lean`.
4. `LeanNanoLlvm/Refinement`: `Refinement.lean` (`RegisterValue.Refines`, `Definition.RefinesWith`, `y ⊑[cfg] x`, `y ⊑ x`).

## Build & Test

```bash
lake build
lake exe lean-nano-llvm
```

Test suites (verified in Lean's kernel):

- [LeanNanoLlvm/AST/Test.lean](LeanNanoLlvm/AST/Test.lean) — syntax quasiquoters, printing, and unexpansion
- [LeanNanoLlvm/Semantics/Test.lean](LeanNanoLlvm/Semantics/Test.lean) — toggleable `undef`, Immediate UB vs `poison`, memory/provenance/endianness/heap/globals, IEEE-754 floats, CFG/parallel `phi`/recursion, aggregates, vectors, and intrinsics
- [LeanNanoLlvm/Refinement/Test.lean](LeanNanoLlvm/Refinement/Test.lean) — width-generic arithmetic & `undef` refinement, `poison`, Immediate UB, nondeterministic `freeze`, IEEE-754 `fneg` & FMF (`nnan`), `select`, and stack memory store-to-load forwarding

## Acknowledgments

This project reuses and adapts some code from [Lean-MLIR](https://github.com/opencompl/lean-mlir) and uses upstream LLVM's `llubi` (`llvm/tools/llubi`) as a semantic reference alongside prior LLVM formalizations such as [Vellvm](https://github.com/vellvm/vellvm).
