# lean-nano-llvm

Lean formalization of a small, executable LLVM-like IR with parsing, printing, wellformedness, denotational semantics, and refinement proofs.

At the core, this project lets you write tiny LLVM programs directly in Lean and prove program optimizations correct.

This project is a research and experimentation artifact, not a production LLVM verification toolchain.

```lean
theorem ret_add_x_0_refines_ret_x :
  [llvm-definition|
    define i8 @f(i8 %x) {
    entry:
      %x = add i8 %x, 0
      ret i8 %x
    }
  ] ⊑ [llvm-definition|
    define i8 @f(i8 %x) {
    entry:
      ret i8 %x
    }
  ] := by
  -- ...
```

> See [LeanNanoLlvm/Refinement/Test.lean](LeanNanoLlvm/Refinement/Test.lean#L50) for the full proof.
>
> This says: the program `x + 0` refines the program `x`, where `x` is a variable of type `i8` (a signed integer of width `8`).

More interestingly, the project supports symbolic widths, so you can write one program with a symbolic width and prove a theorem that holds for every concrete width:

```lean
theorem ret_add_x_0_refines_ret_x_generic (w : Nat) :
  [llvm-1-definition|
    define i$0 @f(i$0 %x) {
    entry:
      %x = add i$0 %x, 0
      ret i$0 %x
    }
  ].instantiateWidths (singletonWidths w)
  ⊑
  [llvm-1-definition|
    define i$0 @f(i$0 %x) {
    entry:
      ret i$0 %x
    }
  ].instantiateWidths (singletonWidths w) := by
  -- ...
```

> See [LeanNanoLlvm/Refinement/Test.lean](LeanNanoLlvm/Refinement/Test.lean#L83) for the full proof.
>
> This says: for every bitwidth `w`, the program `x + 0` refines the program `x`,
where `x` is a variable of type `i$0` (a signed integer of width `w`).

## Why it is interesting

- Arbitrary-width refinement proofs: write one symbolic-width program and prove a theorem for every concrete width.
- Executable semantics: instantiate widths, run the program, and get a concrete result.
- Surface syntax inside Lean: programs can be written in an LLVM-like notation instead of raw constructors.
- Syntax + printing + unexpansion: symbolic widths such as `i$0` round-trip through the frontend.
- Structural wellformedness checks: definitions, declarations, instructions, terminators, scopes, and argument values are checked explicitly.

## What the project provides

- An AST for a small LLVM-like language in [LeanNanoLlvm/AST](LeanNanoLlvm/AST/Test.lean)
- Quasiquoters such as:
  - `[llvm-type| ...]`
  - `[llvm-exp| ...]`
  - `[llvm-instruction| ...]`
  - `[llvm-definition| ...]`
- Symbolic widths via `ConcreteOrMVar`, so widths can be reused across return types, argument types, and instructions
- Width instantiation from symbolic programs to concrete programs
- Denotational semantics for integer expressions and single-block definitions
- A refinement relation for proving one definition refines another

## Small executable example

The project can also execute instantiated symbolic programs. The theorem in [Semantics/Test.lean](LeanNanoLlvm/Semantics/Test.lean#L251) proves:

```lean
runInstantiatedDefinition (singletonWidths 8) [llvm-1-definition|
    define i$0 @f(i$0 %a) {
    entry:
      %x = add i$0 %a, 1
      ret i$0 %x
    }
  ] [ .bv 8 (.value (2 : BitVec 8)) ]
  = .ok (.bv 8 (.value (3 : BitVec 8)))
```

So a symbolic-width function can be instantiated at width `8` and run concretely.

## Supported IR constructs

Currently, the IR supports:

- integer types
- function types
- integer binary operations such as `add`
- conversions such as `trunc`, `zext`, `sext`
- `freeze` (turns `poison` to `0`, which may not be exactly the same as LLVM)
- `ret`
- single basic block function bodies

This is enough to state and prove small optimization theorems cleanly.

## Limitations

This is not a full LLVM model. Important current limitations:

- No multi-basic-block control flow
- No memory model
- No loads, stores, pointers, or aliasing reasoning
- No calls, external effects, or interprocedural semantics
- No phi nodes
- No poison/undef completeness story close to full LLVM
- No first-class refinement interface for unknown `undef` inputs; refinement currently quantifies over an explicit `undef` environment
- Execution requires concrete widths; symbolic-width programs must be instantiated before running

## Build

```bash
lake build
```

Useful test files:

- [AST/Test.lean](LeanNanoLlvm/AST/Test.lean)
- [Semantics/Test.lean](LeanNanoLlvm/Semantics/Test.lean)
- [Refinement/Test.lean](LeanNanoLlvm/Refinement/Test.lean)

## Direction

The project is aimed at a sweet spot:

- small enough that semantics and proofs stay readable
- expressive enough to demonstrate real program refinement arguments
- structured enough to grow toward richer LLVM features later

## Acknowledgments

This project reuses and adapts some code from
[Lean-MLIR](https://github.com/opencompl/lean-mlir) and is also informed by
prior LLVM formalization efforts such as
[Vellvm](https://github.com/vellvm/vellvm), although no Vellvm code is included
in this repository.
