# Differential and mutation testing against llubi and Alive2

This directory holds the infrastructure for validating lean-nano-llvm's semantics against two
independent oracles:

* **llubi** (`llvm/tools/llubi`), LLVM's UB-aware reference interpreter. Our llubi-compatible
  frontend (`lean-nano-llvm llubi`) must produce the same observable behaviour: exit code,
  program output and the `--verbose` instruction trace, byte for byte.
* **Alive2** (`alive-tv`), the SMT-based refinement checker. Every pair Alive2 proves correct
  should be provable by us (`llvm_refine`), and every pair it refutes should be disprovable
  (`llvm_disprove`), ideally with Alive2's own counterexample.

It lives outside `LeanNanoLlvm/` and `Tests/` and does not change the Lean library: the Lean side
of the refinement experiment is generated per case (see [Translation](#4-translation-to-lean)).

The text below is written so that it can be lifted into the evaluation section of a paper. Each
claim names the code that implements it.

## 0. Quick start

```bash
difftest/tools/build_oracles.sh                     # llubi, alive-tv, opt, ... at the pins (~1-2 h)
lake build                                          # lean-nano-llvm itself
DT=difftest/bin/dt
$DT provenance                                      # record versions and pins
$DT collect --llvm-src difftest/.oracles/src/llvm-project --alive2-src difftest/.oracles/src/alive2
$DT mutate --per-unit 10 --max-order 1              # seeded mutants
$DT pairs  --origins alive2-test,opt,mutation       # refinement pairs
$DT cases  --args-per-function 4                    # execution cases
$DT run-llubi  --seeds 0,1                          # phase 2: large-scale runs
$DT run-alive2 --config no-undef-input
$DT run-alive2 --config default
$DT run-alive2 --config test-args                   # Alive2 tests with their own TEST-ARGS (sanity check)
$DT run-lean
$DT report                                          # tables in difftest/work/report/
```

Every stage reads and writes JSON Lines under `difftest/work/` (override with `--work` or
`$DT_WORK`). `run-*` stages are resumable and can be split across machines with
`--shard i/n`; the result files are concatenated afterwards. `--limit N` runs a prefix, for
smoke tests.

## 1. Reproducibility

* **Pinned inputs.** [`tools/pins.env`](tools/pins.env) fixes the llvm-project commit (the same
  one `scripts/run_llubi_tests.sh` uses) and the Alive2 commit. `build_oracles.sh` builds llubi,
  `alive-tv` and the LLVM utilities from one LLVM build at that commit (Release, assertions on,
  RTTI and EH on, X86 target), so both oracles and every corpus filter use the same IR parser and
  verifier. It writes the exact revisions, the Z3 version and the compiler to
  `.oracles/versions.json`. `collect` refuses checkouts that differ from the pins unless
  `--allow-unpinned` is given, and records the revisions it used in `corpus/corpus.json`.
* **Provenance.** `dt provenance` writes `work/provenance.json`: pins, oracle build record, tool
  `--version` strings, the lean-nano-llvm commit and whether the tree was dirty, host and time.
* **Seeds.** All randomness comes from `random.Random(derive_seed(global_seed, unit_id, purpose,
  index))` (`dt/common.py`), where `derive_seed` is the first 64 bits of SHA-256 of its arguments.
  A case therefore depends only on its own content and indices, never on enumeration order,
  parallelism or other cases. The global seed defaults to `20261127` and is recorded in
  `mutants/mutate.json` and `cases/cases.json`. llubi's own seed (`--seed`) is part of each
  execution record.
* **Content addressing.** Units, mutants, pairs and cases are identified by SHA-256 prefixes of
  their content, so re-running a stage is idempotent and results can be joined across stages.

## 2. Corpus

`dt collect` (`dt/corpus.py`) builds the corpus from four sources, in this order:

| Source | Location (at the pins) | Unit kind |
|---|---|---|
| `llvm-transforms` | `llvm/test/Transforms/{InstCombine, InstSimplify, AggressiveInstCombine, Reassociate, EarlyCSE, CorrelatedValuePropagation, SCCP, SimplifyCFG, GVN, DeadStoreElimination, MemCpyOpt, SROA}/**/*.ll` | `function` |
| `llubi-tests` | `llvm/test/tools/llubi/*.ll` | `program` |
| `alive2-tests` | `alive2/tests/alive-tv/**/*.srctgt.ll` | `pair` |
| `repo-tests` | this repository's `Tests/ll/*.ll` | `program` |

Units:

* A **function** unit is one function definition of an LLVM regression test, isolated with
  `llvm-extract --func` (which keeps the globals and declarations it references) and
  re-verified. The test's `opt -passes=` pipelines are recorded from its RUN lines.
* A **program** unit is a whole module with an entry point, executed as is.
* A **pair** unit is an Alive2 test defining `@src` and `@tgt`. Its expected verdict is
  `incorrect` if the test has an `; ERROR:` line and `correct` otherwise; `; TEST-ARGS:` and
  `; XFAIL:` are recorded.

Selection criteria. A candidate is rejected, with the reason recorded in `rejected.jsonl`, if:
the pinned LLVM cannot parse or verify it (`parse-or-verify`); `llvm-extract` fails
(`extract-failed`); the test needs `split-file` or `%S`/`%p` inputs or has no `opt -passes=` RUN
line (`unsupported-run-line`); it uses a target-specific intrinsic (`llvm.x86.*`, `llvm.aarch64.*`,
...) or inline assembly (`target-specific`), since neither oracle models targets; it has more than
200 instructions (`too-large`, configurable); or an Alive2 test lacks `@src`/`@tgt`.
Features our implementation may not support are *not* filtered out: they surface as
`ours-unsupported` or `translation-error` verdicts and are reported as coverage.

An optional fifth source is `scripts/collect_alive2_github.py`, which mines Alive2 links and
proofs from llvm-project issues and pull requests; it is not wired into `collect` because the
result depends on the date of the search and on alive2.llvm.org being reachable, so it should be
frozen into files before use.

Deduplication. Units are deduplicated by a structural hash: SHA-256 of the module after `opt
-passes=metarenamer,instnamer`, which renames every non-intrinsic symbol deterministically, so
units equal up to alpha-renaming collide. For Alive2 tests the key also includes the expected
verdict and `TEST-ARGS`, since the same IR can be a different test under different arguments
(e.g. `aggregate-input-{poison,undef,value}`). The first unit in source order (table above), then path
order, is kept; the others are listed in `duplicates.jsonl` with the unit they duplicate.

The funnel (candidates, rejections by reason, duplicates, accepted) is table `corpus_funnel`, and
the feature mix (integer, float, vector, memory, control flow, intrinsics, undef, poison) is
`corpus_features`.

## 3. Mutation

`dt mutate` (`dt/mutate.py`) derives mutants from function units and from the `@tgt` of Alive2
pair units. Operators are local and type-preserving:

| Operator | Edit |
|---|---|
| `binop-replace` | integer binary opcode to another (`add`…`xor`), dropping flags the new opcode does not allow; same for FP binops |
| `flag-toggle` | add or drop one poison-generating flag: `nuw`/`nsw` (`add`, `sub`, `mul`, `shl`, `trunc`), `exact` (`udiv`, `sdiv`, `lshr`, `ashr`), `disjoint` (`or`), `nneg` (`zext`, `uitofp`), `samesign` (`icmp`), and the fast-math flags `nnan`/`ninf`/`nsz` |
| `pred-replace` | `icmp`/`fcmp` predicate to another |
| `const-replace` | scalar integer constant `c` to one of {0, 1, -1, c+1, c-1, -c, ~c, INT_MIN, INT_MAX, w-1} (wrapped to the width) |
| `operand-swap` | swap the two operands of a binop, compare or `select`; swap the successors of a conditional `br` |
| `operand-replace` | replace an operand by another value of the same type that dominates the use (a parameter, an entry-block value, or an earlier value of the same block) |
| `poison-inject`, `undef-inject` | replace an operand by `poison` / `undef` |
| `freeze-insert` | insert `freeze` on an operand |
| `cast-replace` | `zext`↔`sext`, `uitofp`↔`sitofp`, `fptoui`↔`fptosi` |
| `instr-delete` | delete an instruction, replacing its uses by one of its operands |

Procedure. All sites (operator, line, choice) of a unit are enumerated in a fixed order and
shuffled with the unit's derived seed; the first `--per-unit` sites give first-order mutants. An
order-*k* mutant (`--max-order k`) applies *k* sites in sequence, re-enumerating after each
step. Each mutant is re-verified by the pinned LLVM and classified `ok`, `invalid` (verifier
rejects it, e.g. a dominance violation), `noop` (prints identically to its parent) or
`duplicate` (same text as an earlier mutant of the same parent). Only `ok` mutants are used.
Every mutant records its parent, seed, and each applied site with the instruction before and
after. Table `mutation_operators` gives the validity rate per operator.

## 4. Test cases

### 4.1 Execution cases (llubi)

`dt cases` (`dt/drivers.py`) makes every program unit, function unit and function mutant
executable. llubi only runs an entry point without parameters or with `main`'s signature, so
for a function `@f` with parameters we generate, per argument vector, a module that adds

```llvm
define i32 @__dt_main() {
  %dt.p0 = alloca [64 x i8], align 16          ; one per ptr parameter
  call void @llvm.memset.p0.i64(ptr %dt.p0, i8 R, i64 64, i1 false)
  %dt.r = call T @f(<constant arguments>)
  ret i32 0
}
```

Arguments are drawn per parameter: integers from the boundary set {0, 1, -1, 2, INT_MIN,
INT_MIN+1, INT_MAX, INT_MAX-1} with probability 0.5 and uniformly otherwise; floating-point
values from {±0, ±1, ±inf, qNaN, smallest subnormal, largest finite} with probability 0.5 and as
uniform bit patterns otherwise; vectors element-wise; `poison` with probability 0.05 except for
`noundef` parameters. Pointers point to a fresh 64-byte buffer filled with a random byte.
Functions with aggregate, scalable-vector, `byval`/`sret`/`inalloca`, non-zero address space or
x86_fp80/fp128/ppc_fp128 parameters, or varargs, are recorded in `not-executable.jsonl`. Driver
modules are verified by the pinned LLVM before use. Default: 4 argument vectors per function.

### 4.2 Refinement pairs (Alive2)

`dt pairs` (`dt/pairs.py`) builds pairs (`src`, `tgt`) from four origins:

* `alive2-test`: the Alive2 tests as is.
* `opt`: translation validation of LLVM's own tests, as in Alive2's evaluation: `tgt` is the
  test's first RUN pipeline (`opt -passes=…`) applied to the function unit. Pairs where `opt`
  leaves the function unchanged are recorded as `identity` and excluded.
* `mutation`: `src` is a unit and `tgt` one of its mutants. Because mutants are not
  optimizations, these pairs yield both verdicts.
* `mutation-opt` (optional): `src` is a mutant and `tgt` is `opt` applied to it.

Pairs are content-addressed; a pair produced by two origins is kept once, under the first
origin in the order above.

## 5. Oracles and verdicts

### 5.1 llubi (`dt/oracle_llubi.py`)

Both interpreters get the module on standard input with identical options (`--verbose
--max-steps=100000 --entry-function=E --seed=S`, seeds 0 and 1 by default) and a 60 s wall-clock
limit. Each run gets exactly one verdict, by the first rule that applies:

1. `invalid`: llubi rejects the module (parse or verifier error).
2. `timeout`: either side hit the limit (`timeout_side` says which).
3. `llubi-crash`: llubi died from a signal (reference failure).
4. `ours-crash`: our process died from a signal or ran out of memory.
5. `ours-unsupported`: our parser rejected a module llubi accepted.
6. `match`: exit code, stdout and stderr (the trace) are identical.
7. `mismatch`: otherwise, sub-classified by the first differing channel (exit > stdout > trace)
   and the first differing trace line.

Agreement is `match / (match + mismatch)`. Outputs are stored for every non-matching run
(`--keep-outputs`), and SHA-256 digests for all runs.

### 5.2 Alive2 (`dt/oracle_alive2.py`)

`alive-tv --smt-to=10000` (ms) per pair, 120 s wall-clock limit, in two configurations:
`no-undef-input` (`--disable-undef-input`, primary: it matches our default semantics, which
disable `undef`) and `default`; Alive2 tests are additionally run with their own `TEST-ARGS`
(`test-args`) for the sanity check below. Verdicts:

* `correct`: "Transformation seems to be correct!" (`syntactic_eq` if syntactically equal);
* `incorrect`: "Transformation doesn't verify!", with `error_kind` (`value-mismatch`,
  `ub-introduced`, `poison-introduced`, `undef-introduced`, `memory-mismatch`, `other`), the
  counterexample's input values, and whether Alive2 reports the counterexample unique;
* `inconclusive`: SMT timeout, memory-out or error, or a counterexample that depends on
  approximated semantics;
* `unsupported`: a feature Alive2 does not model, or a type-check failure;
* `error`: any other outcome, including crashes and wall-clock timeouts.

Table `alive2_sanity` compares Alive2's verdicts on the Alive2 tests with the tests' own
expectations, which validates the oracle setup before any comparison with us.

### 5.3 Our side and translation to Lean (`dt/lean_emit.py`)

Each obligation is a standalone Lean file. The two functions are embedded verbatim as string
literals; the `ll_def%` elaborator parses them at elaboration time with
`LeanNanoLlvm.AST.Parser` (the parser behind `lean-nano-llvm run` and the llubi frontend) and
inserts the resulting `Definition` as a concrete AST. No IR is re-printed or re-implemented in
Python, so the statement is about exactly the IR the oracles saw. Three obligations per pair,
each checked by `lake env lean` (kernel-checked, standard axioms only) in its own process with a
300 s limit:

* `prove`: `src ⊒ tgt` by a fixed script: `llvm_refine`, then on every remaining goal the first
  of `simp_all; done`, `bv_omega`, `grind` that succeeds (`bv_decide` is excluded because it
  relies on `Lean.ofReduceBool`);
* `disprove-witness`: `¬ (src ⊒ tgt)` by `llvm_disprove [w…]` with Alive2's counterexample, when
  all its inputs are integers, floats or `poison`;
* `disprove-search`: `¬ (src ⊒ tgt)` by `llvm_disprove` (our bounded witness search).

`⊒` is refinement under `SemanticsConfig.modern` with LLVM's default little-endian 64-bit data
layout. Every file ends with `#print axioms`, and an obligation counts as `checked` only if it
depends on nothing beyond `propext`, `Classical.choice` and `Quot.sound` (otherwise
`nonstandard-axioms`). Each obligation is `checked`, `failed`, `timeout`, `translation-error` (our parser
rejected one side) or `error`. Pairs that call non-intrinsic functions or reference globals are
flagged `static_scope`, since the plain `⊒` statement has no module environment.

A pair's verdict is `proved`, `disproved`, `unknown` (neither), `translation-error`, or
`inconsistent` (both proved and disproved, an alarm). Against Alive2, the classes are:

| Alive2 \ ours | proved | disproved | unknown |
|---|---|---|---|
| correct | agree | **disagree** (we refute a verified pair) | proof gap |
| incorrect | **disagree** (we prove a refuted pair) | agree | disproof gap |

Disagreements and inconsistencies go to `report/refinement-triage.jsonl` for manual triage. A
disagreement is a semantic divergence between Alive2 and us, a bug in either, or a difference
in configuration (undef inputs, data layout), and each needs a written root cause.

## 6. Results format

| File | One row per |
|---|---|
| `corpus/units.jsonl`, `rejected.jsonl`, `duplicates.jsonl` | candidate unit |
| `mutants/mutants.jsonl` | drawn mutant (any status) |
| `pairs/pairs.jsonl`, `skipped.jsonl` | pair / pair not formed |
| `cases/cases.jsonl`, `not-executable.jsonl` | execution case / subject without a driver |
| `results/llubi.jsonl` | (case, llubi seed) |
| `results/alive2-<config>.jsonl` | pair |
| `results/lean.jsonl` | (pair, obligation) |

`dt report` (`dt/report.py`) derives every table from these files only, and writes each as CSV,
a booktabs LaTeX table and Markdown (`report/summary.md`): `corpus_funnel`, `corpus_features`,
`mutation_operators`, `llubi_verdicts`, `llubi_mismatch_channels`, `alive2_verdicts`,
`alive2_sanity`, `lean_obligations`, `refinement_confusion`, `refinement_summary` and `cost`. Each record carries its
unit's feature classes, so any table can be broken down by feature.

## 7. Threats to validity (to address in the paper)

* **Oracle disagreement is not ground truth.** llubi and Alive2 can be wrong. Each disagreement
  is triaged by hand; `alive2_sanity` checks Alive2 against its own tests.
* **Configuration alignment.** Our `⊒` disables `undef`, which is why `--disable-undef-input` is
  the primary Alive2 configuration. Pairs whose IR contains `undef` literals are flagged by the
  `undef` feature class and should be reported separately.
* **Corpus bias.** LLVM's tests target optimizations already implemented, so `opt` pairs are
  mostly correct; mutation pairs balance the verdicts. Stratified tables by origin keep these
  populations apart.
* **Input sampling.** Execution covers a few argument vectors per function. Refinement covers
  all inputs symbolically, so the two experiments complement each other.
* **Mutation equivalence.** Some mutants are semantically equivalent to their parent; for
  refinement they are simply `correct` pairs, and for execution they are still valid programs.

## 8. Status

Phase 1 (infrastructure and data collection) is complete; the large-scale runs (phase 2) start
after the module refactor. A smoke test on 25 files per source (InstCombine and InstSimplify),
with the oracles built at the pins, gave: 129 units, 354 valid first-order mutants, 436 pairs and
1,487 execution cases; 300 llubi runs, all `match`; Alive2 verdicts on all 436 pairs, and the
sanity check agreeing with every decided Alive2 test (4 inconclusive); and 177 Lean obligations
on a 1/6 shard, with no disagreement with Alive2 (32 agree, 25 proof or disproof gaps, mostly
intrinsic calls, memory and external calls that the tactics do not yet handle).
