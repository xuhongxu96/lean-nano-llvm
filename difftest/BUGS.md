# Bugs found by the phase-2 differential campaign

Every entry was confirmed by hand: a minimized reproducer, the pinned oracle's behaviour on it,
and the LangRef text (llvm-project `a58c4ab`, `llvm/docs/LangRef.md`) that decides who is right.
Reproducers live in `Tests/ll/` and run in CI with `scripts/run_ll_tests.sh`: `; EXPECT_*`
comments check `lean-nano-llvm run` (semantics), and `; LLUBI-*` comments, generated from the
pinned llubi by `scripts/gen_llubi_expect.sh`, check the `llubi --verbose` output byte for byte
(the `llubi_*.ll` files and every difftest reproducer). Bugs in the refinement relation and the
tactics are covered by `Tests/Refinement/Difftest.lean`. Triage rules (`dt/triage_rules.py`)
attribute campaign runs to these ids; the per-bug counts are table `triage_bugs` of `dt report`.

**Status.** All B, P and T bugs are fixed: B1-B9 and T1 in `451acab`, P7-P9 and P11-P12 in
`67a4ec4`, P1-P6 and P10 in `7a7bd12`. Re-running the first run's disagreeing cases with the
fixed code showed further instances, fixed in the following commit: B1 at calls to declared
functions, B3 for variadic call types, B4 for `fpext`/`fptrunc`, B8 for the sign of a zero low
double, P1 for debug-info nodes, P2 for intrinsic declarations, and the new P13. Each reproducer was first committed as an
XFAIL test that failed on the unfixed code, and passes now. O1 is a bug in llubi (not ours).
The phase-2 campaign's first run (`results-run1-d3ba2af/`) used the unfixed code; it is the run
that found these bugs.

Ids: `B` semantic bugs in lean-nano-llvm, `P` differences in our llubi-compatible output only
(same execution), `T` bugs in our proof tactics, `O` oracle bugs.

## Semantic bugs (B)

| Id | Bug | LangRef | Reproducers |
|---|---|---|---|
| B1 | `noundef` is checked before the poison-generating attributes (`range`, `nofpclass`, `nonnull`, `align`) of the same parameter or return value are applied; call-site and callee parameter attributes are applied in two separate passes. A value made poison by `range` therefore escapes `noundef`, where LangRef (and llubi's `handleAttributes`) makes it immediate UB. Also affects refinement: our `llvm_disprove` kernel-checks a refutation of Alive2 test pair `ef0c2671893037dc`, which Alive2 proves correct. | Parameter Attributes: `noundef`, `range` | `param_noundef_after_range.ll`, `callsite_noundef_callee_range.ll`, `ret_noundef_after_range.ll` |
| B2 | An unlabeled entry block is named `entry` instead of taking the next unnamed slot number (`%0`, or `%N` after unnamed parameters), so `phi [v, %0]` finds no incoming value. | Functions | `phi_unnamed_entry_block.ll`, `phi_unnamed_entry_block_after_arg.ll` |
| B3 | A call whose function type differs from the callee's signature (parameter types, count) stops with a static error instead of immediate UB; at calls to declarations the signature is not checked at all. | `call`: "If the function signature does not match the function type of the call, the behavior is undefined" | `call_signature_mismatch_arg_ub.ll`, `call_signature_mismatch_count_ub.ll` |
| B4 | `denormal_fpenv` is ignored when it appears in an attribute group (`attributes #0 = { denormal_fpenv(...) }`, the form LLVM prints), and the `float:` override is applied to every type. With input mode `preservesign`/`positivezero` subnormal inputs must be treated as zero. | `denormal_fpenv` | `denormal_fpenv_attr_group.ll`, `denormal_fpenv_float_override.ll` |
| B5 | A signaling-NaN `float`/`half`/`bfloat` literal written in 64-bit hex is quieted (quiet bit set) when parsed. | Simple Constants (hex floating-point) | `snan_float_literal_double_hex.ll` |
| B6 | A datalayout pointer spec with flags (`pe1:64:64:64:32`) is read as the spec of address space 0. | Data Layout: `p[<flags>][<as>]` | `datalayout_pointer_flags.ll` |
| B7 | `!range` metadata with more than one range is ignored. | `range` metadata | `load_range_list_ub.ll` |
| B8 | Conversions into `ppc_fp128` (`fpext`, `sitofp`, `uitofp`) produce an encoding other than LLVM's double-double layout (our `ppc_fp128` arithmetic itself uses the right one). | Floating-Point Types | `ppc_fp128_fpext_layout.ll`, `ppc_fp128_sitofp_layout.ll` |
| B10 | `x86_fp80` (the x87 extended format, not an IEEE interchange format) was 79 bits wide in memory and for `bitcast`, without its explicit integer bit: stores and loads of its bits were wrong and `bitcast` from/to `i80` was rejected. Non-canonical x87 encodings are now decoded as `APFloat` does (unnormals and pseudo-infinities/NaNs are NaN, pseudo-denormals have exponent 1). | Data Layout, Floating-Point Types | `x86_fp80_memory_layout.ll`, `x86_fp80_bitcast.ll`, `x86_fp80_noncanonical_encodings.ll` |
| B11 | An `llvm.assume` operand bundle on a pointer other than the modelled ones (`separate_storage`) ignored a poison pointer, which llubi reports as immediate UB ("Assume on poison pointer."). | `llvm.assume` operand bundles | `llubi_assume_separate_storage_poison.ll` |
| B9 | A call to a module-defined `@malloc`/`@calloc` (and `operator new`) is replaced by the builtin allocator instead of executing the definition. | (a defined function is executed as defined) | `defined_allocator_is_called.ll` |
| B12 | `llvm.fabs` and `llvm.copysign` on `ppc_fp128` treated the double pair as one IEEE binary128 value (sign = the low double's sign bit, only that bit changed). A double-double's sign is its high double's, and a sign change negates both doubles (`DoubleAPFloat::changeSign`), so `fabs(-1 + 2^-1074)` was `(1, 2^-1074)`, value `1 + 2^-1074`, instead of `1 - 2^-1074`. From case `6357d1590901c055`. | `llvm.fabs`, `llvm.copysign` | `llubi_ppc_fp128_sign_ops.ll` |

Follow-up instances (same ids): **B1** a declared callee's parameter attributes also apply to
the arguments (`decl_param_noundef_ub.ll`); **B3** a call without an explicit type has the
non-variadic type of its arguments, so calling a variadic function that way is UB
(`call_signature_mismatch_vararg_ub.ll`; the IR parser now records each call's function type,
`CallSiteInfo.fnTy?`; its first version compared named struct types unresolved, a regression
found by campaign run 2 and fixed with `call_named_struct_type.ll`; the affected run-2 cases are
re-run); **B4** conversions (`fpext`, `fptrunc`) used the module's configuration
instead of the function's denormal mode (`denormal_fpenv_fpext.ll`); **B8** an exact conversion
leaves a zero low double with the sign of the high double (`ppc_fp128_sitofp_negative.ll`), for
integer conversions only (`llubi_ppc_fp128_zero_low_sign.ll`); decimal and special `ppc_fp128`
literals were IEEE binary128 encodings instead of double-doubles, and `fdiv`/`frem` did not
compute in APFloat's 106-bit legacy format (`llubi_ppc_fp128_div_rem.ll`).

**B10** follow-up: `x86_fp80` values are now represented by their x87 encoding, explicit integer
bit included (`FloatFormat.explicitInt`; the IEEE library classifies x87 encodings as `APFloat`
does). A NaN's integer bit used to be lost (a 79-bit format has no room for it) where `APFloat`
keeps it through `bitcast`, NaN propagation, `fneg`/`fabs`/`copysign`, `select`, `freeze` and
memory; an unnormal read from bits is a NaN with the maximal exponent and a pseudo-denormal has
exponent 1, as `bitcastToAPInt` writes them back (`IEEEFloat.readEncoding`); `undef`/`freeze`
values are drawn over all 80 bits, as llubi draws them (`llubi_x86_fp80_explicit_int_bit.ll`).
Randomized check against llubi (450 runs over every encoding class, 3 seeds): 2,477 -> 3
differing lines, all O3. Corpus cases with `x86_fp80`: 1,097 -> 1,197 of 1,268 runs agree; the
rest are O3 and llubi's unsupported `llvm.canonicalize` and libcalls.

Coverage: `f0x<hex>` floating-point literals (the bit pattern of the type; LLVM's current
printer form) were rejected by our parser, so 3,859 corpus cases were unsupported; they now
parse (`llubi_f0x_literals.ll`), and 7,596 of their 7,718 llubi runs agree.

B8 follow-up: `ppc_fp128` division is computed in LLVM's legacy 106-bit format, whose normal range
ends at 2^-969 (`minExponent = -1022 + 53`); a quotient below 2^-968 is rounded to a multiple of
2^-1074 (`ppcLegacyDiv`; our 11-bit-exponent stand-in rounded it more finely), and llubi's decimal
rendering of such a value round-trips through that format too (`ppcDecimal?`). Randomized check
against llubi: 1,400 `fdiv`/`frem` over the whole exponent range, 0 differences (38 before).

## Output-only differences (P)

Same execution, different text in our llubi-compatible `--verbose` output. Each has a
normalizer in `triage_rules.NORMALIZERS` and a `Tests/ll/llubi_*.ll` reproducer.

| Id | Difference |
|---|---|
| P1 | Metadata nodes numbered differently. llubi prints the IR parser's `MDNode` creation order (a forward reference to a numbered node creates a temporary node that takes a number; inline nodes are uniqued), which we now replay. |
| P2 | Attribute groups numbered differently: a declaration without attributes followed by `define` read the keyword as an attribute, adding a spurious attribute set. |
| P3 | `switch` printed without its metadata attachments. |
| P4 | `alloca ..., addrspace(N)` printed as `addrspace ( N)`. |
| P5 | Escapes in quoted names kept verbatim by the parser and re-escaped (`@"\01LC"` printed `@"\5C01LC"`). |
| P6 | `captures(...)` printed without its components. |
| P7 | Signed-division-overflow UB message omits `LHS: a, RHS: b`. |
| P8 | Mismatched-signature UB message ends with an extra `.`. |
| P9 | llubi prints `Object base:` of memory-intrinsic out-of-bounds reports in lowercase hex. |
| P10 | Immediate UB at the same instruction, reported with a different reason (e.g. llubi checks library-call arguments for poison before reading C-string arguments). |
| P11 | `dereferenceable` assume-bundle size printed unsigned (llubi: signed). |
| P12 | Alloca-size UB messages end with an extra `.`. |
| P14 | A direct call whose type differs from the callee's takes the callee's address (LLVM calls through it as a pointer) and llubi allocates a function object for it, which shifts later stack addresses. A personality function (`personality ptr @f`) is such a constant use too (`Declaration.personality?`). |
| P15 | A load that violated both `!noundef` and `!dereferenceable` reported the `!dereferenceable` violation; llubi checks undefined bits, then the poison-generating metadata, then `!noundef`, then `!dereferenceable` (`Semantics.loadValueChecks`). |
| P16 | A `blockaddress` pointer printed its object's internal name instead of the block label (`[L1]`); a pointer to an unnamed global printed `[@0]` instead of `[@]`; a store to a function object was reported as a write to constant memory instead of an out-of-bounds access (function objects are not constant in llubi). |
| P13 | Variadic arguments are not printed on function entry (llubi: `vaarg[i] = <value>`), and a call's function type was printed from the callee instead of the call. |

Follow-ups: **P1** specialized nodes (`!DIFile(...)`) are MDNodes too; metadata nodes are keyed by all their tokens (nodes differing only in float operands were
uniqued into one); **P2** a function's trailing `align N` is its alignment, not an attribute;
intrinsic declarations carry LLVM's implicit attribute sets, for all 17,094 intrinsics of the pinned
LLVM (`Intrinsic::getFnAttributes`, dumped by `difftest/tools/gen_intrinsic_attrs.py`), found by
base name as `Intrinsic::lookupIntrinsicID` does (the first table covered only the corpus's
intrinsics and guessed others from a neighbour with the same prefix).

## Tactic bugs (T)

| Id | Bug |
|---|---|
| T1 | `llvm_disprove`'s witness search evaluates loops in Lean's interpreter without a recursion bound; on a large trip count Lean aborts the whole process ("deep recursion was detected at 'interpreter'", uncaught, exit 134) despite the search's 2000 ms budget. Example: pair `32746c0f44bea3e7`. |
| T2 | `llvm_disprove`'s search was bounded by wall-clock time (2000 ms), so whether a witness was found depended on the machine's load: the result was not reproducible. It is now bounded by heartbeats (Lean's allocation counter, the unit of `maxHeartbeats`; default 20,000 ×1000, `(heartbeats := N)`), identical across runs and loads; `(timeout := ms)` remains as an optional safety net. Calibration: every witness found in run 2 cost under 40 ×1000 heartbeats; 2 s of the old search cost 2,000–43,000. |
| T3 | `llvm_disprove` found a valid witness but could not certify it ("could not close refutation goal", 12,921 obligations in run 2): its certifier stepped both programs with deterministic-step lemmas for a fixed set of instructions (no calls, `extractvalue`, `fcmp`, `ret void`, …), and values computed in a loop were left unevaluated. The target's behaviour is now certified by running the executable interpreter in the kernel (`runSteps_sound`: any interpreter run is a behaviour), so any target instruction is supported; the source side, whose behaviours must all be known, gained deterministic lemmas for intrinsic calls, `extractvalue`, `fcmp` and `ret void`, and evaluates register values when stepping loops. On a random sample of 60 such obligations, 49 are now certified. Remaining: `fcmp` on values computed by float conversions, `alloca`/memory on the source side, non-intrinsic calls. Example: pair `0076a63f65e69b99`. |

## Harness bugs (H)

Bugs in the campaign harness itself, found by the sanity checks and the triage; all fixed.

| Id | Bug |
|---|---|
| H1 | alive-tv checks every function pair of a file; the verdict was "correct" if any pair was (fixed: the section of the pair under test). Made our correct refutation of `34374bb544b3d783` look like a disagreement. |
| H2 | Float counterexamples were emitted as `FloatType.*` instead of `AST.FloatType.*`, so every float witness failed to elaborate. |
| H3 | Lean 4.28 prints `error(<code>):`; such errors were classified `error` instead of `failed`. |
| H4 | The Alive2 sanity check read a test's expected verdict from `; ERROR:` lines only, misreading CHECK-based, unasserted and XFAIL tests. |

## Oracle bugs (O)

| Id | Bug |
|---|---|
| O2 | llubi ignores a `getelementptr` index whose element type has size 0 (`{}`, `[0 x T]`), even a poison one, and returns the base pointer; LangRef ("Poison Values": most instructions return poison when an argument is poison, with a `getelementptr` example) makes the result poison, as ours is. From case `661f6eb3623f33b9`. |
| O1 | llubi aborts (assertion failures, e.g. "Cannot get layout of opaque structs") on modules the verifier accepts. |
| O3 | Not a bug, an `APFloat` artefact: converting an `x86_fp80` NaN to a narrower type keeps the x87 integer bit in a significand bit that `bitcastToAPInt` drops but `bitwiseIsEqual` sees, so llubi prints such a NaN as hex (`double 0x7FF8000000000000`) although its bits are those it prints as `NaN`. A `double` has no room for the hidden bit; triage normalizer `x87-nan-hidden-bit`. |

## Retracted candidates

Kept so that the triage is auditable.

* *llubi ignores the GEP index width.* The test module was invalid (`ptrtoaddr` must produce
  the 32-bit address type); llubi rejected it ("input module is broken").
* *llubi loads a pointer from integer bytes as poison.* It does not (LangRef `bitcast`: a
  pointer with the integer's address and no provenance, which is what both implement); the
  poison in the case came from `!align` (see B1, P10).
