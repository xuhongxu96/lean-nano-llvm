# Bugs found by the phase-2 differential campaign

Every entry was confirmed by hand: a minimized reproducer, the pinned oracle's behaviour on it,
and the LangRef text (llvm-project `a58c4ab`, `llvm/docs/LangRef.md`) that decides who is right.
Reproducers live in `Tests/ll/` (semantics, `scripts/run_ll_tests.sh`), `Tests/llubi-regress/`
(byte-exact llubi output, goldens from the pinned llubi, `scripts/run_llubi_regress.sh`) and
`Tests/Refinement/Difftest.lean` (refinement and tactics). Triage rules (`dt/triage_rules.py`)
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
| B9 | A call to a module-defined `@malloc`/`@calloc` (and `operator new`) is replaced by the builtin allocator instead of executing the definition. | (a defined function is executed as defined) | `defined_allocator_is_called.ll` |

Follow-up instances (same ids): **B1** a declared callee's parameter attributes also apply to
the arguments (`decl_param_noundef_ub.ll`); **B3** a call without an explicit type has the
non-variadic type of its arguments, so calling a variadic function that way is UB
(`call_signature_mismatch_vararg_ub.ll`; the IR parser now records each call's function type,
`CallSiteInfo.fnTy?`); **B4** conversions (`fpext`, `fptrunc`) used the module's configuration
instead of the function's denormal mode (`denormal_fpenv_fpext.ll`); **B8** an exact conversion
leaves a zero low double with the sign of the high double (`ppc_fp128_sitofp_negative.ll`).

## Output-only differences (P)

Same execution, different text in our llubi-compatible `--verbose` output. Each has a
normalizer in `triage_rules.NORMALIZERS`.

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
| P13 | Variadic arguments are not printed on function entry (llubi: `vaarg[i] = <value>`), and a call's function type was printed from the callee instead of the call. |

Follow-ups: **P1** specialized nodes (`!DIFile(...)`) are MDNodes too; **P2** intrinsic
declarations carry LLVM's implicit attribute sets (table generated from the pinned `opt` by
`difftest/tools/gen_intrinsic_attrs.py`).

## Tactic bugs (T)

| Id | Bug |
|---|---|
| T1 | `llvm_disprove`'s witness search evaluates loops in Lean's interpreter without a recursion bound; on a large trip count Lean aborts the whole process ("deep recursion was detected at 'interpreter'", uncaught, exit 134) despite the search's 2000 ms budget. Example: pair `32746c0f44bea3e7`. |

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
| O1 | llubi aborts (assertion failures, e.g. "Cannot get layout of opaque structs") on modules the verifier accepts. |

## Retracted candidates

Kept so that the triage is auditable.

* *llubi ignores the GEP index width.* The test module was invalid (`ptrtoaddr` must produce
  the 32-bit address type); llubi rejected it ("input module is broken").
* *llubi loads a pointer from integer bytes as poison.* It does not (LangRef `bitcast`: a
  pointer with the integer's address and no provenance, which is what both implement); the
  poison in the case came from `!align` (see B1, P10).
