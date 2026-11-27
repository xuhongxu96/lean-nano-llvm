# Bugs found by the phase-2 differential campaign

Every entry was confirmed by hand: a minimized reproducer, the pinned oracle's behaviour on it,
and the LangRef text (llvm-project `a58c4ab`, `llvm/docs/LangRef.md`) that decides who is right.
Reproducers live in `Tests/ll/` and are marked `; XFAIL: difftest bug <id>`: the `EXPECT_*`
lines state the correct behaviour, so `scripts/run_ll_tests.sh` reports XPASS (and fails) once
a bug is fixed. Triage rules (`dt/triage_rules.py`) attribute campaign runs to these ids; the
per-bug counts are table `triage_bugs` of `dt report`.

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

## Output-only differences (P)

Same execution, different text in our llubi-compatible `--verbose` output. Each has a
normalizer in `triage_rules.NORMALIZERS`.

| Id | Difference |
|---|---|
| P1 | Metadata nodes numbered differently (llubi uses LLVM's module slot order). |
| P2 | Attribute groups numbered differently. |
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

## Tactic bugs (T)

| Id | Bug |
|---|---|
| T1 | `llvm_disprove`'s witness search evaluates loops in Lean's interpreter without a recursion bound; on a large trip count Lean aborts the whole process ("deep recursion was detected at 'interpreter'", uncaught, exit 134) despite the search's 2000 ms budget. Example: pair `32746c0f44bea3e7`. |

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
