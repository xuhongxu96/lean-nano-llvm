"""The triage knowledge base: normalizers, llubi rules and refinement verdicts, each with the root
cause established by hand (minimized reproducer under `Tests/`, bug id in `difftest/BUGS.md`).

Adding a rule is a claim about a root cause. Every rule must be specific enough that it cannot
absorb an unrelated difference: it states what the oracle printed, what we printed, and, where
needed, a property of the module itself (`module_re`).
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Callable


@dataclass(frozen=True)
class Normalizer:
    """Removes one printing difference. `llubi`/`ours` are (pattern, replacement) applied to that
    side's stderr; `both` to both sides."""
    id: str
    bug: str
    doc: str
    llubi: tuple[tuple[str, str], ...] = ()
    ours: tuple[tuple[str, str], ...] = ()
    both: tuple[tuple[str, str], ...] = ()

    def apply(self, text: str, side: str) -> str:
        subs = self.both + (self.llubi if side == "llubi" else self.ours)
        for pat, rep in subs:
            text = re.sub(pat, rep, text, flags=re.M)
        return text


NORMALIZERS: list[Normalizer] = [
    Normalizer("md-slot", "P1", "metadata nodes are numbered differently (`!range !2` vs `!0`): llubi "
               "numbers them with LLVM's module SlotTracker, we per printed module order",
               both=((r"(?<=[\s,(])!\d+\b", "!N"),)),
    Normalizer("attr-group", "P2", "attribute groups are numbered differently (`#0` vs `#2`)",
               both=((r"(?<=\S) #\d+\b", " #A"),)),
    Normalizer("switch-metadata", "P3", "`switch` is printed without its metadata attachments "
               "(`!prof`, `!make.implicit`, ...)",
               llubi=((r"^(\s*\])(?:, ![-\w.]+ !\w+)+( jump to | at @)", r"\1\2"),)),
    Normalizer("addrspace-space", "P4", "`alloca ..., addrspace(N)` is printed as `addrspace ( N)`",
               ours=((r"addrspace \( (\d+)\)", r"addrspace(\1)"),)),
    Normalizer("quoted-name-escape", "P5", "escapes in quoted names are kept verbatim by our parser "
               "and re-escaped when printed (`@\"\\01LC\"` printed as `@\"\\5C01LC\"`)",
               ours=((r"\\5C", r"\\"),)),
    Normalizer("captures-components", "P6", "`captures(...)` is printed without its components "
               "(`captures(none)`, `captures(address)` printed as `captures()`)",
               llubi=((r"captures\([^)]*\)", "captures()"),)),
    Normalizer("sdiv-overflow-operands", "P7", "the signed-division-overflow UB message omits llubi's "
               "`LHS: a, RHS: b`",
               llubi=((r"(Signed division overflow\.) LHS: \S+, RHS: \S+$", r"\1"),)),
    Normalizer("object-base-case", "P9", "llubi prints `Object base:` of memory-intrinsic "
               "out-of-bounds reports in lowercase hex (`0xb0`); we print uppercase",
               llubi=((r"(Object base: 0x)([0-9a-f]+)", lambda m: m.group(1) + m.group(2).upper()),)),
    Normalizer("assumption-size-signed", "P11", "llubi prints the size of a `dereferenceable` "
               "assume bundle as a signed integer (`dereferenceable(-1)`); we print it unsigned",
               ours=((r"dereferenceable\((18446744073709551615)\) assumption", "dereferenceable(-1) assumption"),)),
    Normalizer("alloca-size-dot", "P12", "the alloca-size UB messages end with an extra `.`",
               ours=((r"^(Immediate UB detected: Alloca with allocation size that (?:exceeds the maximum "
                      r"object size|overflows uint64_t)\. Size: \d+)\.$", r"\1"),)),
    Normalizer("signature-mismatch-dot", "P8", "the mismatched-signature UB message ends with an extra `.`",
               ours=((r"(mismatched signature\. Expected: .*)\.$", r"\1"),)),
]


@dataclass(frozen=True)
class Rule:
    id: str
    cls: str
    bug: str | None
    root_cause: str
    verdicts: tuple[str, ...] = ("mismatch",)
    llubi_re: str | None = None      # searched in llubi's (normalized) stderr
    ours_re: str | None = None       # searched in our (normalized) stderr
    llubi_not_re: str | None = None
    ours_not_re: str | None = None
    ldiff_re: str | None = None      # searched in llubi's first differing line
    odiff_re: str | None = None      # searched in our first differing line
    exits: tuple[int | None, int | None] | None = None
    module_re: str | None = None     # searched in the case module
    pred: Callable[..., bool] | None = None  # (llubi, ours, ldiff, odiff, module) -> bool

    def matches(self, *, verdict: str, llubi: str, ours: str, ldiff: str, odiff: str,
                lexit, oexit, module: str | None) -> bool:
        if verdict not in self.verdicts:
            return False
        checks: list[tuple[str | None, str, bool]] = [
            (self.llubi_re, llubi, True), (self.ours_re, ours, True),
            (self.llubi_not_re, llubi, False), (self.ours_not_re, ours, False),
            (self.ldiff_re, ldiff, True), (self.odiff_re, odiff, True)]
        for pat, text, want in checks:
            if pat is not None and bool(re.search(pat, text, re.M)) != want:
                return False
        if self.exits is not None and (lexit, oexit) != self.exits:
            return False
        if self.module_re is not None and (module is None or not re.search(self.module_re, module, re.M)):
            return False
        if self.pred is not None and not self.pred(llubi=llubi, ours=ours, ldiff=ldiff, odiff=odiff,
                                                   module=module):
            return False
        return True



# --- helpers for rules that need to look at values ----------------------------------------------

FP_MIN_NORMAL = {"half": 6.103515625e-05, "bfloat": 1.1754943508222875e-38,
                 "float": 1.1754943508222875e-38, "double": 2.2250738585072014e-308}
FP_EXP_MASK = {"half": (0x7C00, 16), "bfloat": (0x7F80, 16), "float": (0x7F800000, 32),
               "double": (0x7FF0000000000000, 64)}
_VAL_RE = re.compile(r"^\s*(?:(?:<\d+ x )?(?P<ty>half|bfloat|float|double)>? (?P<arg>%[-\w.$\"]+) = (?P<aval>.+)|"
                     r"(?P<res>%[-\w.$\"]+) = .*=> (?P<rval>.+))$")


def _is_subnormal(ty: str, text: str) -> bool:
    """`text` is a printed FP value, or a vector / aggregate of them (`{ float 1.0, poison }`,
    `<half 0x0001, ...>`): true if it is, or has an element that is, subnormal."""
    text = text.strip()
    if text[:1] in "{<[" and text[-1:] in "}>]":
        return any(_is_subnormal(ty, e) for e in text[1:-1].split(","))
    for t in ("half", "bfloat", "float", "double"):
        if text.startswith(t + " "):
            ty, text = t, text[len(t) + 1:]
    if text.startswith(("0x", "f0x")):
        try:
            bits = int(text.split("x", 1)[1], 16)
        except ValueError:
            return False
        if text.startswith("0x") and ty in ("float", "half", "bfloat") and bits > (1 << 32):
            return False  # double-hex spelling of a narrower type: not decoded here
        mask, _ = FP_EXP_MASK.get(ty, (0, 0))
        return mask != 0 and bits & mask == 0 and bits & ~mask & ~(1 << (FP_EXP_MASK[ty][1] - 1)) != 0
    try:
        v = abs(float(text))
    except ValueError:
        return False
    return 0 < v < FP_MIN_NORMAL.get(ty, 0)


def fp_diff_has_subnormal_input(*, llubi: str, odiff: str, **_) -> bool:
    """The first differing instruction is an FP operation with a subnormal operand (operand values
    are looked up in the trace lines that precede it on llubi's side)."""
    m = re.match(r"^\s*%[-\w.$\"]+ = (?:\w+ )*?(?:fadd|fsub|fmul|fdiv|frem|fneg|fpext|fptrunc|fcmp|call)\b"
                 r"[^=]*?(half|bfloat|float|double)\b(.*?)=>", odiff)
    if not m:
        return False
    ty, ops = m.group(1), m.group(2)
    vals: dict[str, str] = {}
    for line in llubi.splitlines():
        if line.strip() and line.strip() == odiff.split("=>")[0].strip():
            break
        v = _VAL_RE.match(line)
        if v and v.group("arg"):
            vals[v.group("arg")] = v.group("aval")
        elif v and v.group("res"):
            vals[v.group("res")] = v.group("rval")
    for tok in re.findall(r"%[-\w.$\"]+|-?\d+\.\d+e[-+]\d+|f?0x[0-9A-Fa-f]+", ops):
        val = vals.get(tok, tok)
        if _is_subnormal(ty, val):
            return True
    return False


def fp_diff_output_only(**kw) -> bool:
    return not fp_diff_has_subnormal_input(**kw)


def float_values_differ_in_quiet_bit(*, ldiff: str, odiff: str, **_) -> bool:
    """The two lines are identical except for float hex values that differ in the quiet-NaN bit."""
    a = re.findall(r"0x([0-9A-F]{8})\b", ldiff)
    b = re.findall(r"0x([0-9A-F]{8})\b", odiff)
    if not a or len(a) != len(b) or re.sub(r"0x[0-9A-F]{8}\b", "", ldiff) != re.sub(r"0x[0-9A-F]{8}\b", "", odiff):
        return False
    return any(int(x, 16) ^ int(y, 16) == 0x00400000 for x, y in zip(a, b)) and \
        all(int(x, 16) ^ int(y, 16) in (0, 0x00400000) for x, y in zip(a, b))


def same_ub_point(*, llubi: str, ours: str, ldiff: str, odiff: str, **_) -> bool:
    """Both sides report immediate UB at the same point (identical traces up to the UB line) and
    nothing differs after it: the outcome (UB) agrees and only the stated reason differs."""
    if not (ldiff.startswith("Immediate UB detected:") and odiff.startswith("Immediate UB detected:")):
        return False
    la, lo = llubi.splitlines(), ours.splitlines()
    try:
        i, j = la.index(ldiff), lo.index(odiff)
    except ValueError:
        return False
    return i == j and la[:i] == lo[:j] and la[i + 1:] == lo[j + 1:]

DENORMAL_GROUP = r"^attributes #\d+ = \{[^}]*denormal_fpenv"
FP_RESULT = r"=> (?:half|bfloat|float|double|<\d+ x (?:half|bfloat|float|double)>|\{)|=> poison"

POISON_ATTR = r"(range\(|nofpclass\(|nonnull|align \d)"

LLUBI_RULES: list[Rule] = [
    # --- our semantic bugs --------------------------------------------------------------------
    Rule("B1-noundef-after-poison-attrs", "ours-semantic-bug", "B1",
         "noundef is checked before the poison-generating attributes (range, nofpclass, nonnull, "
         "align) of the same parameter or return value are applied, and call-site and callee "
         "attributes are applied in separate passes; LangRef and llubi apply all poison-generating "
         "attributes first, then noundef",
         llubi_re=r"violates noundef attribute\.$", ours_not_re=r"violates noundef attribute",
         module_re=POISON_ATTR),
    Rule("B2-unnamed-entry-block", "ours-semantic-bug", "B2",
         "an unlabeled entry block is named `entry` instead of taking the next unnamed slot "
         "number, so `phi [v, %N]` naming the entry block has no incoming value",
         ours_re=r"phi node \S+ has no incoming value for predecessor %entry",
         llubi_not_re=r"has no incoming value for predecessor"),
    Rule("B3-call-signature-mismatch", "ours-semantic-bug", "B3",
         "a call whose function type differs from the callee's is immediate UB (LangRef `call`); "
         "we report a static error for parameter type/count mismatches, and stop at calls to "
         "declarations before checking the signature",
         llubi_re=r"Immediate UB detected: Indirect call through a function pointer with mismatched signature",
         ours_re=r"^(Error: (Unmatched argument type|Argument count mismatch)|Unrecognized instruction:)"),
    Rule("B4-denormal-input", "ours-semantic-bug", "B4",
         "denormal_fpenv inside an attribute group is ignored (and a `float:` override is applied "
         "to every type); with input mode preservesign/positivezero an FP operation must treat "
         "subnormal inputs as zero (LangRef denormal_fpenv), and here an operand is subnormal",
         module_re=r"denormal_fpenv", ldiff_re=FP_RESULT, pred=fp_diff_has_subnormal_input),
    Rule("denormal-output-flush", "spec-gap", None,
         "llubi flushes a subnormal *result* under output mode preservesign/positivezero; LangRef "
         "allows but does not mandate this (\"It is not mandated that flushing to zero occurs\"), so "
         "keeping the subnormal is also correct (our B4 attribute loss does not change the verdict)",
         module_re=r"denormal_fpenv", ldiff_re=FP_RESULT, pred=fp_diff_output_only),
    Rule("B5-snan-literal-quieted", "ours-semantic-bug", "B5",
         "a signaling-NaN float literal written in double-hex form is quieted when parsed "
         "(LLVM keeps payload and signaling bit)",
         module_re=r"\b(?:float|half|bfloat) 0x[0-9A-F]{16}\b", pred=float_values_differ_in_quiet_bit),
    Rule("B6-datalayout-pointer-flags", "ours-semantic-bug", "B6",
         "a datalayout pointer spec with flags (`pe1:...`) is read as the spec of address space 0",
         module_re=r'target datalayout = "[^"]*\bp[uezo]+\d*[:(]', ldiff_re=r"=> (ptr|i\d+) "),
    Rule("B7-range-list", "ours-semantic-bug", "B7",
         "!range metadata with several ranges is ignored",
         module_re=r"^!\d+ = !\{i\d+ -?\d+, i\d+ -?\d+, i\d+", ldiff_re=r"!range !\w+ => poison",
         odiff_re=r"!range !\w+ => (?!poison)"),
    Rule("B8-ppc_fp128-conversion", "ours-semantic-bug", "B8",
         "conversions into ppc_fp128 (fpext, sitofp, uitofp) produce an encoding other than LLVM's "
         "double-double layout (high double in the low 64 bits)",
         odiff_re=r"= (fpext|sitofp|uitofp) [^=]* to ppc_fp128 =>", ldiff_re=r"=> ppc_fp128 "),
    Rule("B9-defined-allocator", "ours-semantic-bug", "B9",
         "a call to a module-defined @malloc/@calloc/operator new is replaced by the builtin allocator instead "
         "of executing the definition",
         ldiff_re=r"^Entering function: (malloc|calloc|_Zn[wa][jm])$",
         module_re=r"^define [^@]*@(malloc|calloc|_Zn[wa][jm])\("),
    # --- same outcome (immediate UB at the same instruction), different stated reason ---------
    Rule("B1-metadata-order-diagnostic", "ours-trace-format", "B1",
         "load metadata: llubi applies poison-generating !align/!nonnull/!range before the UB checks "
         "!dereferenceable(_or_null)/!noundef and reports the poison; we check in attachment order "
         "and report the original value. Both are UB at the same load (the B1 ordering bug, with "
         "no observable consequence here)",
         ldiff_re=r"Immediate UB detected: The value poison violates !(noundef|dereferenceable)",
         odiff_re=r"Immediate UB detected: The value (?!poison).* violates !(dereferenceable|dereferenceable_or_null)",
         pred=same_ub_point),
    Rule("ub-reason-differs", "ours-trace-format", "P10",
         "both sides report immediate UB at the same instruction with a different reason (e.g. "
         "llubi checks a library call's arguments for poison before reading its C-string "
         "arguments; we read the string first); the outcome agrees",
         pred=same_ub_point),
    # --- we do not implement a feature the oracle executes ---------------------------------------
    Rule("libcall-not-modelled", "ours-unsupported", None,
         "llubi models this external (C library) function and continues or reports UB in it; we "
         "stop at calls to declarations",
         ldiff_re=r"^Stacktrace:$", odiff_re=r"^Unrecognized instruction:.*\bcall\b"),
    Rule("ours-oom-large-allocation", "crash", None,
         "our interpreter materializes a large allocation and exceeds the 8 GB address-space limit",
         verdicts=("ours-crash",), ours_re=r"INTERNAL PANIC: out of memory"),
    Rule("llubi-abort", "oracle-bug", None,
         "llubi aborts (assertion failure or fatal error) on a module the LLVM verifier accepts",
         verdicts=("llubi-crash",)),
    # --- oracle does not implement a feature we execute ---------------------------------------
    Rule("llubi-unsupported-constant", "oracle-unsupported", None,
         "llubi does not evaluate some constant expressions (e.g. `addrspacecast`) and stops with "
         "'Unsupported constant'; we evaluate them",
         llubi_re=r"^Error: Unsupported constant: "),
    Rule("llubi-unrecognized-instruction", "oracle-unsupported", None,
         "llubi stops at an instruction or intrinsic it does not implement; we execute it",
         ldiff_re=r"^Unrecognized instruction:", odiff_re=r"^(?!Unrecognized instruction:)"),
]


def match_rule(rules: list[Rule], *, module: str | None = None, **kw) -> Rule | None:
    for r in rules:
        if r.matches(module=module, **kw):
            return r
    return None


UNSUPPORTED_FAMILIES: list[tuple[str, str]] = [
    # (family, regex on the parser message); first match wins
    ("constrained FP intrinsics (metadata arguments)", r'strLit "(round\.\w+|fpexcept\.\w+|[ou](eq|ne|gt|ge|lt|le)|ord|uno|true|false)"'),
    ("atomics (orderings, atomicrmw, cmpxchg, fence)", r'"(unordered|monotonic|acquire|release|acq_rel|seq_cst|atomicrmw|cmpxchg|fence|syncscope)"'),
    ("exception handling (EH pads, invoke, landingpad)", r'"(cleanuppad|catchswitch|catchpad|catchret|cleanupret|landingpad|invoke|resume)"'),
    ("function-level metadata attachments (!prof, !dbg, ...)", r"define body\): expected \S+ got \S+metaId"),
    ("block comments /* ... */", r"Tok\.star in type"),
    ("hex float literal f0x... in constant expressions", r'ident "f0x[0-9A-Fa-f]+" in expression'),
    ("garbage collection (gc \"...\")", r'define body\): expected \S+, got \S+ident "gc"'),
    ("allocator parameter attributes (allocptr, allocalign)", r'ident "(allocptr|allocalign)"'),
    ("attribute groups on instructions", r"opcode \S+attrGrp"),
    ("target extension types", r"unknown type 'target'"),
]


def unsupported_family(msg: str) -> str:
    for fam, pat in UNSUPPORTED_FAMILIES:
        if re.search(pat, msg):
            return fam
    return "other: " + unsupported_key(msg)


def unsupported_key(msg: str) -> str:
    """A stable key for a parser rejection message, for grouping `ours-unsupported` runs."""
    m = re.search(r'unsupported instruction opcode \S+ "([^"]+)"', msg)
    if m:
        return "opcode:" + m.group(1)
    m = re.search(r"\(([^)]+)\): expected (\S+), got (\S+)(?: \"?([^\"\s]*))?", msg)
    if m:
        got = m.group(3).rsplit(".", 1)[-1]
        return f"{m.group(1)}:got-{got}{':' + m.group(4) if m.group(4) else ''}"
    m = re.search(r"unexpected token (\S+)(?: \"?([^\"\s]*))?(?: in (\w+))?", msg)
    if m:
        return f"unexpected-{m.group(1).rsplit('.', 1)[-1]}{':' + m.group(2) if m.group(2) else ''}{' in ' + m.group(3) if m.group(3) else ''}"
    return re.sub(r"\d+", "N", msg)[:80]


# Refinement disagreements, by pair id: root cause established by hand.
REFINEMENT_RULES: dict[str, dict[str, str]] = {
    "43005c4d95941233": {
        "id": "B1-refinement", "class": "ours-semantic-bug", "bug": "B1",
        "root_cause": "opt pair (InstCombine fold_select_trunc_nsw_and), correct. Parameter `i8 noundef "
                      "range(i8 0, 2) %y`: our witness put %y out of range, which is UB, but our semantics "
                      "checked noundef before range and made %y poison. No longer refuted after the B1 fix.",
    },
    "5ec489e906cc6d5a": {
        "id": "B1-refinement", "class": "ours-semantic-bug", "bug": "B1",
        "root_cause": "opt pair (InstCombine fold_select_trunc_and), correct; same root cause as "
                      "43005c4d95941233. No longer refuted after the B1 fix.",
    },
    "34374bb544b3d783": {
        "id": "H-alive2-multi-pair", "class": "harness-bug", "bug": "H1",
        "root_cause": "Mutant of an Alive2 test file with four function pairs (src, src3, src9, src4). "
                      "alive-tv checks all of them; the harness took 'correct' from the src9 section while "
                      "src -> tgt (`x - (-1)` vs `-1`) is refuted, so our (right) refutation looked like a "
                      "disagreement. Fixed in the harness (per-pair section, oracle_alive2.select_section); "
                      "the pair's Alive2 verdict is re-run.",
    },
    "34e5e97f58b8f2f3": {
        "id": "alive2-fn-attr-refinement", "class": "out-of-scope", "bug": None,
        "root_cause": "Alive2 test: src has `denormal_fpenv(positivezero)`, tgt has no attributes, both "
                      "return %x. Alive2 refutes with 'Function attributes not refined' (it also requires "
                      "function attributes to be refined); the bodies behave identically in every "
                      "floating-point environment, which is what our function-level refinement states.",
    },
    "ef0c2671893037dc": {
        "id": "B1-refinement", "class": "ours-semantic-bug", "bug": "B1",
        "root_cause": "Alive2 test (correct). Our witness %1 = 0 violates `range(i8 -32, -16)` of a "
                      "`noundef` parameter, which is immediate UB, so src is UB and any tgt refines it. "
                      "Our semantics checks noundef first (0 passes), then range makes %1 poison; src "
                      "returns 1 (select picks 3), tgt returns `or 1, poison` = poison, and the kernel "
                      "accepts the false disproof.",
    },
}
