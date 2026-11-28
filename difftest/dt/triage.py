"""Triage of disagreements: every non-matching run gets a class, a rule and (for bugs) a bug id.

llubi runs. A `mismatch` compares two full traces, so a difference in how a value or an
instruction is *printed* at line k would hide whatever happens after line k. Triage therefore
first applies the *normalizers* of `triage_rules.NORMALIZERS` to both sides: each removes one
known, documented printing difference (and only that). A run whose outputs are equal after
normalization is `ours-trace-format`, and the record lists the normalizers that were
*necessary* (dropping any one of them makes the outputs differ again). Otherwise the
first remaining difference is matched against the ordered `triage_rules.LLUBI_RULES`; the first
rule that matches gives the class. Runs no rule matches are `untriaged`, so nothing is silently
counted as explained.

Refinement pairs. Disagreements between Alive2 and us (and inconsistent pairs) are matched
against `triage_rules.REFINEMENT_RULES` by pair id, each with a written root cause.

Classes (`CLASSES`):

* ``ours-semantic-bug``: our semantics differ from LangRef (and the oracle is right).
* ``ours-trace-format``: same execution, our llubi-compatible output prints something
  differently (only normalizers were needed).
* ``ours-unsupported``: a feature we do not implement (our parser or interpreter rejects it).
* ``oracle-unsupported``: the oracle does not implement a feature we execute; no comparison is
  possible beyond the point where it stopped.
* ``oracle-bug``: the oracle differs from LangRef.
* ``spec-gap``: LangRef leaves the behaviour open (e.g. a nondeterministic choice), so both
  sides are allowed.
* ``out-of-scope``: the oracle checks something our statement does not express (e.g. Alive2 also
  requires function attributes to be refined).
* ``harness-bug``: a bug in the campaign harness (ids `H*` in `difftest/BUGS.md`), fixed.
* ``timeout``, ``invalid``, ``crash``: from the harness verdicts.
* ``untriaged``: no rule; needs a root cause.
"""

from __future__ import annotations

import re
from typing import Any, Callable

from . import triage_rules as R

CLASSES = ["ours-semantic-bug", "ours-trace-format", "ours-unsupported", "oracle-unsupported",
           "oracle-bug", "spec-gap", "out-of-scope", "harness-bug", "timeout", "invalid", "crash",
           "untriaged"]


def _norm_all(text: str, side: str, norms: list[R.Normalizer]) -> str:
    for n in norms:
        text = n.apply(text, side)
    return text


def _first_diff(a: str, b: str) -> tuple[int, str, str]:
    la, lb = a.splitlines(), b.splitlines()
    for i in range(max(len(la), len(lb))):
        x = la[i] if i < len(la) else "<EOF>"
        y = lb[i] if i < len(lb) else "<EOF>"
        if x != y:
            return i + 1, x, y
    return 0, "", ""


def _context(text: str, line: int, before: int = 3) -> str:
    ls = text.splitlines()
    return "\n".join(ls[max(0, line - 1 - before): line + 2])


def triage_llubi(row: dict[str, Any], module: str | None = None) -> dict[str, Any]:
    v = row["verdict"]
    out: dict[str, Any] = {"run_id": row["run_id"], "case": row["case"], "subject": row["subject"],
                           "unit": row.get("unit"), "mutant": row.get("mutant"), "source": row.get("source"),
                           "verdict": v, "categories": row.get("categories")}
    if v == "match":
        return {**out, "class": "match"}
    simple = {"timeout": "timeout", "invalid": "invalid", "llubi-crash": "crash", "ours-crash": "crash"}
    L, O = row["llubi"], row["ours"]
    ls, os_ = L.get("stderr", ""), O.get("stderr", "")
    if v in simple:
        cls = simple[v]
        rule = None
        if v == "ours-crash" or v == "llubi-crash":
            rule = R.match_rule(R.LLUBI_RULES, verdict=v, llubi=ls, ours=os_, ldiff="", odiff="",
                                lexit=L["exit"], oexit=O["exit"])
        if rule:
            return {**out, "class": rule.cls, "rule": rule.id, "bug": rule.bug}
        return {**out, "class": cls, "rule": f"verdict:{v}", "detail": row.get("detail")}
    if v == "ours-unsupported":
        msg = row.get("detail", {}).get("message", "")
        return {**out, "class": "ours-unsupported", "rule": "parser:" + R.unsupported_key(msg), "message": msg}
    # mismatch
    if "stderr" not in L or "stderr" not in O:
        return {**out, "class": "untriaged", "rule": "no-outputs"}
    # Outputs are stored truncated to their last 50,000 characters: two tails cut at different
    # offsets cannot be compared line by line. Such runs are re-run with full outputs
    # (`dt retriage-truncated`) before triage.
    if len(ls) >= 50000 or len(os_) >= 50000:
        return {**out, "class": "untriaged", "rule": "truncated-output"}
    norms = R.NORMALIZERS
    nl, no = _norm_all(ls, "llubi", norms), _norm_all(os_, "ours", norms)
    same_exit = L["exit"] == O["exit"]
    same_out = L.get("stdout", "") == O.get("stdout", "")
    if same_exit and same_out and nl == no:
        needed = []
        for n in norms:
            rest = [m for m in norms if m is not n]
            if _norm_all(ls, "llubi", rest) != _norm_all(os_, "ours", rest):
                needed.append(n.id)
        bugs = sorted({n.bug for n in norms if n.id in needed})
        return {**out, "class": "ours-trace-format", "rule": "normalized:" + "+".join(needed), "bug": bugs}
    line, dl, do = _first_diff(nl, no)
    rule = R.match_rule(R.LLUBI_RULES, verdict=v, llubi=nl, ours=no, ldiff=dl, odiff=do,
                        lexit=L["exit"], oexit=O["exit"], module=module)
    base = {**out, "first_diff_line": line, "llubi_line": dl[:300], "ours_line": do[:300]}
    if rule is None:
        return {**base, "class": "untriaged", "rule": None,
                "llubi_context": _context(nl, line)[:1500], "ours_context": _context(no, line)[:1500]}
    return {**base, "class": rule.cls, "rule": rule.id, "bug": rule.bug}


def triage_refinement(pair: dict[str, Any], alive: str, ours: str) -> dict[str, Any] | None:
    """Rows for disagreements and inconsistencies only."""
    disagree = (alive == "correct" and ours == "disproved") or (alive == "incorrect" and ours == "proved")
    if not disagree and ours != "inconsistent":
        return None
    r = R.REFINEMENT_RULES.get(pair["id"])
    row = {"pair": pair["id"], "origin": pair["origin"], "alive2": alive, "ours": ours}
    if r is None:
        return {**row, "class": "untriaged", "rule": None}
    return {**row, "class": r["class"], "rule": r["id"], "bug": r.get("bug"), "root_cause": r["root_cause"]}
