"""Aggregate tables for the paper, computed only from the per-row JSONL records.

Every table is written three ways from the same rows: CSV (for plotting), a LaTeX ``tabular``
using ``booktabs`` (for the paper), and Markdown (``summary.md``, for reading). No number in a
table is computed from anything but the JSONL files under the work directory, so the tables
can be regenerated, audited, and recomputed by reviewers from the released records.

Our per-pair verdict (``our_verdict``) combines the three obligations of a pair:

* ``proved``: the ``prove`` obligation checked and no disproof did;
* ``disproved``: a ``disprove-*`` obligation checked and the proof did not;
* ``inconsistent``: both checked (impossible unless our semantics or kernel setup is unsound;
  reported as an alarm);
* ``translation-error``: our parser rejected one side;
* ``unknown``: none checked (tactic failures or timeouts).

The comparison classes (``COMPARISON``) against Alive2 are the paper's headline numbers.
"""

from __future__ import annotations

import csv
import re
import statistics
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

from .common import read_jsonl, read_results, write_jsonl

COMPARISON = {
    ("correct", "proved"): "agree",
    ("incorrect", "disproved"): "agree",
    ("correct", "disproved"): "DISAGREE: we refute an Alive2-verified pair",
    ("incorrect", "proved"): "DISAGREE: we prove an Alive2-refuted pair",
    ("correct", "unknown"): "gap: proof not found",
    ("incorrect", "unknown"): "gap: disproof not found",
}


def our_verdict(obls: list[dict[str, Any]]) -> str:
    st = {o["obligation"]: o.get("status") for o in obls}
    if any(s == "translation-error" for s in st.values()):
        return "translation-error"
    proved = st.get("prove") == "checked"
    disproved = any(st.get(k) == "checked" for k in ("disprove-witness", "disprove-search"))
    if proved and disproved:
        return "inconsistent"
    if proved:
        return "proved"
    if disproved:
        return "disproved"
    return "unknown"


class Table:
    def __init__(self, name: str, caption: str, header: list[str]):
        self.name, self.caption, self.header, self.rows = name, caption, header, []

    def add(self, *row: Any) -> None:
        self.rows.append(list(row))

    def write(self, d: Path) -> list[Path]:
        d.mkdir(parents=True, exist_ok=True)
        csv_p = d / f"{self.name}.csv"
        with csv_p.open("w", newline="") as f:
            wr = csv.writer(f)
            wr.writerow(self.header)
            wr.writerows(self.rows)
        tex_p = d / f"{self.name}.tex"
        esc = lambda x: str(x).replace("_", r"\_").replace("%", r"\%").replace("&", r"\&").replace("#", r"\#")
        lines = [r"\begin{table}[t]", r"\centering", rf"\caption{{{esc(self.caption)}}}",
                 rf"\label{{tab:{self.name}}}", r"\begin{tabular}{l" + "r" * (len(self.header) - 1) + "}",
                 r"\toprule", " & ".join(esc(h) for h in self.header) + r" \\", r"\midrule"]
        lines += [" & ".join(esc(c) for c in r) + r" \\" for r in self.rows]
        lines += [r"\bottomrule", r"\end{tabular}", r"\end{table}"]
        tex_p.write_text("\n".join(lines) + "\n")
        return [csv_p, tex_p]

    def markdown(self) -> str:
        out = [f"### {self.caption}", "", "| " + " | ".join(self.header) + " |",
               "|" + "|".join("---" for _ in self.header) + "|"]
        out += ["| " + " | ".join(str(c) for c in r) + " |" for r in self.rows]
        return "\n".join(out) + "\n"


def _pct(a: int, b: int) -> str:
    return f"{100.0 * a / b:.1f}%" if b else "-"


def alive2_expectation(unit: dict[str, Any], recorded: str, alive2_src: Path | None) -> str:
    """The verdict an Alive2 test asserts, from the test file at the pinned Alive2 checkout:
    ``xfail`` (a known Alive2 failure), ``incorrect`` (an ``; ERROR:`` line or a CHECK for
    "Transformation doesn't verify!"), ``correct`` (a CHECK for "seems to be correct", or no
    CHECK lines at all, which is lit's convention for these tests), or ``unasserted`` (CHECK
    lines that test something other than the verdict). Phase 1 recorded only the ``; ERROR:``
    rule (``recorded``), which misreads CHECK-based and unasserted tests."""
    f = (unit.get("origin") or {}).get("file")
    if unit.get("xfail"):
        return "xfail"
    if not f or alive2_src is None or not (alive2_src / f).exists():
        return recorded
    text = (alive2_src / f).read_text(errors="replace")
    if re.search(r"^; ERROR:", text, re.M) or re.search(r"^; CHECK: Transformation doesn't verify", text, re.M):
        return "incorrect"
    if re.search(r"^; CHECK: Transformation seems to be correct", text, re.M):
        return "correct"
    if re.search(r"^; CHECK(-NOT)?:", text, re.M):
        return "unasserted"
    return "correct"


def build(work: Path, out: Path, alive_config: str = "no-undef-input", alive2_src: Path | None = None) -> list[Path]:
    if alive2_src is None:
        from .common import ORACLES
        alive2_src = ORACLES / "src" / "alive2"
    tables: list[Table] = []

    # T1: corpus funnel ------------------------------------------------------------------
    acc = list(read_jsonl(work / "corpus" / "units.jsonl"))
    rej = list(read_jsonl(work / "corpus" / "rejected.jsonl"))
    dup = list(read_jsonl(work / "corpus" / "duplicates.jsonl"))
    if acc or rej:
        reasons = sorted({r["reason"] for r in rej})
        t = Table("corpus_funnel", "Corpus construction: candidates per source and why they were excluded",
                  ["source", "candidates", *[f"rejected: {r}" for r in reasons], "duplicates", "accepted"])
        for src in sorted({r["source"] for r in acc + rej + dup}):
            a = sum(1 for r in acc if r["source"] == src)
            d = sum(1 for r in dup if r["source"] == src)
            rr = [sum(1 for r in rej if r["source"] == src and r["reason"] == x) for x in reasons]
            t.add(src, a + d + sum(rr), *rr, d, a)
        tables.append(t)
        t = Table("corpus_features", "Accepted units by feature class (classes overlap)",
                  ["source", "units", "integer", "float", "vector", "memory", "control-flow", "intrinsic", "undef", "poison"])
        for src in sorted({r["source"] for r in acc}):
            rows = [r for r in acc if r["source"] == src]
            cnt = Counter(c for r in rows for c in r["features"]["categories"])
            t.add(src, len(rows), *[cnt.get(c, 0) for c in t.header[2:]])
        tables.append(t)

    # T2: mutation operators ----------------------------------------------------------------
    muts = list(read_jsonl(work / "mutants" / "mutants.jsonl"))
    if muts:
        t = Table("mutation_operators", "Mutants per operator (first-order) and their validity",
                  ["operator", "drawn", "invalid", "no-op", "duplicate", "valid", "valid rate"])
        by: dict[str, Counter] = defaultdict(Counter)
        for m in muts:
            if m["order"] == 1 and m["sites"]:
                by[m["sites"][0]["operator"]][m["status"]] += 1
        for op in sorted(by):
            c = by[op]
            n = sum(c.values())
            t.add(op, n, c["invalid"], c["noop"], c["duplicate"], c["ok"], _pct(c["ok"], n))
        tables.append(t)

    # T3: llubi differential ----------------------------------------------------------------
    ll = list(read_results(work / "results" / "llubi.jsonl", "run_id"))
    if ll:
        from .oracle_llubi import VERDICTS
        t = Table("llubi_verdicts", "Differential execution against llubi: verdict per case source",
                  ["source", "runs", *VERDICTS, "agreement"])
        for src in sorted({r.get("source") or "?" for r in ll}):
            rows = [r for r in ll if (r.get("source") or "?") == src]
            c = Counter(r["verdict"] for r in rows)
            comparable = c["match"] + c["mismatch"]
            t.add(src, len(rows), *[c.get(v, 0) for v in VERDICTS], _pct(c["match"], comparable))
        tables.append(t)
        t = Table("llubi_mismatch_channels", "llubi mismatches by first differing channel",
                  ["channel", "runs"])
        for ch, n in sorted(Counter(r["detail"].get("channel") for r in ll if r["verdict"] == "mismatch").items(), key=lambda x: str(x[0])):
            t.add(ch, n)
        tables.append(t)
        write_jsonl(out / "llubi-mismatches.jsonl", [r for r in ll if r["verdict"] in ("mismatch", "ours-crash")])

    # T4: Alive2 verdicts ---------------------------------------------------------------------
    al = list(read_results(work / "results" / f"alive2-{alive_config}.jsonl", "pair"))
    pairs = {p["id"]: p for p in read_jsonl(work / "pairs" / "pairs.jsonl")}
    if al:
        from .oracle_alive2 import VERDICTS as AV
        t = Table("alive2_verdicts", f"Alive2 verdicts per pair origin (configuration {alive_config})",
                  ["origin", "pairs", *AV])
        for o in sorted({r["origin"] for r in al}):
            c = Counter(r["verdict"] for r in al if r["origin"] == o)
            t.add(o, sum(c.values()), *[c.get(v, 0) for v in AV])
        tables.append(t)
    ta = list(read_results(work / "results" / "alive2-test-args.jsonl", "pair"))
    if ta:
        units_by_id = {u["id"]: u for u in read_jsonl(work / "corpus" / "units.jsonl") if u["kind"] == "pair"}
        exp = []
        for r in ta:
            p = pairs.get(r["pair"])
            if not p or not p.get("expected"):
                continue
            u = units_by_id.get((p.get("parent") or {}).get("unit"), {})
            exp.append((alive2_expectation(u, p["expected"]["verdict"], alive2_src), r["verdict"]))
        if exp:
            t = Table("alive2_sanity", "Oracle sanity check: Alive2 verdicts (each test's TEST-ARGS) against the tests' own expectations",
                      ["expected", "tests", "correct", "incorrect", "inconclusive", "unsupported", "error"])
            for e in ("correct", "incorrect", "unasserted", "xfail"):
                c = Counter(v for x, v in exp if x == e)
                if c:
                    t.add(e, sum(c.values()), *[c.get(v, 0) for v in t.header[2:]])
            tables.append(t)

    # T5: ours vs Alive2 ----------------------------------------------------------------------
    le = list(read_results(work / "results" / "lean.jsonl", "run_id"))
    if le:
        from .lean_emit import OBLIGATIONS
        sts = ["checked", "failed", "timeout", "translation-error", "nonstandard-axioms", "error", "not-applicable"]
        t = Table("lean_obligations", "Our obligations by pair origin and outcome",
                  ["origin", "obligation", *sts])
        for o in sorted({r["origin"] for r in le}):
            for k in OBLIGATIONS:
                c = Counter(r["status"] for r in le if r["origin"] == o and r["obligation"] == k)
                if c:
                    t.add(o, k, *[c.get(x, 0) for x in sts])
        tables.append(t)
    if le and al:
        obls: dict[str, list] = defaultdict(list)
        for r in le:
            obls[r["pair"]].append(r)
        alive = {r["pair"]: r for r in al}
        ours_cols = ["proved", "disproved", "unknown", "translation-error", "inconsistent"]
        t = Table("refinement_confusion", "Our verdicts (columns) against Alive2's (rows), all origins",
                  ["Alive2 \\ ours", *ours_cols])
        cells: Counter = Counter()
        triage = []
        for pid, os_ in obls.items():
            a = alive.get(pid)
            if not a:
                continue
            ov = our_verdict(os_)
            cells[(a["verdict"], ov)] += 1
            cls = COMPARISON.get((a["verdict"], ov))
            if ov == "inconsistent" or (cls and cls.startswith("DISAGREE")):
                triage.append({"pair": pid, "origin": a["origin"], "alive2": a["verdict"], "ours": ov,
                               "class": cls or "inconsistent", "alive2_error": a.get("error"),
                               "obligations": os_})
        for av in ("correct", "incorrect", "inconclusive", "unsupported", "error"):
            t.add(av, *[cells.get((av, ov), 0) for ov in ours_cols])
        tables.append(t)
        cls_counts = Counter(COMPARISON.get(k, "other") for k, n in cells.items() for _ in range(n))
        t = Table("refinement_summary", "Agreement classes between our verdicts and Alive2's", ["class", "pairs"])
        for k, n in sorted(cls_counts.items()):
            t.add(k, n)
        tables.append(t)
        write_jsonl(out / "refinement-triage.jsonl", triage)

    # T7: triage (dt triage) ----------------------------------------------------------------------
    tl = list(read_jsonl(out / "triage-llubi.jsonl"))
    if tl and ll:
        from .triage import CLASSES
        from . import triage_rules as TR
        n_match = Counter(r.get("source") or "?" for r in ll if r["verdict"] == "match")
        srcs = sorted({r.get("source") or "?" for r in ll})
        t = Table("triage_llubi_classes", "Every llubi run by triage class and case source (runs)",
                  ["class", *srcs, "total"])
        c2 = Counter(((r.get("source") or "?"), r["class"]) for r in tl)
        t.add("match", *[n_match[s_] for s_ in srcs], sum(n_match.values()))
        for cl in CLASSES:
            row = [c2[(s_, cl)] for s_ in srcs]
            if sum(row):
                t.add(cl, *row, sum(row))
        tables.append(t)
        # agreement: raw (byte-exact), modulo output format, and semantic
        tot = Counter(r["class"] for r in tl)
        comparable = len([r for r in ll if r["verdict"] in ("match", "mismatch")])
        m = n_match.total() if hasattr(n_match, "total") else sum(n_match.values())
        sem = tot["ours-semantic-bug"] + tot["oracle-bug"] + tot["spec-gap"] + tot["untriaged"]
        t = Table("llubi_agreement", "Agreement with llubi over comparable runs (both executed the module)",
                  ["measure", "runs", "of comparable", "rate"])
        fmt = tot["ours-trace-format"]
        t.add("byte-exact match", m, comparable, _pct(m, comparable))
        t.add("match modulo output format (P*)", m + fmt, comparable, _pct(m + fmt, comparable))
        t.add("semantic divergence (B*, oracle bugs, spec gaps, untriaged)", sem, comparable, _pct(sem, comparable))
        tables.append(t)
        # per bug: runs, distinct cases, distinct units (a unit and its mutants count once)
        rule_doc = {r.id: r.root_cause for r in TR.LLUBI_RULES}
        rule_doc.update({f"normalized:{n.id}": n.doc for n in TR.NORMALIZERS})
        bug_doc = {n.bug: n.doc for n in TR.NORMALIZERS}
        bug_doc.update({r.bug: r.root_cause for r in TR.LLUBI_RULES if r.bug})
        per: dict[str, list] = defaultdict(list)
        for r in tl:
            bugs = r.get("bug") or []
            for b in ([bugs] if isinstance(bugs, str) else bugs):
                per[b].append(r)
        tr_ = [json_row for json_row in read_jsonl(out / "triage-refinement.jsonl")]
        t = Table("triage_bugs", "Confirmed bugs (difftest/BUGS.md): llubi runs, distinct cases and distinct units affected, refinement pairs",
                  ["bug", "class", "llubi runs", "cases", "units", "refinement pairs"])
        for b in sorted(set(per) | {r.get("bug") for r in tr_ if r.get("bug")}, key=lambda x: (x[0], int(x[1:]) if x[1:].isdigit() else 0)):
            rs = per.get(b, [])
            cls = Counter(r["class"] for r in rs).most_common(1)[0][0] if rs else "ours-semantic-bug"
            t.add(b, cls, len(rs), len({r["case"] for r in rs}), len({r.get("unit") for r in rs}),
                  sum(1 for r in tr_ if r.get("bug") == b))
        tables.append(t)
        t = Table("triage_rules", "Runs per triage rule (llubi)", ["rule", "class", "runs", "cases"])
        byrule: dict[tuple, set] = defaultdict(set)
        nrule: Counter = Counter()
        for r in tl:
            k = (r.get("rule") if not str(r.get("rule")).startswith("parser:") else "parser (see ours_unsupported)", r["class"])
            nrule[k] += 1
            byrule[k].add(r["case"])
        for k, n in nrule.most_common():
            t.add(k[0], k[1], n, len(byrule[k]))
        tables.append(t)
        t = Table("ours_unsupported", "Features our parser rejects (llubi accepts), by feature family (top 30 by distinct cases)",
                  ["feature", "runs", "cases"])
        uk: dict[str, set] = defaultdict(set)
        un: Counter = Counter()
        for r in tl:
            if r["class"] == "ours-unsupported" and str(r.get("rule")).startswith("parser:"):
                k = TR.unsupported_family(r.get("message", ""))
                un[k] += 1
                uk[k].add(r["case"])
        for k, _ in sorted(uk.items(), key=lambda x: -len(x[1]))[:30]:
            t.add(k, un[k], len(uk[k]))
        tables.append(t)
        import re as _re
        t = Table("oracle_unsupported", "Instructions llubi does not execute (we do), top 30 by distinct cases",
                  ["instruction", "runs", "cases"])
        ok: dict[str, set] = defaultdict(set)
        on: Counter = Counter()
        for r in tl:
            if r["class"] == "oracle-unsupported":
                line = r.get("llubi_line", "")
                mm = _re.search(r"call [^@]*@([-\w.$]+)", line) or _re.search(r"=\s*(\w+)|^\s*Unrecognized instruction:\s+(\w+)", line)
                k = (mm.group(1) or (mm.group(2) if mm.lastindex and mm.lastindex > 1 else "?")) if mm else "?"
                k = _re.sub(r"\.(p\d+|[vi]\d+|f\d+|nxv\d+\w*|v\d+\w+)+$", "", k) if k.startswith("llvm.") else k
                on[k] += 1
                ok[k].add(r["case"])
        for k, _ in sorted(ok.items(), key=lambda x: -len(x[1]))[:30]:
            t.add(k, on[k], len(ok[k]))
        tables.append(t)
    trf = list(read_jsonl(out / "triage-refinement.jsonl"))
    if trf:
        t = Table("triage_refinement", "Refinement disagreements with Alive2 by triage class",
                  ["class", "rule", "bug", "pairs"])
        for (cl, ru, bu), n in sorted(Counter((r["class"], r.get("rule"), r.get("bug")) for r in trf).items(), key=lambda x: -x[1]):
            t.add(cl, ru, bu or "", n)
        tables.append(t)

    # T8: proof coverage by feature ------------------------------------------------------------
    if le and al:
        units = {u["id"]: u for u in read_jsonl(work / "corpus" / "units.jsonl")}
        muts = {m["id"]: m for m in read_jsonl(work / "mutants" / "mutants.jsonl")}
        def feats(p: dict) -> list[str]:
            par = p.get("parent") or {}
            src = muts.get(par.get("mutant")) or units.get(par.get("unit")) or {}
            return (src.get("features") or {}).get("categories") or []
        scope = {r["pair"]: bool(r.get("static_scope")) for r in le if r["obligation"] == "prove"}
        t = Table("refinement_by_feature", "Proof and disproof rates by feature class (pairs within the function-level statement, i.e. no calls to non-intrinsics or globals)",
                  ["feature", "Alive2 correct", "proved", "rate", "Alive2 incorrect", "disproved", "rate"])
        acc: dict[str, Counter] = defaultdict(Counter)
        for pid, os_ in obls.items():
            a = alive.get(pid)
            if not a or scope.get(pid) or pid not in pairs:
                continue
            ov = our_verdict(os_)
            for f in feats(pairs[pid]) + ["all"]:
                acc[f][(a["verdict"], ov)] += 1
        for f in sorted(acc, key=lambda x: (x != "all", x)):
            c = acc[f]
            nc = sum(v for (av, _), v in c.items() if av == "correct")
            ni = sum(v for (av, _), v in c.items() if av == "incorrect")
            t.add(f, nc, c[("correct", "proved")], _pct(c[("correct", "proved")], nc),
                  ni, c[("incorrect", "disproved")], _pct(c[("incorrect", "disproved")], ni))
        tables.append(t)

    # T6: cost ----------------------------------------------------------------------------------
    cost = Table("cost", "Wall-clock time per check (seconds)", ["tool", "checks", "median", "p90", "max"])
    for name, xs in (("llubi", [r["llubi"]["wall_s"] for r in ll]), ("ours (llubi frontend)", [r["ours"]["wall_s"] for r in ll]),
                     ("alive-tv", [r["wall_s"] for r in al]), ("ours (Lean obligations)", [r["wall_s"] for r in le if "wall_s" in r])):
        if xs:
            xs = sorted(xs)
            cost.add(name, len(xs), f"{statistics.median(xs):.3f}", f"{xs[int(0.9 * (len(xs) - 1))]:.3f}", f"{xs[-1]:.3f}")
    if cost.rows:
        tables.append(cost)

    paths: list[Path] = []
    for t in tables:
        paths += t.write(out)
    md = out / "summary.md"
    md.write_text("# Differential testing summary\n\n" + "\n".join(t.markdown() for t in tables))
    paths.append(md)
    return paths
