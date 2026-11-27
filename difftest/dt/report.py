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
import statistics
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

from .common import read_jsonl, write_jsonl

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


def build(work: Path, out: Path, alive_config: str = "no-undef-input") -> list[Path]:
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
    ll = list(read_jsonl(work / "results" / "llubi.jsonl"))
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
    al = list(read_jsonl(work / "results" / f"alive2-{alive_config}.jsonl"))
    pairs = {p["id"]: p for p in read_jsonl(work / "pairs" / "pairs.jsonl")}
    if al:
        from .oracle_alive2 import VERDICTS as AV
        t = Table("alive2_verdicts", f"Alive2 verdicts per pair origin (configuration {alive_config})",
                  ["origin", "pairs", *AV])
        for o in sorted({r["origin"] for r in al}):
            c = Counter(r["verdict"] for r in al if r["origin"] == o)
            t.add(o, sum(c.values()), *[c.get(v, 0) for v in AV])
        tables.append(t)
    ta = list(read_jsonl(work / "results" / "alive2-test-args.jsonl"))
    if ta:
        exp = [(pairs[r["pair"]]["expected"]["verdict"], r["verdict"]) for r in ta
               if r["pair"] in pairs and pairs[r["pair"]].get("expected")]
        if exp:
            t = Table("alive2_sanity", "Oracle sanity check: Alive2 verdicts (each test's TEST-ARGS) against the tests' expectations",
                      ["expected", "correct", "incorrect", "inconclusive", "unsupported", "error"])
            for e in ("correct", "incorrect"):
                c = Counter(v for x, v in exp if x == e)
                t.add(e, *[c.get(v, 0) for v in t.header[1:]])
            tables.append(t)

    # T5: ours vs Alive2 ----------------------------------------------------------------------
    le = list(read_jsonl(work / "results" / "lean.jsonl"))
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
