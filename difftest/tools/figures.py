#!/usr/bin/env python3
"""Paper figures, derived only from `dt report`'s CSV tables and the per-row result records.

Usage: figures.py WORK [OUT]     (default OUT: WORK/report/figures; writes PDF and PNG)
Requires matplotlib (tested with 3.9.2). Every figure has a CSV/LaTeX table of the same data
in WORK/report/, so no number appears only in a figure.

Colors: the validated categorical order (blue, orange, aqua, yellow; adjacent CVD dE >= 9.1)
and a single-hue sequential ramp for the heat map. Aqua and yellow are below 3:1 contrast on
white, so every mark carrying them is directly labeled.
"""
from __future__ import annotations

import csv
import glob
import json
import sys
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.colors import LinearSegmentedColormap  # noqa: E402

SERIES = ["#2a78d6", "#eb6834", "#1baf7a", "#eda100"]
INK, INK2, GRID = "#0b0b0b", "#52514e", "#e4e3df"
BLUES = LinearSegmentedColormap.from_list("blues", ["#f3f7fd", "#9cc0ee", "#2a78d6", "#123d73"])

plt.rcParams.update({
    "font.size": 8, "axes.edgecolor": INK2, "axes.labelcolor": INK, "xtick.color": INK2,
    "ytick.color": INK2, "axes.spines.top": False, "axes.spines.right": False,
    "axes.grid": True, "grid.color": GRID, "grid.linewidth": 0.6, "axes.axisbelow": True,
    "pdf.fonttype": 42, "savefig.bbox": "tight", "savefig.dpi": 200,
})


def table(rep: Path, name: str) -> list[dict[str, str]]:
    p = rep / f"{name}.csv"
    return list(csv.DictReader(p.open())) if p.exists() else []


def save(fig, out: Path, name: str) -> None:
    out.mkdir(parents=True, exist_ok=True)
    for ext in ("pdf", "png"):
        fig.savefig(out / f"{name}.{ext}")
    plt.close(fig)
    print(out / f"{name}.pdf")


def hbar(ax, labels, values, color, fmt="{:,}", log=False):
    y = range(len(labels))
    ax.barh(list(y), values, color=color, height=0.62, edgecolor="white", linewidth=1)
    ax.set_yticks(list(y), labels)
    ax.invert_yaxis()
    ax.grid(axis="y", visible=False)
    if log:
        ax.set_xscale("log")
    for i, v in enumerate(values):
        ax.text(v * (1.08 if log else 1.0) + (0 if log else max(values) * 0.01), i, fmt.format(v),
                va="center", ha="left", color=INK, fontsize=7)


def fig_llubi_classes(rep: Path, out: Path) -> None:
    rows = table(rep, "triage_llubi_classes")
    if not rows:
        return
    rows = [r for r in rows if int(r["total"]) > 0]
    fig, ax = plt.subplots(figsize=(4.2, 0.28 * len(rows) + 0.6))
    hbar(ax, [r["class"] for r in rows], [int(r["total"]) for r in rows], SERIES[0], log=True)
    ax.set_xlabel("llubi runs (log scale)")
    ax.set_title("Every execution run by triage class", loc="left", color=INK, fontsize=9)
    save(fig, out, "llubi_triage_classes")


def fig_bugs(rep: Path, out: Path) -> None:
    rows = table(rep, "triage_bugs")
    if not rows:
        return
    sem = [r for r in rows if r["bug"].startswith("B")]
    fmt = [r for r in rows if r["bug"].startswith("P")]
    fig, axes = plt.subplots(1, 2, figsize=(6.4, 0.24 * max(len(sem), len(fmt)) + 0.9))
    for ax, rs, title, col in ((axes[0], sem, "Semantic bugs (B)", SERIES[0]),
                               (axes[1], fmt, "Output-only differences (P)", SERIES[1])):
        if rs:
            hbar(ax, [r["bug"] for r in rs], [int(r["units"]) for r in rs], col)
        ax.set_title(title, loc="left", color=INK, fontsize=9)
        ax.set_xlabel("distinct corpus units affected")
    save(fig, out, "bugs_units")


def fig_confusion(rep: Path, out: Path) -> None:
    rows = table(rep, "refinement_confusion")
    if not rows:
        return
    cols = [c for c in rows[0] if c != "Alive2 \\ ours"]
    data = [[int(r[c]) for c in cols] for r in rows]
    import math
    fig, ax = plt.subplots(figsize=(4.6, 2.4))
    ax.imshow([[math.log10(v + 1) for v in row] for row in data], cmap=BLUES, aspect="auto")
    ax.set_xticks(range(len(cols)), cols, rotation=20, ha="right")
    ax.set_yticks(range(len(rows)), [r["Alive2 \\ ours"] for r in rows])
    ax.grid(False)
    top = max(math.log10(v + 1) for row in data for v in row) or 1
    for i, row in enumerate(data):
        for j, v in enumerate(row):
            ax.text(j, i, f"{v:,}", ha="center", va="center", fontsize=7,
                    color="white" if math.log10(v + 1) > 0.6 * top else INK)
    ax.set_xlabel("our verdict")
    ax.set_ylabel("Alive2 verdict")
    ax.set_title("Refinement verdicts: Alive2 against ours (pairs; color log-scaled)", loc="left", color=INK, fontsize=9)
    save(fig, out, "refinement_confusion")


def fig_features(rep: Path, out: Path) -> None:
    rows = table(rep, "refinement_by_feature")
    if not rows:
        return
    pct = lambda s: float(s.rstrip("%")) if s not in ("-", "") else 0.0
    labels = [r["feature"] for r in rows]
    a = [pct(r["rate"]) for r in rows]
    b = [pct(list(r.values())[-1]) for r in rows]
    fig, ax = plt.subplots(figsize=(4.4, 0.36 * len(rows) + 0.8))
    y = list(range(len(rows)))
    h = 0.36
    ax.barh([i - h / 2 for i in y], a, height=h, color=SERIES[0], edgecolor="white", linewidth=1,
            label="proved (of Alive2-correct)")
    ax.barh([i + h / 2 for i in y], b, height=h, color=SERIES[1], edgecolor="white", linewidth=1,
            label="disproved (of Alive2-incorrect)")
    for i in y:
        ax.text(a[i] + 1, i - h / 2, f"{a[i]:.0f}%", va="center", fontsize=6.5, color=INK)
        ax.text(b[i] + 1, i + h / 2, f"{b[i]:.0f}%", va="center", fontsize=6.5, color=INK)
    ax.set_yticks(y, labels)
    ax.invert_yaxis()
    ax.set_xlim(0, 105)
    ax.grid(axis="y", visible=False)
    ax.set_xlabel("pairs (%)")
    ax.legend(loc="lower right", frameon=False, fontsize=7)
    ax.set_title("Proof and disproof rates by feature class", loc="left", color=INK, fontsize=9)
    save(fig, out, "refinement_by_feature")


def fig_cost(work: Path, out: Path) -> None:
    series: dict[str, list[float]] = {"llubi": [], "ours (llubi frontend)": [], "alive-tv": [], "ours (Lean obligation)": []}
    for f in glob.glob(str(work / "results" / "llubi*.jsonl")):
        for line in open(f):
            try:
                r = json.loads(line)
            except ValueError:
                continue
            series["llubi"].append(r["llubi"]["wall_s"])
            series["ours (llubi frontend)"].append(r["ours"]["wall_s"])
    for f in glob.glob(str(work / "results" / "alive2-no-undef-input*.jsonl")):
        for line in open(f):
            try:
                series["alive-tv"].append(json.loads(line)["wall_s"])
            except (ValueError, KeyError):
                pass
    for f in glob.glob(str(work / "results" / "lean*.jsonl")):
        for line in open(f):
            try:
                r = json.loads(line)
            except ValueError:
                continue
            if r.get("wall_s") is not None:
                series["ours (Lean obligation)"].append(r["wall_s"])
    fig, ax = plt.subplots(figsize=(4.4, 2.6))
    for (name, xs), col in zip(series.items(), SERIES):
        if not xs:
            continue
        xs = sorted(max(x, 1e-3) for x in xs)
        n = len(xs)
        step = max(1, n // 2000)
        px = xs[::step] + [xs[-1]]
        py = [i / n for i in range(0, n, step)] + [1.0]
        ax.plot(px, py, color=col, linewidth=2, label=f"{name} (n={n:,})")
    ax.set_xscale("log")
    ax.set_xlabel("wall-clock time per check (s, log scale)")
    ax.set_ylabel("fraction of checks")
    ax.legend(loc="lower right", frameon=False, fontsize=6.5)
    ax.set_title("Cost per check", loc="left", color=INK, fontsize=9)
    save(fig, out, "cost_ecdf")


def main() -> int:
    work = Path(sys.argv[1])
    out = Path(sys.argv[2]) if len(sys.argv) > 2 else work / "report" / "figures"
    rep = work / "report"
    fig_llubi_classes(rep, out)
    fig_bugs(rep, out)
    fig_confusion(rep, out)
    fig_features(rep, out)
    fig_cost(work, out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
