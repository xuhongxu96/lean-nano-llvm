#!/usr/bin/env python3
"""Progress of a running campaign: rows done per stage (all shard files), rate over the last
interval, and an ETA. Usage: progress.py WORK [--state FILE]

Totals: llubi = cases x 2 seeds; alive2-<config> = pairs (test-args: Alive2 tests only);
lean = pairs x obligations requested (pass --lean-obligations, default 2: prove, disprove-search).
Reads only line counts, so it is cheap enough to run while shards are writing."""
import argparse
import json
import time
from pathlib import Path


def lines(p: Path) -> int:
    with p.open("rb") as f:
        return sum(buf.count(b"\n") for buf in iter(lambda: f.read(1 << 20), b""))


ap = argparse.ArgumentParser()
ap.add_argument("work")
ap.add_argument("--state", default=None)
ap.add_argument("--lean-obligations", type=int, default=2)
a = ap.parse_args()
w = Path(a.work)
n_cases = lines(w / "cases" / "cases.jsonl")
n_pairs = lines(w / "pairs" / "pairs.jsonl")
totals = {"llubi": 2 * n_cases, "alive2-no-undef-input": n_pairs, "alive2-default": n_pairs,
          "alive2-test-args": 714, "lean": a.lean_obligations * n_pairs}
state_p = Path(a.state or (w / "logs" / ".progress.json"))
prev = json.loads(state_p.read_text()) if state_p.exists() else {}
now = time.time()
cur = {"t": now}
for stage, total in totals.items():
    files = list((w / "results").glob(f"{stage}.jsonl")) + list((w / "results").glob(f"{stage}.shard-*.jsonl"))
    if not files:
        continue
    done = sum(lines(f) for f in files)
    cur[stage] = done
    rate = eta = ""
    if stage in prev and now > prev["t"]:
        r = (done - prev[stage]) / (now - prev["t"])
        rate = f"{r:8.1f}/s"
        eta = f"ETA {(total - done) / r / 3600:6.2f} h" if r > 0 else ""
    print(f"{stage:24s} {done:>10,} / {total:>10,} ({100 * done / max(total, 1):5.1f}%) {rate} {eta}")
state_p.parent.mkdir(parents=True, exist_ok=True)
state_p.write_text(json.dumps(cur))
