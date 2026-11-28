#!/usr/bin/env python3
"""Assemble the final result set of the phase-2 campaign into a view directory.

Usage: assemble_final.py WORK VIEW

The final numbers come from the code after all fixes. The runs that produced them:

* llubi: `results/llubi-run3*.jsonl` (run 3, final code, all 3,048,296 runs).
* Alive2: `results/alive2-*.jsonl` (oracle only; the 50 multi-pair rows re-run with the fixed
  parser are in `alive2-no-undef-input.shard-0-of-1.jsonl`, their old rows removed).
* Lean `prove` / `disprove-search`: run 2 (`lean.shard-*-of-32`, code 67a4ec4) for every pair
  except those whose semantics changed after 67a4ec4 (pairs mentioning `x86_fp80`,
  `ppc_fp128`, `denormal_fpenv` or `llvm.assume`, listed in `logs/lean-final-rerun-pairs.txt`),
  which come from `lean-final*.jsonl` (final code).
* Lean `disprove-witness`: `lean.shard-*-of-16` (final code).

The view links the inputs and writes one result file per stage, so `dt triage` and `dt report`
run on it unchanged. Every choice (which file a row comes from) is recorded in
`VIEW/results/SOURCES.json`.
"""
import glob
import json
import os
import sys
from pathlib import Path


def rows(paths):
    for p in paths:
        with open(p) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    yield json.loads(line)
                except ValueError:
                    pass  # a row cut short by a kill; it was re-run


def main() -> int:
    work, view = Path(sys.argv[1]), Path(sys.argv[2])
    (view / "results").mkdir(parents=True, exist_ok=True)
    for d in ("corpus", "mutants", "pairs", "cases", "lean"):
        link = view / d
        if not link.exists():
            os.symlink(work / d, link)
    res = work / "results"
    sources = {}

    # llubi: run 3
    llubi_files = sorted(glob.glob(str(res / "llubi-run3*.jsonl")))
    n = 0
    seen = set()
    with open(view / "results" / "llubi.jsonl", "w") as out:
        for r in rows(llubi_files):
            if r["run_id"] in seen:
                continue
            seen.add(r["run_id"])
            out.write(json.dumps(r, sort_keys=True) + "\n")
            n += 1
    sources["llubi"] = {"files": llubi_files, "rows": n}

    # Alive2
    for cfg in ("no-undef-input", "test-args"):
        files = sorted(glob.glob(str(res / f"alive2-{cfg}*.jsonl")))
        seen, n = set(), 0
        with open(view / "results" / f"alive2-{cfg}.jsonl", "w") as out:
            for r in rows(files):
                if r["pair"] in seen:
                    continue
                seen.add(r["pair"])
                out.write(json.dumps(r, sort_keys=True) + "\n")
                n += 1
        sources[f"alive2-{cfg}"] = {"files": files, "rows": n}

    # Lean
    affected = {l.strip() for l in open(work / "logs" / "lean-final-rerun-pairs.txt") if l.strip()}
    run2 = sorted(glob.glob(str(res / "lean.shard-*-of-32.jsonl")))
    final = sorted(glob.glob(str(res / "lean-final*.jsonl")))
    witness = sorted(glob.glob(str(res / "lean.shard-*-of-16.jsonl")))
    seen, counts = set(), {"run2": 0, "final": 0, "witness": 0}
    with open(view / "results" / "lean.jsonl", "w") as out:
        for tag, files, keep in (("final", final, lambda r: True),
                                 ("witness", witness, lambda r: r["obligation"] == "disprove-witness"),
                                 ("run2", run2, lambda r: r["pair"] not in affected)):
            for r in rows(files):
                if r["run_id"] in seen or not keep(r):
                    continue
                seen.add(r["run_id"])
                r["code_version"] = tag
                out.write(json.dumps(r, sort_keys=True) + "\n")
                counts[tag] += 1
    sources["lean"] = {"run2_files": run2, "final_files": final, "witness_files": witness,
                       "affected_pairs": len(affected), "rows": counts}
    (view / "results" / "SOURCES.json").write_text(json.dumps(sources, indent=2))
    print(json.dumps({k: (v["rows"] if "rows" in v else v) for k, v in sources.items()}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
