"""Command-line interface: one subcommand per pipeline stage.

    dt collect      corpus from pinned upstream tests          -> work/corpus/
    dt mutate       seeded mutants of corpus units             -> work/mutants/
    dt pairs        refinement pairs (Alive2 tests, opt, mutation) -> work/pairs/
    dt cases        execution cases (programs, drivers)        -> work/cases/
    dt run-llubi    llubi vs. ours on execution cases          -> work/results/llubi.jsonl
    dt run-alive2   Alive2 verdicts on pairs                   -> work/results/alive2-<config>.jsonl
    dt run-lean     our proofs/disproofs on pairs              -> work/results/lean.jsonl
    dt report       tables (CSV, LaTeX, Markdown) from results -> work/report/
    dt provenance   versions and pins of this run              -> work/provenance.json

Run stages are resumable (rows already present in the output are skipped) and shardable
(``--shard i/n`` keeps the rows whose id hashes to i modulo n), so a large campaign can be
split across machines and re-assembled by concatenating the JSONL files.
"""

from __future__ import annotations

import argparse
import concurrent.futures as cf
import json
import sys
from pathlib import Path
from typing import Any, Callable, Iterable

from . import corpus as corpus_mod
from . import drivers, ir, lean_emit, mutate, oracle_alive2, oracle_llubi, pairs, report, triage
from .common import WORK, provenance, read_jsonl, read_results, sha256, shard_path, write_jsonl

DEFAULT_SEED = 20261127


def _shard_ok(rid: str, shard: str | None) -> bool:
    if not shard:
        return True
    i, n = (int(x) for x in shard.split("/"))
    return int(sha256(rid)[:8], 16) % n == i


def _parallel(fn: Callable[[Any], Any], items: Iterable[Any], jobs: int) -> Iterable[Any]:
    """Unordered parallel map with a bounded number of tasks in flight, so memory stays
    proportional to `jobs`, not to the number of items."""
    window = max(4 * jobs, 16)
    with cf.ThreadPoolExecutor(max_workers=jobs) as ex:
        pending: set[cf.Future] = set()
        for it in items:
            pending.add(ex.submit(fn, it))
            if len(pending) >= window:
                done, pending = cf.wait(pending, return_when=cf.FIRST_COMPLETED)
                for f in done:
                    yield f.result()
        for f in cf.as_completed(pending):
            yield f.result()


def _sort_jsonl(path: Path, key: str) -> None:
    """Sort a JSONL file by one field, so outputs are byte-identical across runs."""
    rows = sorted(path.read_text().splitlines(), key=lambda l: json.loads(l)[key])
    path.write_text("".join(r + "\n" for r in rows))


def _resume(out: Path, key: str = "id") -> set[str]:
    """Rows already done, in the unsharded file or any shard file (so a stage can be resumed
    with a different sharding)."""
    return {r[key] for r in read_results(out)}


def _work(args) -> Path:
    return Path(args.work) if args.work else WORK


# --------------------------------------------------------------------------------------------


def cmd_collect(args) -> int:
    w = _work(args)
    stats = corpus_mod.collect(
        llvm_src=Path(args.llvm_src) if args.llvm_src else None,
        alive2_src=Path(args.alive2_src) if args.alive2_src else None,
        repo_root=Path(__file__).resolve().parents[2],
        transform_dirs=args.transform_dirs.split(",") if args.transform_dirs else corpus_mod.DEFAULT_TRANSFORM_DIRS,
        max_instr=args.max_instructions,
        jobs=args.jobs,
        limit=args.limit,
        out=w / "corpus",
        allow_unpinned=args.allow_unpinned,
    )
    print(json.dumps(stats))
    return 0


def cmd_mutate(args) -> int:
    w = _work(args)
    units = corpus_mod.load_units(w / "corpus", kinds=["function", "pair"])
    out_dir = w / "mutants"
    ops = args.operators.split(",") if args.operators else None

    def one(u: dict[str, Any]) -> list[dict[str, Any]]:
        fn = "tgt" if u["kind"] == "pair" else u["function"]
        rows = []
        for order in range(1, args.max_order + 1):
            try:
                ms = mutate.mutate_unit(u["id"], u["text"], fn, global_seed=args.seed,
                                        count=args.per_unit, order=order, operators=ops)
            except Exception as e:  # recorded, never silently dropped
                rows.append({"id": f"{u['id']}-o{order}-error", "parent": u["id"], "parent_kind": u["kind"],
                             "function": fn, "order": order, "status": "error", "sites": [],
                             "detail": f"{type(e).__name__}: {e}"[:500]})
                continue
            for m in ms:
                mid = f"{u['id']}-o{order}-{m.index}"
                row = {"id": mid, "parent": u["id"], "parent_kind": u["kind"], "function": fn,
                       "order": order, "index": m.index, "seed": m.seed, "global_seed": args.seed,
                       "sites": m.sites, "status": m.status, "detail": m.detail}
                if m.text is not None:
                    p = out_dir / "units" / f"{mid}.ll"
                    p.parent.mkdir(parents=True, exist_ok=True)
                    p.write_text(m.text)
                    row["path"] = f"units/{mid}.ll"
                    row["features"] = {"categories": ir.features(m.text).categories()}
                rows.append(row)
        return rows

    all_rows: list[dict[str, Any]] = []
    for rows in _parallel(one, units, args.jobs):
        all_rows.extend(rows)
    all_rows.sort(key=lambda r: r["id"])
    write_jsonl(out_dir / "mutants.jsonl", all_rows)
    (out_dir / "mutate.json").write_text(json.dumps({
        "global_seed": args.seed, "per_unit": args.per_unit, "max_order": args.max_order,
        "operators": ops or list(mutate.OPERATORS),
    }, indent=2))
    by = {}
    for r in all_rows:
        by[r["status"]] = by.get(r["status"], 0) + 1
    print(json.dumps(by))
    return 0


def cmd_pairs(args) -> int:
    w = _work(args)
    units = {u["id"]: u for u in corpus_mod.load_units(w / "corpus")}
    rows: list[dict[str, Any]] = []
    skipped: list[dict[str, Any]] = []
    origins = set(args.origins.split(","))

    if "alive2-test" in origins:
        for u in units.values():
            if u["kind"] == "pair":
                rows.append(pairs.make_pair("alive2-test", u["text"], None, "src", "tgt",
                                            {"unit": u["id"]}, {"expected": u["expected"],
                                                                   "alive2_test_args": u["alive2_test_args"]}))

    def opt_one(u: dict[str, Any]) -> tuple[dict | None, dict | None]:
        pipe = u["pipelines"][0]
        tgt, status = pairs.opt_target(u["text"], pipe, u["function"])
        if status != "ok":
            return None, {"origin": "opt", "unit": u["id"], "status": status}
        return pairs.make_pair("opt", u["text"], tgt, u["function"], u["function"],
                               {"unit": u["id"]}, {"pipeline": pipe}), None

    if "opt" in origins:
        fus = [u for u in units.values() if u["kind"] == "function"]
        for ok, bad in _parallel(opt_one, fus, args.jobs):
            if ok:
                rows.append(ok)
            if bad:
                skipped.append(bad)

    mutants = [m for m in read_jsonl(w / "mutants" / "mutants.jsonl") if m["status"] == "ok"]
    if "mutation" in origins:
        for m in mutants:
            u = units[m["parent"]]
            mt = (w / "mutants" / m["path"]).read_text()
            if u["kind"] == "pair":
                # src unchanged, @tgt mutated: the mutant module holds both.
                rows.append(pairs.make_pair("mutation", mt, None, "src", "tgt", {"unit": u["id"], "mutant": m["id"]}))
            else:
                rows.append(pairs.make_pair("mutation", u["text"], mt, u["function"], u["function"],
                                            {"unit": u["id"], "mutant": m["id"]}))

    def mopt_one(m: dict[str, Any]) -> tuple[dict | None, dict | None]:
        u = units[m["parent"]]
        mt = (w / "mutants" / m["path"]).read_text()
        pipe = u["pipelines"][0]
        tgt, status = pairs.opt_target(mt, pipe, u["function"])
        if status != "ok":
            return None, {"origin": "mutation-opt", "mutant": m["id"], "status": status}
        return pairs.make_pair("mutation-opt", mt, tgt, u["function"], u["function"],
                               {"unit": u["id"], "mutant": m["id"]}, {"pipeline": pipe}), None

    if "mutation-opt" in origins:
        fms = [m for m in mutants if units[m["parent"]]["kind"] == "function"]
        for ok, bad in _parallel(mopt_one, fms, args.jobs):
            if ok:
                rows.append(ok)
            if bad:
                skipped.append(bad)

    # Pairs are content-addressed; identical pairs from different origins are kept once
    # (first origin in PAIR_ORIGINS order) and the rest recorded as duplicates.
    order = {o: i for i, o in enumerate(pairs.PAIR_ORIGINS)}
    rows.sort(key=lambda r: (order[r["origin"]], r["id"]))
    seen: set[str] = set()
    kept = []
    for r in rows:
        if r["id"] in seen:
            skipped.append({"origin": r["origin"], "pair": r["id"], "status": "duplicate"})
            continue
        seen.add(r["id"])
        kept.append(r)
    stored = pairs.store(kept, w / "pairs" / "files")
    write_jsonl(w / "pairs" / "pairs.jsonl", stored)
    write_jsonl(w / "pairs" / "skipped.jsonl", skipped)
    by: dict[str, int] = {}
    for r in stored:
        by[r["origin"]] = by.get(r["origin"], 0) + 1
    print(json.dumps({"pairs": by, "skipped": len(skipped)}))
    return 0


def cmd_cases(args) -> int:
    w = _work(args)
    units = corpus_mod.load_units(w / "corpus", kinds=["program", "function"])
    mutants = [m for m in read_jsonl(w / "mutants" / "mutants.jsonl")
               if m["status"] == "ok" and m["parent_kind"] == "function"]
    out_dir = w / "cases" / "files"
    out_dir.mkdir(parents=True, exist_ok=True)
    # (subject id, origin, text, entry or function, is a whole program)
    subjects: list[tuple[str, dict[str, Any], str, str, bool]] = []
    for u in units:
        if u["kind"] == "program":
            subjects.append((u["id"], {"unit": u["id"], "source": u["source"]}, u["text"], u.get("entry", "main"), True))
        else:
            subjects.append((u["id"], {"unit": u["id"], "source": u["source"]}, u["text"], u["function"], False))
    for m in mutants:
        subjects.append((m["id"], {"unit": m["parent"], "mutant": m["id"], "source": "mutation"},
                         (w / "mutants" / m["path"]).read_text(), m["function"], False))

    def one(s: tuple[str, dict[str, Any], str, str, bool]) -> tuple[list[dict], list[dict]]:
        sid, origin, text, fn, is_program = s
        if is_program:
            mods = [(text, fn, None, None)]
        else:
            try:
                n = args.args_per_mutant if "mutant" in origin else args.args_per_function
                ds = drivers.make_drivers(sid, text, fn, n, args.seed)
            except drivers.Unsupported as e:
                return [], [{"subject": sid, **origin, "reason": str(e)}]
            except Exception as e:  # recorded, never silently dropped
                return [], [{"subject": sid, **origin, "reason": f"driver-error: {type(e).__name__}: {e}"[:500]}]
            mods = [(d.module, "__dt_main", d.args, d.seed) for d in ds]
        rs, bad = [], []
        for k, (mod, entry, a, aseed) in enumerate(mods):
            ok, diag = ir.verify(mod)
            if not ok:
                bad.append({"subject": sid, **origin, "reason": "driver-invalid", "detail": diag[:500]})
                continue
            cid = sha256(mod + entry)[:16]
            (out_dir / f"{cid}.ll").write_text(mod)
            rs.append({"id": cid, "subject": sid, **origin, "entry": entry, "args": a,
                       "args_seed": aseed, "path": f"files/{cid}.ll",
                       "features": {"categories": ir.features(mod).categories()}})
        return rs, bad

    cases_p, bad_p = w / "cases" / "cases.jsonl", w / "cases" / "not-executable.jsonl"
    write_jsonl(cases_p, [])
    write_jsonl(bad_p, [])
    n_cases = n_bad = 0
    for rs, bad in _parallel(one, subjects, args.jobs):
        n_cases += write_jsonl(cases_p, rs, append=True)
        n_bad += write_jsonl(bad_p, bad, append=True)
    _sort_jsonl(cases_p, "id")
    _sort_jsonl(bad_p, "subject")
    (w / "cases" / "cases.json").write_text(json.dumps({
        "global_seed": args.seed, "args_per_function": args.args_per_function,
        "args_per_mutant": args.args_per_mutant,
        "arg_generator": vars(drivers.ArgGen()),
    }, indent=2))
    print(json.dumps({"cases": n_cases, "not_executable": n_bad}))
    return 0


def cmd_run_llubi(args) -> int:
    w = _work(args)
    out = w / "results" / "llubi.jsonl"
    done = _resume(out, "run_id")
    seeds = [int(s) for s in args.seeds.split(",")]
    todo = []
    for c in read_jsonl(w / "cases" / "cases.jsonl"):
        if not _shard_ok(c["id"], args.shard):
            continue
        for s in seeds:
            rid = f"{c['id']}:{s}"
            if rid not in done:
                todo.append((c, s, rid))
    if args.limit is not None:
        todo = todo[: args.limit]

    def one(t):
        c, s, rid = t
        mod = (w / "cases" / c["path"]).read_text()
        r = oracle_llubi.run_case(mod, c["entry"], s, timeout=args.timeout, keep_outputs=args.keep_outputs)
        return {"run_id": rid, "case": c["id"], "subject": c["subject"], "unit": c.get("unit"),
                "mutant": c.get("mutant"), "source": c.get("source"),
                "categories": c["features"]["categories"], **r}

    n = 0
    dest = shard_path(out, args.shard)
    for row in _parallel(one, todo, args.jobs):
        write_jsonl(dest, [row], append=True)
        n += 1
    print(json.dumps({"ran": n, "output": str(dest)}))
    return 0


def cmd_run_alive2(args) -> int:
    w = _work(args)
    out = w / "results" / f"alive2-{args.config}.jsonl"
    done = _resume(out, "pair")
    todo = [p for p in read_jsonl(w / "pairs" / "pairs.jsonl")
            if p["id"] not in done and _shard_ok(p["id"], args.shard)]
    if args.limit is not None:
        todo = todo[: args.limit]

    def one(p):
        src, tgt = pairs.load_pair(w / "pairs", p)
        extra = None
        if args.config == "test-args":
            if p["origin"] != "alive2-test":
                return None
            extra = p.get("alive2_test_args", "").split()
        r = oracle_alive2.check(src, tgt, config=args.config, smt_timeout_ms=args.smt_timeout,
                                wall_timeout=args.timeout, extra=extra, src_fn=p["src_fn"])
        return {"pair": p["id"], "origin": p["origin"], **r}

    n = 0
    dest = shard_path(out, args.shard)
    for row in _parallel(one, todo, args.jobs):
        if row is None:
            continue
        write_jsonl(dest, [row], append=True)
        n += 1
    print(json.dumps({"ran": n, "output": str(dest)}))
    return 0


def cmd_run_lean(args) -> int:
    w = _work(args)
    out = w / "results" / f"{args.results_name}.jsonl"
    only = None
    if args.pairs_file:
        only = {l.strip() for l in open(args.pairs_file) if l.strip()}
    done = _resume(out, "run_id")
    alive = {r["pair"]: r for r in read_results(w / "results" / f"alive2-{args.config}.jsonl", "pair")}
    kinds = args.obligations.split(",")
    todo = []
    for p in read_jsonl(w / "pairs" / "pairs.jsonl"):
        if not _shard_ok(p["id"], args.shard) or (only is not None and p["id"] not in only):
            continue
        for k in kinds:
            rid = f"{p['id']}:{k}"
            if rid not in done:
                todo.append((p, k, rid))
    if args.limit is not None:
        todo = todo[: args.limit]

    def prepare(t):
        """(row base, obligation block or None when not applicable)."""
        p, kind, rid = t
        src, tgt = pairs.load_pair(w / "pairs", p)
        sm, sf, tm, tf = pairs.lean_sides(src, tgt, p["src_fn"], p["tgt_fn"])
        base = {"run_id": rid, "pair": p["id"], "origin": p["origin"], "obligation": kind,
                "static_scope": lean_emit.pair_is_translatable(sm, tm)}
        a = alive.get(p["id"])
        witness = lean_emit.witness_term(a["counterexample"]) if a and a.get("counterexample") else None
        base["witness"] = witness
        name = f"case_{p['id']}_{kind.replace('-', '_')}"
        block = lean_emit.obligation_block(kind, sm, sf, tm, tf, witness=witness, name=name)
        return base, block

    def single(base, block):
        r = lean_emit.check_obligation(lean_emit.PRELUDE + block, w / "lean", timeout=args.timeout)
        return {**base, **r, "mode": "single"}

    def one_batch(ts):
        rows, blocks, bases = [], [], {}
        for t in ts:
            base, block = prepare(t)
            if block is None:
                rows.append({**base, "status": "not-applicable"})
            else:
                key = sha256(base["run_id"])[:16]
                bases[key] = (base, block)
                blocks.append((key, block))
        if not blocks:
            return rows
        if len(blocks) == 1:
            return rows + [single(*bases[blocks[0][0]])]
        res, info = lean_emit.check_batch(blocks, w / "lean", timeout=args.batch_timeout)
        if res is None:
            # The batch did not complete: every obligation is re-checked in its own process.
            return rows + [{**single(*bases[k]), "batch_fallback": info} for k, _ in blocks]
        return rows + [{**bases[k][0], **res[k], "file": f"lean/{res[k]['file']}", "mode": "batch",
                        "batch": info["batch_file"], "batch_size": info["batch_size"]} for k, _ in blocks]

    chunks = [todo[i:i + args.batch] for i in range(0, len(todo), args.batch)]
    dest = shard_path(out, args.shard)
    n = 0
    for rows in _parallel(one_batch, chunks, args.jobs):
        write_jsonl(dest, rows, append=True)
        n += len(rows)
    print(json.dumps({"ran": n, "output": str(dest)}))
    return 0


def cmd_triage(args) -> int:
    """Classify every non-matching llubi run and every refinement disagreement
    (`dt/triage.py`), writing report/triage-llubi.jsonl and report/triage-refinement.jsonl."""
    import collections

    w = _work(args)
    rep = w / "report"
    rep.mkdir(parents=True, exist_ok=True)
    cases = {c["id"]: c for c in read_jsonl(w / "cases" / "cases.jsonl")} if not args.skip_llubi else {}
    counts: collections.Counter = collections.Counter()
    if not args.skip_llubi:
        out = rep / "triage-llubi.jsonl"
        write_jsonl(out, [])

        def one(r):
            if r["verdict"] == "match":
                return None
            mod = None
            if r["verdict"] == "mismatch":
                mod = (w / "cases" / cases[r["case"]]["path"]).read_text()
            return triage.triage_llubi(r, mod)

        buf = []
        for t in map(one, read_results(w / "results" / "llubi.jsonl", "run_id")):
            if t is None:
                counts["llubi", "match"] += 1
                continue
            counts["llubi", t["class"]] += 1
            buf.append(t)
            if len(buf) >= 10000:
                write_jsonl(out, buf, append=True)
                buf = []
        write_jsonl(out, buf, append=True)
    # Refinement: our pair verdict from the obligations, against Alive2's.
    al = {r["pair"]: r for r in read_results(w / "results" / f"alive2-{args.config}.jsonl", "pair")}
    obs: dict[str, dict[str, str]] = collections.defaultdict(dict)
    for r in read_results(w / "results" / "lean.jsonl", "run_id"):
        obs[r["pair"]][r["obligation"]] = r["status"]
    rows = []
    for p in read_jsonl(w / "pairs" / "pairs.jsonl"):
        if p["id"] not in obs or p["id"] not in al:
            continue
        o = obs[p["id"]]
        proved = o.get("prove") == "checked"
        disp = "checked" in (o.get("disprove-search"), o.get("disprove-witness"))
        ours = "inconsistent" if proved and disp else "proved" if proved else "disproved" if disp else "unknown"
        t = triage.triage_refinement(p, al[p["id"]]["verdict"], ours)
        if t:
            rows.append(t)
            counts["refinement", t["class"]] += 1
    write_jsonl(rep / "triage-refinement.jsonl", rows)
    print(json.dumps({f"{a}/{b}": n for (a, b), n in sorted(counts.items())}, indent=1))
    return 0


def cmd_report(args) -> int:
    w = _work(args)
    paths = report.build(w, w / "report", alive_config=args.config)
    print(json.dumps({"written": [str(p) for p in paths]}))
    return 0


def cmd_provenance(args) -> int:
    w = _work(args)
    w.mkdir(parents=True, exist_ok=True)
    (w / "provenance.json").write_text(json.dumps(provenance(), indent=2, sort_keys=True))
    print(w / "provenance.json")
    return 0


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(prog="dt", description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--work", help="working directory (default difftest/work or $DT_WORK)")
    ap.add_argument("--jobs", "-j", type=int, default=4)
    sub = ap.add_subparsers(dest="cmd", required=True)

    s = sub.add_parser("collect")
    s.add_argument("--llvm-src", help="llvm-project checkout at LLVM_COMMIT")
    s.add_argument("--alive2-src", help="alive2 checkout at ALIVE2_COMMIT")
    s.add_argument("--transform-dirs", help="comma-separated llvm/test/Transforms subdirectories")
    s.add_argument("--max-instructions", type=int, default=200)
    s.add_argument("--limit", type=int, help="first N files per source (smoke tests)")
    s.add_argument("--allow-unpinned", action="store_true")
    s.set_defaults(fn=cmd_collect)

    s = sub.add_parser("mutate")
    s.add_argument("--seed", type=int, default=DEFAULT_SEED)
    s.add_argument("--per-unit", type=int, default=10)
    s.add_argument("--max-order", type=int, default=1)
    s.add_argument("--operators", help=f"subset of {','.join(mutate.OPERATORS)}")
    s.set_defaults(fn=cmd_mutate)

    s = sub.add_parser("pairs")
    s.add_argument("--origins", default="alive2-test,opt,mutation")
    s.set_defaults(fn=cmd_pairs)

    s = sub.add_parser("cases")
    s.add_argument("--seed", type=int, default=DEFAULT_SEED)
    s.add_argument("--args-per-function", type=int, default=4, help="argument vectors per corpus function")
    s.add_argument("--args-per-mutant", type=int, default=4, help="argument vectors per mutant")
    s.set_defaults(fn=cmd_cases)

    for name, fn in (("run-llubi", cmd_run_llubi), ("run-alive2", cmd_run_alive2), ("run-lean", cmd_run_lean)):
        s = sub.add_parser(name)
        s.add_argument("--shard", help="i/n")
        s.add_argument("--limit", type=int)
        s.set_defaults(fn=fn)
        if name == "run-llubi":
            s.add_argument("--seeds", default="0,1")
            s.add_argument("--timeout", type=float, default=60)
            s.add_argument("--keep-outputs", choices=["all", "mismatch", "none"], default="mismatch")
        if name == "run-alive2":
            s.add_argument("--config", choices=list(oracle_alive2.CONFIGS), default="no-undef-input")
            s.add_argument("--smt-timeout", type=int, default=10000, help="ms")
            s.add_argument("--timeout", type=float, default=120)
        if name == "run-lean":
            s.add_argument("--config", choices=list(oracle_alive2.CONFIGS), default="no-undef-input",
                           help="which Alive2 results supply witnesses")
            s.add_argument("--obligations", default=",".join(lean_emit.OBLIGATIONS))
            s.add_argument("--timeout", type=float, default=300, help="s, per obligation checked alone")
            s.add_argument("--batch", type=int, default=16,
                           help="obligations per Lean process (1: one process per obligation)")
            s.add_argument("--pairs-file", help="only the pairs listed (one id per line)")
            s.add_argument("--results-name", default="lean",
                           help="results/<name>.jsonl (a separate set, e.g. a re-run on newer code)")
            s.add_argument("--batch-timeout", type=float, default=900,
                           help="s, per batch; on timeout the batch is re-checked one obligation per process")

    s = sub.add_parser("triage")
    s.add_argument("--config", choices=list(oracle_alive2.CONFIGS), default="no-undef-input")
    s.add_argument("--skip-llubi", action="store_true")
    s.set_defaults(fn=cmd_triage)

    s = sub.add_parser("report")
    s.add_argument("--config", choices=list(oracle_alive2.CONFIGS), default="no-undef-input")
    s.set_defaults(fn=cmd_report)

    s = sub.add_parser("provenance")
    s.set_defaults(fn=cmd_provenance)

    args = ap.parse_args(argv)
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
