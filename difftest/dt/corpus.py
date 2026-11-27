"""Corpus collection: turn pinned upstream test suites into deduplicated, verified units.

A *unit* is one self-contained LLVM IR module accepted by the pinned LLVM verifier:

* ``function``: one function definition (plus the declarations and globals it references),
  extracted with ``llvm-extract`` from an LLVM regression test. Used for refinement pairs
  (``pairs.py``) and, through a synthesized driver (``drivers.py``), for execution.
* ``program``: a whole module with an entry point (``main``), executed as is.
* ``pair``: a module defining ``@src`` and ``@tgt`` (Alive2's ``*.srctgt.ll`` convention), with
  the test's expected verdict when the test states one.

Every candidate yields exactly one row, in ``units.jsonl`` (accepted), ``rejected.jsonl``
(with a reason from ``REJECT_REASONS``) or ``duplicates.jsonl`` (with the unit it duplicates),
so the corpus-construction funnel in the paper is a direct count of these files.
"""

from __future__ import annotations

import concurrent.futures as cf
import json
import re
from pathlib import Path
from typing import Any, Iterable

from . import ir
from .common import WORK, git_rev, read_jsonl, read_pins, sha256, write_jsonl

# Default pass directories (llvm/test/Transforms/<dir>): peephole and scalar passes whose tests
# are mostly single-function, loop-free or small-CFG integer/FP code, the scope of both oracles.
DEFAULT_TRANSFORM_DIRS = [
    "InstCombine", "InstSimplify", "AggressiveInstCombine", "Reassociate", "EarlyCSE",
    "CorrelatedValuePropagation", "SCCP", "SimplifyCFG", "GVN", "DeadStoreElimination",
    "MemCpyOpt", "SROA",
]

REJECT_REASONS = {
    "parse-or-verify": "rejected by the pinned LLVM parser or verifier",
    "extract-failed": "llvm-extract could not isolate the function",
    "unsupported-run-line": "test relies on split-file, %S/%p inputs, or has no opt RUN line",
    "target-specific": "uses a target-specific intrinsic (llvm.<target>.*) or inline asm",
    "too-large": "more instructions than --max-instructions",
    "no-src-tgt": "Alive2 test does not define both @src and @tgt",
    "declaration-only": "no function bodies",
}

TARGET_INTRINSIC_RE = re.compile(
    r"@llvm\.(x86|aarch64|arm|amdgcn|r600|nvvm|ppc|riscv|wasm|hexagon|mips|s390|loongarch|spv|dx)\."
)
RUN_RE = re.compile(r"^\s*;\s*RUN:\s*(.*)$", re.M)
PASSES_RE = re.compile(r"-passes=(?:'([^']*)'|\"([^\"]*)\"|(\S+))")


def run_lines(text: str) -> list[str]:
    """RUN lines with `\\` continuations joined."""
    lines, cur = [], ""
    for m in RUN_RE.finditer(text):
        part = m.group(1).rstrip()
        if part.endswith("\\"):
            cur += part[:-1] + " "
        else:
            lines.append((cur + part).strip())
            cur = ""
    return lines


def opt_passes(text: str) -> tuple[list[str], str | None]:
    """All `-passes=` pipelines of `opt` RUN lines, and a reason if the test is unusable."""
    rl = run_lines(text)
    if any("split-file" in l or "%S" in l or "%p" in l for l in rl):
        return [], "unsupported-run-line"
    pipelines = []
    for l in rl:
        if not re.search(r"\bopt\b", l):
            continue
        m = PASSES_RE.search(l)
        if m:
            p = next(g for g in m.groups() if g is not None)
            if p not in pipelines:
                pipelines.append(p)
    if not pipelines:
        return [], "unsupported-run-line"
    return pipelines, None


def unit_row(kind: str, source: str, origin: dict[str, Any], canonical: str,
             extra: dict[str, Any] | None = None) -> dict[str, Any]:
    feats = ir.features(canonical)
    row = {
        "kind": kind,
        "source": source,
        "origin": origin,
        "text_sha256": sha256(ir.strip_header(canonical)),
        "structural_sha256": ir.structural_hash(canonical),
        "features": {
            "categories": feats.categories(),
            "opcodes": feats.opcodes,
            "intrinsics": feats.intrinsics,
            "int_widths": feats.int_widths,
            "blocks": feats.blocks,
            "instructions": feats.instructions,
        },
        "text": ir.strip_header(canonical),
    }
    row["id"] = row["structural_sha256"][:16]
    if extra:
        row.update(extra)
    return row


def reject(source: str, origin: dict[str, Any], reason: str, detail: str = "") -> dict[str, Any]:
    assert reason in REJECT_REASONS, reason
    return {"source": source, "origin": origin, "reason": reason, "detail": detail[:2000]}


# --------------------------------------------------------------------------------------------
# Sources


def llvm_transform_file(path: Path, rel: str, max_instr: int) -> list[dict[str, Any]]:
    """Units from one llvm/test/Transforms test file: one per defined function."""
    text = path.read_text(errors="replace")
    origin = {"file": rel}
    pipelines, why = opt_passes(text)
    if why:
        return [{"_reject": reject("llvm-transforms", origin, why)}]
    ok, canon = ir.verify(text)
    if not ok:
        return [{"_reject": reject("llvm-transforms", origin, "parse-or-verify", canon)}]
    names = ir.defined_functions(canon)
    if not names:
        return [{"_reject": reject("llvm-transforms", origin, "declaration-only")}]
    out = []
    for name in names:
        o = {"file": rel, "function": name.strip('"')}
        r = ir.extract_function(canon, name)
        if r.exit != 0:
            out.append({"_reject": reject("llvm-transforms", o, "extract-failed", r.stderr)})
            continue
        ok, unit = ir.verify(r.stdout)
        if not ok:
            out.append({"_reject": reject("llvm-transforms", o, "parse-or-verify", unit)})
            continue
        if TARGET_INTRINSIC_RE.search(unit) or re.search(r"\basm\b\s+(sideeffect\s+)?\"", unit):
            out.append({"_reject": reject("llvm-transforms", o, "target-specific")})
            continue
        if ir.features(unit).instructions > max_instr:
            out.append({"_reject": reject("llvm-transforms", o, "too-large")})
            continue
        out.append(unit_row("function", "llvm-transforms", o, unit,
                            {"function": name.strip('"'), "pipelines": pipelines}))
    return out


def llubi_test_file(path: Path, rel: str) -> list[dict[str, Any]]:
    text = path.read_text(errors="replace")
    origin = {"file": rel}
    ok, canon = ir.verify(text)
    if not ok:
        return [{"_reject": reject("llubi-tests", origin, "parse-or-verify", canon)}]
    rl = run_lines(text)
    return [unit_row("program", "llubi-tests", origin, canon, {"run_lines": rl, "entry": "main"})]


ERROR_RE = re.compile(r"^;\s*ERROR:\s*(.*)$", re.M)
TEST_ARGS_RE = re.compile(r"^;\s*TEST-ARGS:\s*(.*)$", re.M)


def alive2_test_file(path: Path, rel: str) -> list[dict[str, Any]]:
    """An Alive2 `*.srctgt.ll` test. Its expected verdict is `incorrect` iff it has `; ERROR:`."""
    text = path.read_text(errors="replace")
    origin = {"file": rel}
    ok, canon = ir.verify(text)
    if not ok:
        return [{"_reject": reject("alive2-tests", origin, "parse-or-verify", canon)}]
    names = {n.strip('"') for n in ir.defined_functions(canon)}
    if not {"src", "tgt"} <= names:
        return [{"_reject": reject("alive2-tests", origin, "no-src-tgt")}]
    if TARGET_INTRINSIC_RE.search(canon):
        return [{"_reject": reject("alive2-tests", origin, "target-specific")}]
    errs = ERROR_RE.findall(text)
    args = TEST_ARGS_RE.findall(text)
    return [unit_row("pair", "alive2-tests", origin, canon, {
        "expected": {"verdict": "incorrect" if errs else "correct", "error": errs[0].strip() if errs else None},
        "alive2_test_args": " ".join(a.strip() for a in args),
        "xfail": bool(re.search(r"^;\s*XFAIL:", text, re.M)),
    })]


def repo_ll_file(path: Path, rel: str) -> list[dict[str, Any]]:
    text = path.read_text(errors="replace")
    origin = {"file": rel}
    ok, canon = ir.verify(text)
    if not ok:
        return [{"_reject": reject("repo-tests", origin, "parse-or-verify", canon)}]
    entry = "main"
    m = re.search(r"^; ARGS:.*--entry(?:-function)?[= ](\S+)", text, re.M)
    if m:
        entry = m.group(1)
    return [unit_row("program", "repo-tests", origin, canon, {"entry": entry})]


# --------------------------------------------------------------------------------------------
# Driver


def _files(root: Path, pattern: str) -> list[Path]:
    return sorted(p for p in root.glob(pattern) if p.is_file())


def collect(
    llvm_src: Path | None,
    alive2_src: Path | None,
    repo_root: Path,
    transform_dirs: list[str],
    max_instr: int,
    jobs: int,
    limit: int | None,
    out: Path,
    allow_unpinned: bool = False,
) -> dict[str, int]:
    pins = read_pins()
    tasks: list[tuple[str, Any, tuple]] = []
    source_revs: dict[str, str | None] = {}

    def check_pin(name: str, path: Path, pin_key: str) -> None:
        rev = git_rev(path)
        source_revs[name] = rev
        if rev != pins.get(pin_key) and not allow_unpinned:
            raise SystemExit(f"{name} checkout {path} is at {rev}, pin {pin_key}={pins.get(pin_key)}"
                             " (pass --allow-unpinned to override; the revision is recorded)")

    if llvm_src:
        check_pin("llvm-project", llvm_src, "LLVM_COMMIT")
        for d in transform_dirs:
            for p in _files(llvm_src / "llvm" / "test" / "Transforms" / d, "**/*.ll"):
                tasks.append(("llvm-transforms", llvm_transform_file,
                              (p, str(p.relative_to(llvm_src)), max_instr)))
        for p in _files(llvm_src / "llvm" / "test" / "tools" / "llubi", "*.ll"):
            tasks.append(("llubi-tests", llubi_test_file, (p, str(p.relative_to(llvm_src)))))
    if alive2_src:
        check_pin("alive2", alive2_src, "ALIVE2_COMMIT")
        for p in _files(alive2_src / "tests" / "alive-tv", "**/*.srctgt.ll"):
            tasks.append(("alive2-tests", alive2_test_file, (p, str(p.relative_to(alive2_src)))))
    for p in _files(repo_root / "Tests" / "ll", "*.ll"):
        tasks.append(("repo-tests", repo_ll_file, (p, str(p.relative_to(repo_root)))))

    if limit is not None:
        # Deterministic subsample for smoke tests: the first `limit` files of each source.
        seen: dict[str, int] = {}
        kept = []
        for t in tasks:
            seen[t[0]] = seen.get(t[0], 0) + 1
            if seen[t[0]] <= limit:
                kept.append(t)
        tasks = kept

    with cf.ThreadPoolExecutor(max_workers=jobs) as ex:
        results = list(ex.map(lambda t: t[1](*t[2]), tasks))

    # Deduplicate in task order (sources in the order above, files sorted): the first unit with
    # a given structural hash is kept, later ones are recorded as duplicates of it.
    accepted, rejected, dups = [], [], []
    first: dict[str, str] = {}
    units_dir = out / "units"
    units_dir.mkdir(parents=True, exist_ok=True)
    for rows in results:
        for r in rows:
            if "_reject" in r:
                rejected.append(r["_reject"])
                continue
            # An Alive2 test's meaning includes its expectation and its alive-tv arguments, so
            # two tests with the same IR but different TEST-ARGS are different units.
            key = r["structural_sha256"]
            if r["kind"] == "pair":
                key += "|" + json.dumps([r["expected"], r["alive2_test_args"]], sort_keys=True)
            if key in first:
                dups.append({"source": r["source"], "origin": r["origin"], "dup_of": first[key]})
                continue
            if r["kind"] == "pair":
                r["id"] = sha256(key)[:16]
            first[key] = r["id"]
            text = r.pop("text")
            (units_dir / f"{r['id']}.ll").write_text(text)
            r["path"] = f"units/{r['id']}.ll"
            accepted.append(r)

    write_jsonl(out / "units.jsonl", accepted)
    write_jsonl(out / "rejected.jsonl", rejected)
    write_jsonl(out / "duplicates.jsonl", dups)
    (out / "corpus.json").write_text(json.dumps({
        "source_revisions": source_revs,
        "transform_dirs": transform_dirs,
        "max_instructions": max_instr,
        "limit_per_source": limit,
        "candidates": sum(len(r) for r in results),
        "accepted": len(accepted),
        "rejected": len(rejected),
        "duplicates": len(dups),
    }, indent=2, sort_keys=True))
    return {"accepted": len(accepted), "rejected": len(rejected), "duplicates": len(dups)}


def load_units(corpus: Path, kinds: Iterable[str] | None = None) -> list[dict[str, Any]]:
    ks = set(kinds) if kinds else None
    rows = [r for r in read_jsonl(corpus / "units.jsonl") if ks is None or r["kind"] in ks]
    for r in rows:
        r["text"] = (corpus / r["path"]).read_text()
    return rows


def default_corpus() -> Path:
    return WORK / "corpus"
