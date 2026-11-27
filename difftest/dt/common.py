"""Shared infrastructure: paths, tool resolution, subprocess execution, hashing, seeds, JSONL.

Everything that influences an experiment's outcome is either a pinned input (`tools/pins.env`),
an explicit seed, or recorded in the run's `provenance.json` (`provenance()`), so that each
result row can be traced back to exactly how it was produced.
"""

from __future__ import annotations

import hashlib
import json
import os
import resource
import shutil
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Iterator

DIFFTEST = Path(__file__).resolve().parent.parent
REPO = DIFFTEST.parent
WORK = Path(os.environ.get("DT_WORK", DIFFTEST / "work"))
ORACLES = Path(os.environ.get("DT_ORACLES", DIFFTEST / ".oracles"))

SCHEMA_VERSION = 1

# LLVM allows integer types up to i8388608; their constants exceed Python's default limit on
# int <-> str conversion.
import sys as _sys

_sys.set_int_max_str_digits(0)


def read_pins() -> dict[str, str]:
    pins: dict[str, str] = {}
    for line in (DIFFTEST / "tools" / "pins.env").read_text().splitlines():
        line = line.strip()
        if line and not line.startswith("#") and "=" in line:
            k, v = line.split("=", 1)
            pins[k.strip()] = v.strip()
    return pins


def tool(name: str) -> str:
    """Resolve an external tool: `$DT_<NAME>`, then `$DT_ORACLES/bin`, then `PATH`."""
    env = os.environ.get("DT_" + name.upper().replace("-", "_"))
    if env:
        return env
    cand = ORACLES / "bin" / name
    if cand.exists():
        return str(cand)
    found = shutil.which(name)
    if found:
        return found
    raise FileNotFoundError(
        f"tool '{name}' not found (build it with difftest/tools/build_oracles.sh or set DT_{name.upper()})"
    )


def ours() -> str:
    """The lean-nano-llvm executable under test."""
    return os.environ.get("DT_OURS", str(REPO / ".lake" / "build" / "bin" / "lean-nano-llvm"))


@dataclass
class Run:
    argv: list[str]
    exit: int | None  # None on timeout
    stdout: str
    stderr: str
    wall_s: float
    timeout: bool
    max_rss_kb: int


def run(
    argv: list[str],
    *,
    stdin: str | None = None,
    timeout: float = 60.0,
    mem_mb: int | None = 8192,
    cwd: str | Path | None = None,
) -> Run:
    """Run a command with a wall-clock timeout and an address-space limit.

    Output is decoded as UTF-8 with replacement so that byte-level differences remain visible
    (as U+FFFD) instead of aborting the harness.
    """

    # The address-space limit is applied with `prlimit` rather than a `preexec_fn`: a
    # `preexec_fn` forces fork+exec of the (large) harness process, which is ~20x slower than
    # the posix_spawn path subprocess uses otherwise.
    if mem_mb and shutil.which("prlimit"):
        argv_exec = ["prlimit", f"--as={mem_mb * 1024 * 1024}", "--", *argv]
    else:
        argv_exec = argv

    t0 = time.monotonic()
    before = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    try:
        p = subprocess.run(
            argv_exec,
            input=stdin.encode() if stdin is not None else None,
            capture_output=True,
            timeout=timeout,
            cwd=cwd,
        )
        out, err, code, to = p.stdout, p.stderr, p.returncode, False
    except subprocess.TimeoutExpired as e:
        out, err, code, to = e.stdout or b"", e.stderr or b"", None, True
    wall = time.monotonic() - t0
    rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    return Run(
        argv=argv,
        exit=code,
        stdout=out.decode("utf-8", "replace"),
        stderr=err.decode("utf-8", "replace"),
        wall_s=round(wall, 4),
        timeout=to,
        max_rss_kb=max(rss, before),
    )


def sha256(text: str | bytes) -> str:
    if isinstance(text, str):
        text = text.encode()
    return hashlib.sha256(text).hexdigest()


def derive_seed(*parts: Any) -> int:
    """A 64-bit seed derived from a global seed and stable identifiers.

    Seeds depend only on content hashes and indices, never on enumeration order or wall time,
    so any single case can be regenerated in isolation and runs are order-independent.
    """
    h = hashlib.sha256("\x1f".join(str(p) for p in parts).encode()).digest()
    return int.from_bytes(h[:8], "little")


def write_jsonl(path: Path, rows: Iterable[dict[str, Any]], append: bool = False) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    n = 0
    with path.open("a" if append else "w") as f:
        for r in rows:
            f.write(json.dumps(r, sort_keys=True, ensure_ascii=False) + "\n")
            n += 1
    return n


def read_jsonl(path: Path) -> Iterator[dict[str, Any]]:
    """Rows of a JSONL file. A line that does not parse (a row cut short when a run was killed
    mid-write) is skipped with a warning, so the row is simply re-run on resume."""
    if not path.exists():
        return
    with path.open() as f:
        for n, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            try:
                yield json.loads(line)
            except ValueError:
                print(f"warning: {path}:{n}: skipping malformed row", file=_sys.stderr)


def shard_path(path: Path, shard: str | None) -> Path:
    """Where a sharded run writes: ``results/x.jsonl`` -> ``results/x.shard-3-of-16.jsonl``, so
    concurrent shards never write the same file."""
    if not shard:
        return path
    i, n = shard.split("/")
    return path.with_name(f"{path.stem}.shard-{i}-of-{n}{path.suffix}")


def result_files(path: Path) -> list[Path]:
    """The unsharded result file and every shard file of it."""
    return [path, *sorted(path.parent.glob(f"{path.stem}.shard-*{path.suffix}"))]


def read_results(path: Path, key: str | None = None) -> Iterator[dict[str, Any]]:
    """Rows of a result file and all its shards. With ``key``, a row whose key was already seen
    is dropped (first occurrence wins), so overlapping re-runs never double count."""
    seen: set[str] = set()
    for p in result_files(path):
        for r in read_jsonl(p):
            if key is not None:
                if r[key] in seen:
                    continue
                seen.add(r[key])
            yield r


def git_rev(path: Path) -> str | None:
    try:
        return subprocess.run(
            ["git", "-C", str(path), "rev-parse", "HEAD"], capture_output=True, text=True, check=True
        ).stdout.strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        return None


def git_dirty(path: Path) -> bool | None:
    try:
        out = subprocess.run(
            ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"],
            capture_output=True, text=True, check=True,
        ).stdout
        return bool(out.strip())
    except (subprocess.CalledProcessError, FileNotFoundError):
        return None


def tool_version(name: str) -> str | None:
    try:
        exe = tool(name)
    except FileNotFoundError:
        return None
    r = run([exe, "--version"], timeout=20)
    text = (r.stdout or r.stderr).strip()
    # The whole banner: LLVM's first line is just "LLVM (http://llvm.org/):".
    return " | ".join(l.strip() for l in text.splitlines() if l.strip()) or None


def _cmd_version(argv: list[str]) -> str | None:
    try:
        r = run(argv, timeout=60, cwd=REPO)
    except FileNotFoundError:
        return None
    return (r.stdout or r.stderr).strip() or None


def _host() -> dict[str, Any]:
    h: dict[str, Any] = {"cpus": os.cpu_count(), "uname": " ".join(os.uname())}
    try:
        lscpu = subprocess.run(["lscpu"], capture_output=True, text=True).stdout
        for k in ("Model name", "Architecture", "Socket(s)", "NUMA node(s)"):
            for line in lscpu.splitlines():
                if line.startswith(k + ":"):
                    h[k.lower().replace("(s)", "s").replace(" ", "_")] = line.split(":", 1)[1].strip()
        for line in Path("/proc/meminfo").read_text().splitlines():
            if line.startswith("MemTotal:"):
                h["mem_total_kb"] = int(line.split()[1])
    except (OSError, ValueError):
        pass
    return h


def provenance(extra: dict[str, Any] | None = None) -> dict[str, Any]:
    """Everything needed to reproduce a run: pins, tool versions, our commit, host."""
    versions_file = ORACLES / "versions.json"
    p: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "pins": read_pins(),
        "oracle_build": json.loads(versions_file.read_text()) if versions_file.exists() else None,
        "lean_nano_llvm_commit": git_rev(REPO),
        "lean_nano_llvm_dirty": git_dirty(REPO),
        "tools": {t: tool_version(t) for t in ("opt", "llubi", "alive-tv")},
        "host": _host(),
        "lean": _cmd_version(["lake", "env", "lean", "--version"]),
        "python": _sys.version.split()[0],
        "time_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    if extra:
        p.update(extra)
    return p
