"""Differential execution against llubi.

A *case* is (module text, entry function, llubi options, seed). Both interpreters receive the
module on standard input (so diagnostics name ``<stdin>`` on both sides) with identical
options, and the comparison is on the full observable behaviour: exit code, standard output,
and standard error, which with ``--verbose`` is the instruction-level trace. Our frontend aims
to reproduce llubi byte for byte, so the comparison is exact equality; no normalization is
applied besides decoding as UTF-8 with replacement.

Verdicts (``VERDICTS``) are assigned by the first matching rule, in this order, so each case
gets exactly one verdict:

1. ``invalid``: llubi rejects the module (parse or verifier error). Not a test of our semantics.
2. ``timeout``: either side exceeded the wall-clock limit (sub-classified in ``timeout_side``).
3. ``llubi-crash``: llubi died from a signal (e.g. an assertion), i.e. a reference failure.
4. ``ours-crash``: our process died from a signal or out of memory.
5. ``ours-unsupported``: our parser rejected a module llubi accepted.
6. ``match``: exit code, stdout and stderr are identical.
7. ``mismatch``: anything else, sub-classified by the first differing channel
   (``exit`` > ``stdout`` > ``trace``) and, for traces, the first differing line number.
"""

from __future__ import annotations

import re
from typing import Any

from .common import Run, ours, run, sha256, tool

VERDICTS = ["invalid", "timeout", "llubi-crash", "ours-crash", "ours-unsupported", "match", "mismatch"]

DEFAULT_OPTIONS = ["--verbose", "--max-steps=100000"]
LLUBI_REJECT_RE = re.compile(r"(error: .*input module is broken|^<stdin>:\d+:\d+: error:|^llubi: <stdin>:\d+:\d+: error:)", re.M)
OURS_PARSE_RE = re.compile(r"^llubi: <stdin>: error:", re.M)


def _side(r: Run, keep: bool) -> dict[str, Any]:
    d: dict[str, Any] = {
        "exit": r.exit,
        "timeout": r.timeout,
        "wall_s": r.wall_s,
        "stdout_sha256": sha256(r.stdout),
        "stderr_sha256": sha256(r.stderr),
        "stderr_lines": r.stderr.count("\n"),
    }
    if keep:
        d["stdout"] = r.stdout[-20000:]
        d["stderr"] = r.stderr[-50000:]
    return d


def first_diff_line(a: str, b: str) -> int | None:
    la, lb = a.splitlines(), b.splitlines()
    for i, (x, y) in enumerate(zip(la, lb)):
        if x != y:
            return i + 1
    return None if len(la) == len(lb) else min(len(la), len(lb)) + 1


def classify(ref: Run, our: Run) -> tuple[str, dict[str, Any]]:
    info: dict[str, Any] = {}
    if not ref.timeout and ref.exit not in (None,) and ref.exit != 0 and LLUBI_REJECT_RE.search(ref.stderr):
        return "invalid", info
    if ref.timeout or our.timeout:
        info["timeout_side"] = "both" if ref.timeout and our.timeout else ("llubi" if ref.timeout else "ours")
        return "timeout", info
    if ref.exit is not None and ref.exit < 0:
        info["signal"] = -ref.exit
        return "llubi-crash", info
    if our.exit is not None and (our.exit < 0 or "out of memory" in our.stderr.lower()):
        info["signal"] = -our.exit if our.exit < 0 else None
        return "ours-crash", info
    if our.exit == 1 and OURS_PARSE_RE.search(our.stderr):
        info["message"] = OURS_PARSE_RE.split(our.stderr, maxsplit=1)[-1].strip().splitlines()[0][:500]
        return "ours-unsupported", info
    if ref.exit == our.exit and ref.stdout == our.stdout and ref.stderr == our.stderr:
        return "match", info
    if ref.exit != our.exit:
        info["channel"] = "exit"
    elif ref.stdout != our.stdout:
        info["channel"] = "stdout"
        info["first_diff_line"] = first_diff_line(ref.stdout, our.stdout)
    else:
        info["channel"] = "trace"
        info["first_diff_line"] = first_diff_line(ref.stderr, our.stderr)
    return "mismatch", info


def run_case(module: str, entry: str, seed: int, options: list[str] | None = None,
             timeout: float = 60.0, keep_outputs: str = "mismatch") -> dict[str, Any]:
    """Run one case on both interpreters and classify it. ``keep_outputs`` is ``all``,
    ``mismatch`` (outputs kept for every verdict except ``match``) or ``none``."""
    opts = list(options if options is not None else DEFAULT_OPTIONS)
    argv_tail = [*opts, f"--entry-function={entry}", f"--seed={seed}", "-"]
    ref = run([tool("llubi"), *argv_tail], stdin=module, timeout=timeout)
    our = run([ours(), "llubi", *argv_tail], stdin=module, timeout=timeout)
    verdict, info = classify(ref, our)
    keep = keep_outputs == "all" or (keep_outputs == "mismatch" and verdict != "match")
    return {
        "options": argv_tail[:-1],
        "seed": seed,
        "module_sha256": sha256(module),
        "verdict": verdict,
        "detail": info,
        "llubi": _side(ref, keep),
        "ours": _side(our, keep),
    }
