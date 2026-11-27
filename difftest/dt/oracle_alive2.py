"""Refinement verdicts from Alive2 (`alive-tv`).

Each pair module defines ``@src`` and ``@tgt``; ``alive-tv`` checks that ``tgt`` refines
``src``. The tool's text output is parsed into one verdict from ``VERDICTS``:

* ``correct``: "Transformation seems to be correct!" (``syntactic_eq`` records the
  "(syntactically equal)" variant).
* ``incorrect``: "Transformation doesn't verify!" with an SMT counterexample.
  ``error_kind`` is one of ``ERROR_KINDS``; ``counterexample`` lists the input values of
  Alive2's (minimized) model, parsed where they are integers, floats, ``poison`` or ``undef``;
  ``unique`` records Alive2's "The counterexample is unique" note.
* ``inconclusive``: Alive2 could not decide: SMT timeout or memory-out, or a counterexample
  that depends on approximated semantics ("Couldn't prove the correctness"). ``reason`` says
  which.
* ``unsupported``: Alive2 does not model a feature of the input ("ERROR: Unsupported ...",
  type-check failure, signature mismatch).
* ``error``: anything else, including a crash or a wall-clock timeout of the process.

Configurations. Alive2's default treats function inputs as possibly ``undef``; our default
semantics (``SemanticsConfig.modern``) disables ``undef``. The primary configuration is
therefore ``--disable-undef-input``; the default configuration is recorded as a secondary
configuration, so results can be reported both ways. ``test-args`` runs each Alive2 test with
its own ``; TEST-ARGS:``, the configuration its expected verdict refers to.
"""

from __future__ import annotations

import re
from typing import Any

from .common import run, sha256, tool

VERDICTS = ["correct", "incorrect", "inconclusive", "unsupported", "error"]
ERROR_KINDS = {
    "Value mismatch": "value-mismatch",
    "Source is more defined than target": "ub-introduced",
    "Target is more poisonous than source": "poison-introduced",
    "Target's return value is more undefined": "undef-introduced",
    "Mismatch in memory": "memory-mismatch",
}
CONFIGS = {
    "no-undef-input": ["--disable-undef-input"],
    "default": [],
    # Alive2 tests only: each test's own `; TEST-ARGS:` (the configuration its expected verdict
    # refers to). Used for the oracle sanity check.
    "test-args": [],
}

SUMMARY_RE = re.compile(
    r"Summary:\s+(\d+) correct transformations\s+(\d+) incorrect transformations\s+"
    r"(\d+) failed-to-prove transformations\s+(\d+) Alive2 errors"
)
EXAMPLE_VAR_RE = re.compile(r"^(?P<ty>.+?) (?P<name>%[-\w.$\"]+) = (?P<val>.*)$")
INT_VAL_RE = re.compile(r"^#x([0-9a-f]+) \((-?\d+)\)")
FLOAT_VAL_RE = re.compile(r"^#x([0-9a-f]+) \(([^)]*)\)")


def parse_value(ty: str, raw: str) -> dict[str, Any]:
    raw = raw.strip()
    if raw == "poison":
        return {"kind": "poison"}
    if raw == "undef":
        return {"kind": "undef"}
    m = re.fullmatch(r"i(\d+)", ty)
    if m:
        v = INT_VAL_RE.match(raw)
        if v:
            w = int(m.group(1))
            return {"kind": "int", "width": w, "bits": int(v.group(1), 16) & ((1 << w) - 1)}
    if ty in ("half", "bfloat", "float", "double"):
        v = FLOAT_VAL_RE.match(raw)
        if v:
            return {"kind": "float", "type": ty, "bits": int(v.group(1), 16), "text": v.group(2)}
    return {"kind": "raw", "text": raw}


def parse_output(out: str) -> dict[str, Any]:
    rec: dict[str, Any] = {}
    s = SUMMARY_RE.search(out)
    rec["summary"] = [int(x) for x in s.groups()] if s else None
    if "Transformation seems to be correct!" in out:
        rec["verdict"] = "correct"
        rec["syntactic_eq"] = "(syntactically equal)" in out
        return rec
    if "Couldn't prove the correctness of the transformation" in out:
        rec["verdict"], rec["reason"] = "inconclusive", "approximation"
        rec["approximations"] = re.findall(r"^ - (.*)$", out, re.M)
        return rec
    m = re.search(r"^ERROR: (.*)$", out, re.M)
    if "Transformation doesn't verify!" in out and m and m.group(1).startswith("program doesn't type check"):
        rec["verdict"], rec["reason"] = "unsupported", "type-check"
        return rec
    if "Transformation doesn't verify!" in out:
        rec["verdict"] = "incorrect"
        msg = m.group(1).strip() if m else ""
        rec["error"] = msg
        rec["error_kind"] = next((v for k, v in ERROR_KINDS.items() if msg.startswith(k)), "other")
        rec["unique"] = "NOTE: The counterexample is unique." in out
        cex = []
        ex = out.split("\nExample:\n", 1)
        if len(ex) == 2:
            for line in ex[1].splitlines():
                if not line.strip() or line.startswith(("Source", "Target")):
                    break
                vm = EXAMPLE_VAR_RE.match(line)
                if vm:
                    cex.append({"name": vm["name"], "type": vm["ty"].strip(), "raw": vm["val"].strip(),
                                **{"value": parse_value(vm["ty"].strip(), vm["val"])}})
        rec["counterexample"] = cex
        return rec
    if m:
        msg = m.group(1).strip()
        rec["error"] = msg
        if msg.startswith("Timeout") or "Timeout" in msg:
            rec["verdict"], rec["reason"] = "inconclusive", "smt-timeout"
        elif msg.startswith("Out of memory") or "memory" in msg.lower() and "out of" in msg.lower():
            rec["verdict"], rec["reason"] = "inconclusive", "smt-memout"
        elif msg.startswith("SMT Error"):
            rec["verdict"], rec["reason"] = "inconclusive", "smt-error"
        elif "Unsupported" in msg or "Signature mismatch" in msg or "unsupported" in msg:
            rec["verdict"], rec["reason"] = "unsupported", msg[:200]
        else:
            rec["verdict"], rec["reason"] = "error", msg[:200]
        return rec
    rec["verdict"], rec["reason"] = "error", "unparsed-output"
    return rec


def check(src_module: str, tgt_module: str | None = None, config: str = "no-undef-input",
          smt_timeout_ms: int = 10000, wall_timeout: float = 120.0, extra: list[str] | None = None,
          keep_output: bool = True) -> dict[str, Any]:
    """Check one pair. With ``tgt_module=None``, ``src_module`` defines ``@src`` and ``@tgt``
    (single-file mode); otherwise the two modules are compared function by function, by name
    (two-file mode, used for opt-derived and mutation-derived pairs)."""
    import tempfile

    args = [f"--smt-to={smt_timeout_ms}", *CONFIGS[config], *(extra or [])]
    with tempfile.TemporaryDirectory() as d:
        files = [f"{d}/src.ll"]
        open(files[0], "w").write(src_module)
        if tgt_module is None:
            args = ["--src-fn=src", "--tgt-fn=tgt", *args]
        else:
            files.append(f"{d}/tgt.ll")
            open(files[1], "w").write(tgt_module)
        r = run([tool("alive-tv"), *args, *files], timeout=wall_timeout)
        out = (r.stdout + "\n" + r.stderr).replace(d + "/", "")
    if r.timeout:
        rec = {"verdict": "error", "reason": "wall-timeout"}
    elif r.exit is not None and r.exit < 0:
        rec = {"verdict": "error", "reason": f"signal-{-r.exit}"}
    else:
        rec = parse_output(out)
        if rec.get("summary") and sum(rec["summary"]) > 1:
            rec["note"] = "more than one function pair compared"
    rec.update({
        "config": config,
        "args": args,
        "exit": r.exit,
        "wall_s": r.wall_s,
        "pair_sha256": sha256(src_module + "\0" + (tgt_module or "")),
    })
    if keep_output:
        rec["output"] = out[-20000:]
    return rec
