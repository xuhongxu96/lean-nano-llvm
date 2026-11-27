"""Refinement pairs (src, tgt) and execution cases, derived from the corpus and the mutants.

Pair origins (``PAIR_ORIGINS``):

* ``alive2-test``: an Alive2 ``*.srctgt.ll`` test as is (expected verdict from the test).
* ``opt``: translation validation of LLVM's own tests, as in Alive2's evaluation: ``src`` is a
  function unit, ``tgt`` is ``opt -passes=<the test's first RUN pipeline>`` applied to it.
  Pairs whose target prints identically to the source are recorded as ``identity`` and kept out
  of the main tables.
* ``mutation``: ``src`` is a unit, ``tgt`` is one of its mutants (for Alive2 tests, a mutant of
  ``@tgt``). Mutations are not optimizations, so these pairs exercise both verdicts.
* ``mutation-opt``: ``src`` is a mutant and ``tgt`` is ``opt`` applied to it (translation
  validation on mutated inputs).

Execution cases: every ``program`` unit runs as is; every ``function`` unit and every mutant of
one runs through ``drivers.make_drivers``. Each case is run under each llubi seed requested.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any

from . import ir
from .common import sha256

PAIR_ORIGINS = ["alive2-test", "opt", "mutation", "mutation-opt"]


def pair_id(src: str, tgt: str | None, src_fn: str, tgt_fn: str) -> str:
    return sha256("\x1f".join([src, tgt or "", src_fn, tgt_fn]))[:16]


def opt_target(module: str, pipeline: str, fn: str) -> tuple[str | None, str]:
    """Run the pipeline; returns (target module or None, status)."""
    r = ir.opt(["-S", f"-passes={pipeline}"], module, timeout=120)
    if r.exit != 0:
        return None, "opt-failed"
    out = ir.strip_header(r.stdout)
    if ir.function_body(out, fn) is None:
        return None, "function-removed"
    if out == ir.strip_header(module):
        return out, "identity"
    return out, "ok"


def make_pair(origin: str, src: str, tgt: str | None, src_fn: str, tgt_fn: str,
              parent: dict[str, Any], extra: dict[str, Any] | None = None) -> dict[str, Any]:
    row = {
        "id": pair_id(src, tgt, src_fn, tgt_fn),
        "origin": origin,
        "parent": parent,
        "src_fn": src_fn,
        "tgt_fn": tgt_fn,
        "single_file": tgt is None,
        "src": src,
        "tgt": tgt,
    }
    if extra:
        row.update(extra)
    return row


def store(rows: list[dict[str, Any]], d: Path) -> list[dict[str, Any]]:
    """Write pair texts to files and replace them by paths in the rows."""
    d.mkdir(parents=True, exist_ok=True)
    out = []
    for r in rows:
        r = dict(r)
        (d / f"{r['id']}.src.ll").write_text(r.pop("src"))
        r["src_path"] = f"{d.name}/{r['id']}.src.ll"
        tgt = r.pop("tgt")
        if tgt is not None:
            (d / f"{r['id']}.tgt.ll").write_text(tgt)
            r["tgt_path"] = f"{d.name}/{r['id']}.tgt.ll"
        else:
            r["tgt_path"] = None
        out.append(r)
    return out


def load_pair(root: Path, r: dict[str, Any]) -> tuple[str, str | None]:
    src = (root / r["src_path"]).read_text()
    tgt = (root / r["tgt_path"]).read_text() if r.get("tgt_path") else None
    return src, tgt


def lean_sides(src: str, tgt: str | None, src_fn: str, tgt_fn: str) -> tuple[str, str, str, str]:
    """(src module, src fn, tgt module, tgt fn) for the Lean side: single-file pairs use the
    same module for both sides."""
    return src, src_fn, (tgt if tgt is not None else src), tgt_fn

