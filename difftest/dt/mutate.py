"""Seeded, enumerable mutation of LLVM IR functions.

Design (stated so it can be reported as is):

1. A mutation *site* is a triple (operator, line, choice). For a given function text, the
   function ``sites()`` enumerates all sites in a fixed order (line order, then operator order,
   then choice order). It works on canonical IR printed by the pinned LLVM, one instruction per
   line.
2. The mutants of a unit are drawn from that list without replacement, using
   ``random.Random(derive_seed(global_seed, unit_id, "mutate", order))``. A higher-order mutant
   (``order > 1``) applies ``order`` sites in sequence, re-enumerating after each step. The same
   (seed, unit, order, count) therefore always yields the same mutants, whatever else is in the
   corpus.
3. Each mutant is re-verified by the pinned LLVM (``opt -passes=verify``). Mutants that fail
   verification, that print identically to their parent, or that duplicate an earlier mutant of
   the same parent (by text hash) are recorded with that outcome and not used further.

Operators (``OPERATORS``) are restricted to local, type-preserving edits. They model the edits
peephole optimizations make (opcode, predicate, constant and operand changes) and the
poison-generating annotations whose semantics are most often subtle (flags, ``poison``,
``undef``, ``freeze``).
"""

from __future__ import annotations

import random
import re
from dataclasses import dataclass
from typing import Callable, Iterator

from . import ir
from .common import derive_seed, sha256

TY = r"(?:i\d+|<(?:vscale x )?\d+ x i\d+>)"
FTY = r"(?:half|bfloat|float|double|fp128|x86_fp80|ppc_fp128|<(?:vscale x )?\d+ x (?:half|bfloat|float|double)>)"
ANYTY = r"(?:i\d+|ptr|half|bfloat|float|double|fp128|x86_fp80|ppc_fp128|<(?:vscale x )?\d+ x [^>]+>)"
VAL = r"(?:%[-\w.$]+|-?\d+|true|false|poison|undef|null|zeroinitializer|splat \([^()]*\)|<[^<>]*>|0x[0-9A-Fa-f]+|-?\d+\.\d+(?:e[-+]?\d+)?)"
LOCAL = re.compile(r"%[-\w.$]+")

INT_FLAGS = {
    "add": ["nuw", "nsw"], "sub": ["nuw", "nsw"], "mul": ["nuw", "nsw"], "shl": ["nuw", "nsw"],
    "udiv": ["exact"], "sdiv": ["exact"], "lshr": ["exact"], "ashr": ["exact"], "or": ["disjoint"],
}
CAST_FLAGS = {"trunc": ["nuw", "nsw"], "zext": ["nneg"], "uitofp": ["nneg"]}
FMF = ["nnan", "ninf", "nsz"]
ICMP_PREDS = ["eq", "ne", "ugt", "uge", "ult", "ule", "sgt", "sge", "slt", "sle"]
FCMP_PREDS = ["oeq", "ogt", "oge", "olt", "ole", "one", "ord", "ueq", "ugt", "uge", "ult", "ule",
              "une", "uno", "true", "false"]
COMMUTATIVE = {"add", "mul", "and", "or", "xor", "fadd", "fmul"}

BINOP_RE = re.compile(
    rf"^(?P<ind>\s+)(?P<res>%[-\w.$]+) = (?P<op>{'|'.join(ir.INT_BINOPS)})(?P<flags>(?: (?:nuw|nsw|exact|disjoint))*)"
    rf" (?P<ty>{TY}) (?P<a>{VAL}), (?P<b>{VAL})(?P<rest>.*)$"
)
FBINOP_RE = re.compile(
    rf"^(?P<ind>\s+)(?P<res>%[-\w.$]+) = (?P<op>{'|'.join(ir.FP_BINOPS)})(?P<flags>(?: (?:nnan|ninf|nsz|arcp|contract|afn|reassoc|fast))*)"
    rf" (?P<ty>{FTY}) (?P<a>{VAL}), (?P<b>{VAL})(?P<rest>.*)$"
)
ICMP_RE = re.compile(
    rf"^(?P<ind>\s+)(?P<res>%[-\w.$]+) = icmp(?P<flags>(?: samesign)?) (?P<pred>{'|'.join(ICMP_PREDS)})"
    rf" (?P<ty>{TY}|ptr) (?P<a>{VAL}), (?P<b>{VAL})(?P<rest>.*)$"
)
FCMP_RE = re.compile(
    rf"^(?P<ind>\s+)(?P<res>%[-\w.$]+) = fcmp(?P<flags>(?: (?:nnan|ninf|nsz|arcp|contract|afn|reassoc|fast))*) (?P<pred>{'|'.join(FCMP_PREDS)})"
    rf" (?P<ty>{FTY}) (?P<a>{VAL}), (?P<b>{VAL})(?P<rest>.*)$"
)
CAST_RE = re.compile(
    rf"^(?P<ind>\s+)(?P<res>%[-\w.$]+) = (?P<op>trunc|zext|sext|uitofp|sitofp|fptoui|fptosi|fpext|fptrunc|bitcast|ptrtoint|inttoptr)"
    rf"(?P<flags>(?: (?:nuw|nsw|nneg))*) (?P<sty>{ANYTY}) (?P<a>{VAL}) to (?P<dty>{ANYTY})(?P<rest>.*)$"
)
SELECT_RE = re.compile(
    rf"^(?P<ind>\s+)(?P<res>%[-\w.$]+) = select(?P<flags>(?: (?:nnan|ninf|nsz|arcp|contract|afn|reassoc|fast))*)"
    rf" (?P<cty>i1|<(?:vscale x )?\d+ x i1>) (?P<c>{VAL}), (?P<ty>{ANYTY}) (?P<a>{VAL}), (?P=ty) (?P<b>{VAL})(?P<rest>.*)$"
)
FREEZE_RE = re.compile(rf"^(?P<ind>\s+)(?P<res>%[-\w.$]+) = freeze (?P<ty>{ANYTY}) (?P<a>{VAL})(?P<rest>.*)$")
CONDBR_RE = re.compile(r"^(?P<ind>\s+)br i1 (?P<c>%[-\w.$]+|true|false), label (?P<t>%[-\w.$]+), label (?P<f>%[-\w.$]+)(?P<rest>.*)$")
LABEL_RE = re.compile(r"^([-\w.$]+):")


@dataclass(frozen=True)
class Site:
    operator: str
    line: int
    choice: str


@dataclass
class FunctionView:
    """The lines of one function and the SSA values (with types) usable at each line."""
    lines: list[str]
    start: int  # index of the `define` line
    end: int  # index of the closing `}`
    defs: dict[int, tuple[str, str]]  # line -> (value, type)
    block_of: dict[int, int]  # line -> block index (0 = entry)
    params: list[tuple[str, str]]


def view(text: str, fn: str | None) -> FunctionView | None:
    lines = text.split("\n")
    start = None
    for i, l in enumerate(lines):
        if l.startswith("define") and (fn is None or re.search(r"@" + re.escape(fn) + r"\s*\(", l)):
            start = i
            break
    if start is None:
        return None
    end = next((j for j in range(start, len(lines)) if lines[j].startswith("}")), len(lines) - 1)
    sig = ir.signature(lines[start])
    params = [(p.name, p.ty) for p in (sig.params if sig else []) if p.name]
    defs: dict[int, tuple[str, str]] = {}
    block_of: dict[int, int] = {}
    blk = 0
    for i in range(start + 1, end):
        l = lines[i]
        if LABEL_RE.match(l):
            blk += 1
            continue
        block_of[i] = blk
        for rx, tykey in ((BINOP_RE, "ty"), (FBINOP_RE, "ty"), (CAST_RE, "dty"), (SELECT_RE, "ty"), (FREEZE_RE, "ty")):
            m = rx.match(l)
            if m:
                defs[i] = (m.group("res"), m.group(tykey))
                break
        else:
            m = ICMP_RE.match(l) or FCMP_RE.match(l)
            if m:
                ty = m.group("ty")
                vm = re.match(r"<((?:vscale x )?\d+) x ", ty)
                defs[i] = (m.group("res"), f"<{vm.group(1)} x i1>" if vm else "i1")
    return FunctionView(lines, start, end, defs, block_of, params)


def available(v: FunctionView, line: int, ty: str) -> list[str]:
    """Values of type `ty` that dominate `line`: parameters, earlier values of the entry
    block, and earlier values of the same block."""
    out = [n for n, t in v.params if t == ty]
    b = v.block_of.get(line)
    for i, (n, t) in sorted(v.defs.items()):
        if i >= line or t != ty:
            continue
        if v.block_of.get(i) == 0 or v.block_of.get(i) == b:
            out.append(n)
    return out


def int_width(ty: str) -> int | None:
    m = re.search(r"i(\d+)>?$", ty)
    return int(m.group(1)) if m else None


def const_choices(c: int, w: int) -> list[int]:
    smin, smax = -(1 << (w - 1)), (1 << (w - 1)) - 1
    cands = [0, 1, -1, c + 1, c - 1, -c, ~c, smin, smax]
    if w > 1:
        cands.append(w - 1)
    out = []
    for x in cands:
        # Wrap to the signed range of the width, as LLVM prints constants.
        x = ((x - smin) % (1 << w)) + smin if w > 0 else 0
        if x != c and x not in out:
            out.append(x)
    return out


def fmt_const(x: int, w: int) -> str:
    if w == 1:
        return "true" if x & 1 else "false"
    return str(x)


# --------------------------------------------------------------------------------------------
# Operators: each maps (view, line index, match) to a list of (choice, new line(s)).

Edit = tuple[str, list[str]]


def _flags(m: re.Match) -> list[str]:
    return m.group("flags").split()


def _with_flags(base: str, flags: list[str]) -> str:
    return base + "".join(" " + f for f in flags)


def op_binop_replace(v, i, l) -> list[Edit]:
    m = BINOP_RE.match(l)
    if m:
        out = []
        for op in ir.INT_BINOPS:
            if op == m.group("op"):
                continue
            keep = [f for f in _flags(m) if f in INT_FLAGS.get(op, [])]
            out.append((op, [f"{m['ind']}{m['res']} = {_with_flags(op, keep)} {m['ty']} {m['a']}, {m['b']}{m['rest']}"]))
        return out
    m = FBINOP_RE.match(l)
    if m:
        return [(op, [f"{m['ind']}{m['res']} = {op}{m['flags']} {m['ty']} {m['a']}, {m['b']}{m['rest']}"])
                for op in ir.FP_BINOPS if op != m.group("op")]
    return []


def op_flag_toggle(v, i, l) -> list[Edit]:
    out = []
    for rx, table in ((BINOP_RE, INT_FLAGS), (CAST_RE, CAST_FLAGS)):
        m = rx.match(l)
        if not m:
            continue
        allowed = table.get(m.group("op"), [])
        cur = _flags(m)
        for f in allowed:
            new = [x for x in cur if x != f] if f in cur else cur + [f]
            new = [x for x in allowed if x in new]  # canonical order
            head = l[: m.start("flags")] + "".join(" " + x for x in new) + l[m.end("flags"):]
            out.append((("drop-" if f in cur else "add-") + f, [head]))
    m = ICMP_RE.match(l)
    if m:
        cur = "samesign" in _flags(m)
        new = l[: m.start("flags")] + ("" if cur else " samesign") + l[m.end("flags"):]
        out.append((("drop-" if cur else "add-") + "samesign", [new]))
    for rx in (FBINOP_RE, FCMP_RE, SELECT_RE):
        m = rx.match(l)
        if m and (rx is not SELECT_RE or re.match(FTY, m.group("ty"))):
            cur = _flags(m)
            for f in FMF:
                new = [x for x in cur if x != f] if f in cur else cur + [f]
                out.append((("drop-" if f in cur else "add-") + f,
                            [l[: m.start("flags")] + "".join(" " + x for x in new) + l[m.end("flags"):]]))
    return out


def op_pred_replace(v, i, l) -> list[Edit]:
    for rx, preds in ((ICMP_RE, ICMP_PREDS), (FCMP_RE, FCMP_PREDS)):
        m = rx.match(l)
        if m:
            return [(p, [l[: m.start("pred")] + p + l[m.end("pred"):]]) for p in preds if p != m.group("pred")]
    return []


def op_const_replace(v, i, l) -> list[Edit]:
    out = []
    for rx in (BINOP_RE, ICMP_RE, SELECT_RE):
        m = rx.match(l)
        if not m:
            continue
        w = int_width(m.group("ty"))
        if w is None or m.group("ty").startswith("<"):
            continue
        for g in ("a", "b"):
            tok = m.group(g)
            if tok in ("true", "false"):
                c = 1 if tok == "true" else 0
            elif re.fullmatch(r"-?\d+", tok):
                c = int(tok)
            else:
                continue
            for x in const_choices(c, w):
                out.append((f"{g}:{fmt_const(x, w)}", [l[: m.start(g)] + fmt_const(x, w) + l[m.end(g):]]))
    return out


def op_operand_swap(v, i, l) -> list[Edit]:
    for rx in (BINOP_RE, FBINOP_RE, ICMP_RE, FCMP_RE, SELECT_RE):
        m = rx.match(l)
        if m and m.group("a") != m.group("b"):
            return [("swap", [l[: m.start("a")] + m.group("b") + l[m.end("a"): m.start("b")] + m.group("a") + l[m.end("b"):]])]
    m = CONDBR_RE.match(l)
    if m:
        return [("swap-successors", [f"{m['ind']}br i1 {m['c']}, label {m['f']}, label {m['t']}{m['rest']}"])]
    return []


def op_operand_replace(v, i, l) -> list[Edit]:
    out = []
    for rx in (BINOP_RE, FBINOP_RE, ICMP_RE, FCMP_RE, SELECT_RE, FREEZE_RE, CAST_RE):
        m = rx.match(l)
        if not m:
            continue
        ty = m.group("sty") if rx is CAST_RE else m.group("ty")
        for g in ("a", "b"):
            if g not in m.groupdict() or m.group(g) is None:
                continue
            for cand in available(v, i, ty):
                if cand != m.group(g) and cand != m.group("res"):
                    out.append((f"{g}:{cand}", [l[: m.start(g)] + cand + l[m.end(g):]]))
        break
    return out


def _value_inject(v, i, l, what: str) -> list[Edit]:
    out = []
    for rx in (BINOP_RE, FBINOP_RE, ICMP_RE, FCMP_RE, SELECT_RE, CAST_RE):
        m = rx.match(l)
        if not m:
            continue
        for g in ("a", "b", "c"):
            if g in m.groupdict() and m.group(g) not in (None, what):
                out.append((g, [l[: m.start(g)] + what + l[m.end(g):]]))
        break
    return out


def op_poison_inject(v, i, l) -> list[Edit]:
    return _value_inject(v, i, l, "poison")


def op_undef_inject(v, i, l) -> list[Edit]:
    return _value_inject(v, i, l, "undef")


def op_freeze_insert(v, i, l) -> list[Edit]:
    out = []
    for rx in (BINOP_RE, FBINOP_RE, ICMP_RE, FCMP_RE, SELECT_RE, CAST_RE):
        m = rx.match(l)
        if not m:
            continue
        for g in ("a", "b", "c"):
            if g not in m.groupdict() or m.group(g) is None or not m.group(g).startswith("%"):
                continue
            ty = m.group("cty") if g == "c" else (m.group("sty") if rx is CAST_RE else m.group("ty"))
            fr = f"%dt.fr{i}{g}"
            out.append((g, [f"{m['ind']}{fr} = freeze {ty} {m.group(g)}",
                            l[: m.start(g)] + fr + l[m.end(g):]]))
        break
    return out


def op_cast_replace(v, i, l) -> list[Edit]:
    m = CAST_RE.match(l)
    if not m:
        return []
    alt = {"zext": ["sext"], "sext": ["zext"], "uitofp": ["sitofp"], "sitofp": ["uitofp"],
           "fptoui": ["fptosi"], "fptosi": ["fptoui"]}.get(m.group("op"), [])
    return [(op, [f"{m['ind']}{m['res']} = {_with_flags(op, [f for f in _flags(m) if f in CAST_FLAGS.get(op, [])])}"
                  f" {m['sty']} {m['a']} to {m['dty']}{m['rest']}"]) for op in alt]


def op_instr_delete(v, i, l) -> list[Edit]:
    """Delete a value-producing instruction, replacing its uses with one of its operands of
    the same type (``x op y`` becomes ``x``)."""
    for rx in (BINOP_RE, FBINOP_RE, SELECT_RE, FREEZE_RE):
        m = rx.match(l)
        if not m:
            continue
        out = []
        for g in ("a", "b"):
            if g in m.groupdict() and m.group(g) is not None:
                out.append((f"use-{g}", ["<<delete>>", m.group("res"), m.group(g)]))
        return out
    return []


OPERATORS: dict[str, Callable[[FunctionView, int, str], list[Edit]]] = {
    "binop-replace": op_binop_replace,
    "flag-toggle": op_flag_toggle,
    "pred-replace": op_pred_replace,
    "const-replace": op_const_replace,
    "operand-swap": op_operand_swap,
    "operand-replace": op_operand_replace,
    "poison-inject": op_poison_inject,
    "undef-inject": op_undef_inject,
    "freeze-insert": op_freeze_insert,
    "cast-replace": op_cast_replace,
    "instr-delete": op_instr_delete,
}


def sites(text: str, fn: str | None, operators: list[str]) -> Iterator[tuple[Site, list[str]]]:
    v = view(text, fn)
    if v is None:
        return
    for i in range(v.start + 1, v.end):
        l = v.lines[i]
        if LABEL_RE.match(l) or not l.strip() or l.lstrip().startswith(";"):
            continue
        for name in operators:
            for choice, new in OPERATORS[name](v, i, l):
                yield Site(name, i, choice), new


def apply(text: str, site: Site, new: list[str]) -> str:
    lines = text.split("\n")
    if new and new[0] == "<<delete>>":
        _, res, repl = new
        end = next(j for j in range(site.line, len(lines)) if lines[j].startswith("}"))
        pat = re.compile(re.escape(res) + r"(?![-\w.$])")
        for j in range(site.line + 1, end):
            lines[j] = pat.sub(repl, lines[j])
        del lines[site.line]
        return "\n".join(lines)
    return "\n".join(lines[: site.line] + new + lines[site.line + 1:])


@dataclass
class Mutant:
    parent: str
    index: int
    order: int
    seed: int
    sites: list[dict]
    status: str  # ok | invalid | noop | duplicate
    text: str | None
    detail: str = ""


def mutate_unit(
    unit_id: str,
    text: str,
    fn: str | None,
    *,
    global_seed: int,
    count: int,
    order: int = 1,
    operators: list[str] | None = None,
) -> list[Mutant]:
    """Draw `count` mutants of function `fn` of `text` (see the module docstring)."""
    ops = operators or list(OPERATORS)
    seed = derive_seed(global_seed, unit_id, "mutate", order)
    rng = random.Random(seed)
    base_hash = sha256(ir.strip_header(text))
    seen: set[str] = {base_hash}
    out: list[Mutant] = []
    first = list(sites(text, fn, ops))
    rng.shuffle(first)
    pool = first
    for k in range(min(count, len(first))):
        cur, applied = text, []
        site, new = pool[k]
        for step in range(order):
            if step > 0:
                more = list(sites(cur, fn, ops))
                if not more:
                    break
                site, new = more[rng.randrange(len(more))]
            applied.append({"operator": site.operator, "line": site.line, "choice": site.choice,
                            "before": cur.split("\n")[site.line].strip(),
                            "after": "\n".join(x.strip() for x in new if not x.startswith("<<"))})
            cur = apply(cur, site, new)
        ok, canon = ir.verify(cur)
        m = Mutant(unit_id, k, order, seed, applied, "ok", None)
        if not ok:
            m.status, m.detail = "invalid", canon.splitlines()[0] if canon else ""
        else:
            h = sha256(ir.strip_header(canon))
            if h == base_hash:
                m.status = "noop"
            elif h in seen:
                m.status = "duplicate"
            else:
                seen.add(h)
                m.text = ir.strip_header(canon)
        out.append(m)
    return out
