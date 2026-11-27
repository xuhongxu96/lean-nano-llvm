"""Lightweight, LLVM-tool-backed utilities on textual LLVM IR.

Parsing and canonicalization are delegated to the pinned LLVM (`opt`, `llvm-extract`), so that
"valid IR" always means "accepted by the same LLVM the oracles are built from". The textual
helpers here only read IR that LLVM has already printed (one instruction per line, canonical
spacing), which keeps them simple and predictable.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field

from .common import Run, run, sha256, tool

DEFINE_RE = re.compile(r"^define\b[^@]*@(\"[^\"]+\"|[-\w.$]+)\s*\(", re.M)
DECLARE_RE = re.compile(r"^declare\b[^@]*@(\"[^\"]+\"|[-\w.$]+)\s*\(", re.M)
INSTR_RE = re.compile(r"^\s+(?:(%[-\w.$\"]+)\s*=\s*)?([a-z_]+)\b(.*)$")
INTRINSIC_RE = re.compile(r"@(llvm\.[\w.]+)")

FLOAT_TYPES = {"half", "bfloat", "float", "double", "fp128", "x86_fp80", "ppc_fp128"}

INT_BINOPS = ["add", "sub", "mul", "udiv", "sdiv", "urem", "srem", "shl", "lshr", "ashr", "and", "or", "xor"]
FP_BINOPS = ["fadd", "fsub", "fmul", "fdiv", "frem"]
MEMORY_OPS = {"load", "store", "alloca", "getelementptr", "atomicrmw", "cmpxchg", "fence"}
TERMINATORS = {"ret", "br", "switch", "indirectbr", "invoke", "callbr", "resume", "unreachable",
               "catchswitch", "catchret", "cleanupret"}


def opt(args: list[str], text: str, timeout: float = 60) -> Run:
    return run([tool("opt"), *args], stdin=text, timeout=timeout)


def verify(text: str) -> tuple[bool, str]:
    """Parse and verify with the pinned LLVM; returns (ok, canonical text or diagnostic)."""
    r = opt(["-S", "-passes=verify"], text)
    if r.exit == 0:
        return True, r.stdout
    return False, (r.stderr or "timeout").strip()


def strip_header(text: str) -> str:
    return "\n".join(
        l for l in text.splitlines() if not l.startswith("; ModuleID") and not l.startswith("source_filename")
    ).strip() + "\n"


def structural_hash(canonical: str) -> str:
    """Hash modulo alpha-renaming of locals, blocks, globals and functions.

    `metarenamer` renames every non-intrinsic symbol deterministically, so two units that differ
    only in names (very common across LLVM's tests) collide, which is what deduplication wants.
    Falls back to the plain canonical text if the pass is unavailable.
    """
    r = opt(["-S", "-passes=metarenamer,instnamer"], canonical)
    body = r.stdout if r.exit == 0 else canonical
    return sha256(strip_header(body))


def defined_functions(text: str) -> list[str]:
    return [m.group(1) for m in DEFINE_RE.finditer(text)]


def declared_functions(text: str) -> list[str]:
    return [m.group(1) for m in DECLARE_RE.finditer(text)]


def extract_function(module: str, name: str) -> Run:
    """`llvm-extract` one function with the globals and declarations it references."""
    fn = name.strip('"')
    return run([tool("llvm-extract"), "-S", f"--func={fn}", "-"], stdin=module, timeout=60)


def function_body(text: str, name: str) -> str | None:
    """The `define ... { ... }` text of one function in canonical IR."""
    m = re.search(r"^define\b[^\n]*@" + re.escape(name) + r"\s*\(", text, re.M)
    if not m:
        return None
    end = text.find("\n}", m.start())
    return text[m.start(): end + 2] if end >= 0 else None


# --------------------------------------------------------------------------------------------
# Types and signatures


def split_top(s: str, sep: str = ",") -> list[str]:
    """Split at `sep` outside (), [], {}, <> and quotes."""
    out, depth, cur, q = [], 0, [], False
    for ch in s:
        if ch == '"':
            q = not q
        if not q:
            if ch in "([{<":
                depth += 1
            elif ch in ")]}>":
                depth -= 1
            elif ch == sep and depth == 0:
                out.append("".join(cur).strip())
                cur = []
                continue
        cur.append(ch)
    if "".join(cur).strip():
        out.append("".join(cur).strip())
    return out


def take_type(s: str) -> tuple[str, str]:
    """Split a leading LLVM type off `s`; returns (type, rest)."""
    s = s.lstrip()
    if s[:1] in "<[{":
        close = {"<": ">", "[": "]", "{": "}"}
        depth, i = 0, 0
        # `<{ ... }>` packed structs nest two kinds; count all openers.
        for i, ch in enumerate(s):
            if ch in "<[{(":
                depth += 1
            elif ch in ">]})":
                depth -= 1
                if depth == 0:
                    break
        _ = close
        return s[: i + 1], s[i + 1:]
    m = re.match(r"(ptr(?:\s+addrspace\(\d+\))?|i\d+|b\d+|void|label|metadata|token|half|bfloat|float|double|fp128|x86_fp80|ppc_fp128|x86_amx|%[-\w.$\"]+)", s)
    if not m:
        return "", s
    return m.group(1), s[m.end():]


@dataclass
class Param:
    ty: str
    attrs: str
    name: str


@dataclass
class Signature:
    name: str
    ret: str
    params: list[Param]
    varargs: bool
    header: str


def signature(define_line: str) -> Signature | None:
    m = re.match(r"^define\b(.*?)@(\"[^\"]+\"|[-\w.$]+)\s*\((.*)$", define_line)
    if not m:
        return None
    pre, name, rest = m.groups()
    # Return type is the last type-looking token of the prefix (after linkage/attrs).
    pre_tokens = pre.split()
    ret = ""
    for i in range(len(pre_tokens)):
        t, _ = take_type(" ".join(pre_tokens[i:]))
        if t:
            ret = t
            break
    depth, j = 1, 0
    for j, ch in enumerate(rest):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                break
    plist = rest[:j]
    params, varargs = [], False
    for p in split_top(plist):
        if p == "...":
            varargs = True
            continue
        ty, tail = take_type(p)
        nm = re.search(r"(%[-\w.$\"]+)\s*$", tail)
        params.append(Param(ty=ty, attrs=tail[: nm.start()].strip() if nm else tail.strip(),
                            name=nm.group(1) if nm else ""))
    return Signature(name=name, ret=ret, params=params, varargs=varargs, header=define_line)


def signature_of(text: str, name: str) -> Signature | None:
    body = function_body(text, name)
    return signature(body.splitlines()[0]) if body else None


# --------------------------------------------------------------------------------------------
# Features (for stratified reporting)


@dataclass
class Features:
    opcodes: dict[str, int] = field(default_factory=dict)
    intrinsics: list[str] = field(default_factory=list)
    int_widths: list[int] = field(default_factory=list)
    has_float: bool = False
    has_vector: bool = False
    has_scalable: bool = False
    has_ptr: bool = False
    has_memory: bool = False
    has_calls: bool = False
    has_undef: bool = False
    has_poison: bool = False
    blocks: int = 0  # maximum over the module's function definitions
    instructions: int = 0  # total over the module's function definitions

    def categories(self) -> list[str]:
        """Coarse, mutually non-exclusive feature classes used in the paper's breakdown tables."""
        c = []
        if any(o in self.opcodes for o in INT_BINOPS + ["icmp", "select", "trunc", "zext", "sext"]):
            c.append("integer")
        if self.has_float:
            c.append("float")
        if self.has_vector:
            c.append("vector")
        if self.has_memory:
            c.append("memory")
        if self.blocks > 1:
            c.append("control-flow")
        if self.intrinsics:
            c.append("intrinsic")
        if self.has_undef:
            c.append("undef")
        if self.has_poison:
            c.append("poison")
        return c or ["other"]


def features(text: str) -> Features:
    f = Features()
    in_fn = False
    cur_blocks = 0
    for line in text.splitlines():
        if line.startswith("define"):
            in_fn = True
            cur_blocks = 1  # the entry block, which canonical IR prints without a label
            continue
        if line.startswith("}"):
            in_fn = False
            f.blocks = max(f.blocks, cur_blocks)
            continue
        if not in_fn:
            continue
        if re.match(r"^[-\w.$\"]+:", line):
            cur_blocks += 1
            continue
        m = INSTR_RE.match(line)
        if not m:
            continue
        op = m.group(2)
        if op in ("tail", "musttail", "notail"):
            op = "call"
        f.instructions += 1
        f.opcodes[op] = f.opcodes.get(op, 0) + 1
        if op in MEMORY_OPS:
            f.has_memory = True
        if op in ("call", "invoke", "callbr"):
            intr = INTRINSIC_RE.findall(line)
            if intr:
                f.intrinsics.extend(intr)
            else:
                f.has_calls = True
        if "undef" in re.findall(r"\bundef\b", line):
            f.has_undef = True
        if re.search(r"\bpoison\b", line):
            f.has_poison = True
    # Type-level features come from the whole text.
    f.int_widths = sorted({int(w) for w in re.findall(r"\bi(\d+)\b", text)})
    f.has_float = any(re.search(r"\b" + t + r"\b", text) for t in FLOAT_TYPES)
    f.has_vector = bool(re.search(r"<\s*(vscale\s+x\s+)?\d+\s+x\s", text))
    f.has_scalable = "vscale x" in text
    f.has_ptr = bool(re.search(r"\bptr\b", text))
    f.intrinsics = sorted(set(f.intrinsics))
    return f
