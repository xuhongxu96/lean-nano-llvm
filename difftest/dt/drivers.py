"""Execution drivers: make a function with parameters executable by llubi.

llubi only executes an entry function with no parameters or with ``main``'s signature (it
passes null for any other parameter list). For each function unit we therefore synthesize, per
argument vector, a module that appends a parameterless entry ``@__dt_main`` calling the function
under test with constant arguments. Both interpreters run that entry with ``--verbose``, whose
trace prints the call's result.

Argument generation (``ArgGen``), per parameter type:

* ``iN``: drawn from the boundary set {0, 1, -1, 2, INT_MIN, INT_MIN+1, INT_MAX, INT_MAX-1}
  with probability ``p_boundary``, otherwise uniformly from [0, 2^N), printed as signed.
  ``i1`` is ``true``/``false``.
* floating point: drawn from {+0, -0, 1, -1, +inf, -inf, qNaN, smallest subnormal, largest
  finite} with probability ``p_boundary``, otherwise a uniformly random bit pattern, printed in
  LLVM's hexadecimal form (``0x``, ``0xH``, ``0xR``).
* fixed vectors: element-wise as above.
* ``ptr``: a fresh 64-byte, 16-aligned ``alloca`` in the driver, filled with ``memset`` to a
  random byte. Only address space 0 is supported.
* any scalar or vector argument is ``poison`` with probability ``p_poison``, except parameters
  marked ``noundef`` (passing poison there is immediate UB, which would mask the body).

Unsupported parameter kinds (aggregates, scalable vectors, ``byval``/``sret``/``inalloca``/
``preallocated``, non-zero address spaces, x86_fp80/fp128/ppc_fp128, varargs) make the unit
non-executable; this is recorded, not silently skipped.
"""

from __future__ import annotations

import random
import re
import struct
from dataclasses import dataclass

from . import ir
from .common import derive_seed

FP_BITS = {"half": 16, "bfloat": 16, "float": 32, "double": 64}
UNSUPPORTED_ATTRS = ("byval", "sret", "inalloca", "preallocated", "byref", "swifterror", "swiftself")
# Size bounds on generated constants (larger arguments occur only in LLVM's stress tests of
# type limits, e.g. i8388608 or <4294967295 x i8>).
MAX_INT_BITS = 4096
MAX_VECTOR_LANES = 1024
MEMSET = "declare void @llvm.memset.p0.i64(ptr writeonly, i8, i64, i1 immarg)"


class Unsupported(Exception):
    pass


def _fp_special(ty: str) -> list[int]:
    w = FP_BITS[ty]
    if ty == "half":
        return [0x0000, 0x8000, 0x3C00, 0xBC00, 0x7C00, 0xFC00, 0x7E00, 0x0001, 0x7BFF]
    if ty == "bfloat":
        return [0x0000, 0x8000, 0x3F80, 0xBF80, 0x7F80, 0xFF80, 0x7FC0, 0x0001, 0x7F7F]
    if w == 32:
        return [0x00000000, 0x80000000, 0x3F800000, 0xBF800000, 0x7F800000, 0xFF800000,
                0x7FC00000, 0x00000001, 0x7F7FFFFF]
    return [0x0, 0x8000000000000000, 0x3FF0000000000000, 0xBFF0000000000000, 0x7FF0000000000000,
            0xFFF0000000000000, 0x7FF8000000000000, 0x1, 0x7FEFFFFFFFFFFFFF]


def fp_literal(ty: str, bits: int) -> str:
    if ty == "half":
        return f"0xH{bits:04X}"
    if ty == "bfloat":
        return f"0xR{bits:04X}"
    if ty == "double":
        return f"0x{bits:016X}"
    # float constants are written as the double with the same value (exact by construction).
    f = struct.unpack("<f", struct.pack("<I", bits))[0]
    if f != f:  # NaN: widen the payload exactly as LLVM does (sign, quiet bit, payload << 29)
        sign = bits >> 31
        payload = bits & 0x7FFFFF
        d = (sign << 63) | (0x7FF << 52) | (payload << 29)
        return f"0x{d:016X}"
    return f"0x{struct.unpack('<Q', struct.pack('<d', f))[0]:016X}"


@dataclass
class ArgGen:
    p_poison: float = 0.05
    p_boundary: float = 0.5

    def scalar(self, rng: random.Random, ty: str, noundef: bool) -> str:
        if not noundef and rng.random() < self.p_poison:
            return "poison"
        m = re.fullmatch(r"i(\d+)", ty)
        if m:
            w = int(m.group(1))
            if w > MAX_INT_BITS:
                raise Unsupported(f"argument type {ty} wider than {MAX_INT_BITS} bits")
            if w == 1:
                return rng.choice(["true", "false"])
            smin, smax = -(1 << (w - 1)), (1 << (w - 1)) - 1
            if rng.random() < self.p_boundary:
                return str(rng.choice([0, 1, -1, 2, smin, smin + 1, smax, smax - 1]))
            x = rng.getrandbits(w)
            return str(x - (1 << w) if x > smax else x)
        if ty in FP_BITS:
            bits = rng.choice(_fp_special(ty)) if rng.random() < self.p_boundary else rng.getrandbits(FP_BITS[ty])
            return fp_literal(ty, bits)
        raise Unsupported(f"argument type {ty}")

    def value(self, rng: random.Random, ty: str, noundef: bool) -> str:
        m = re.fullmatch(r"<(\d+) x (.+)>", ty)
        if m:
            n, et = int(m.group(1)), m.group(2)
            if n > MAX_VECTOR_LANES:
                raise Unsupported(f"vector argument with {n} lanes")
            return "<" + ", ".join(f"{et} {self.scalar(rng, et, noundef)}" for _ in range(n)) + ">"
        if ty.startswith("<vscale"):
            raise Unsupported("scalable vector argument")
        return self.scalar(rng, ty, noundef)


@dataclass
class Driver:
    module: str
    args: list[str]  # the typed argument list of the call, for the record
    seed: int


def make_drivers(unit_id: str, text: str, fn: str, count: int, global_seed: int,
                 gen: ArgGen | None = None) -> list[Driver]:
    gen = gen or ArgGen()
    sig = ir.signature_of(text, fn)
    if sig is None:
        raise Unsupported("no definition")
    if sig.varargs:
        raise Unsupported("varargs function")
    for p in sig.params:
        if any(a in p.attrs for a in UNSUPPORTED_ATTRS):
            raise Unsupported(f"parameter attribute in '{p.attrs}'")
        if p.ty.startswith(("[", "{", "%", "<{")) or "addrspace" in p.ty or p.ty in ("x86_fp80", "fp128", "ppc_fp128"):
            raise Unsupported(f"argument type {p.ty}")
    has_memset = "@llvm.memset.p0.i64(" in text
    out = []
    for k in range(count):
        seed = derive_seed(global_seed, unit_id, "args", k)
        rng = random.Random(seed)
        body, args = [], []
        for j, p in enumerate(sig.params):
            if p.ty == "ptr":
                body.append(f"  %dt.p{j} = alloca [64 x i8], align 16")
                body.append(f"  call void @llvm.memset.p0.i64(ptr %dt.p{j}, i8 {rng.getrandbits(8) - 128}, i64 64, i1 false)")
                args.append(f"ptr %dt.p{j}")
            else:
                args.append(f"{p.ty} {gen.value(rng, p.ty, 'noundef' in p.attrs)}")
        call = f"call {sig.ret} @{fn}({', '.join(args)})"
        body.append(f"  {call}" if sig.ret == "void" else f"  %dt.r = {call}")
        body.append("  ret i32 0")
        mod = text.rstrip() + "\n\ndefine i32 @__dt_main() {\n" + "\n".join(body) + "\n}\n"
        if not has_memset and any(p.ty == "ptr" for p in sig.params):
            mod += "\n" + MEMSET + "\n"
        out.append(Driver(module=mod, args=args, seed=seed))
    return out
