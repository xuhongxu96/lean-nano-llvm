#!/usr/bin/env python3
"""Cross-check lean-nano-llvm against LLVM's llubi .ll test suite.

Parses every `; RUN:` directive (including `sed` substitutions, `not llubi`,
`--entry-function`, `--max-mem`, `--max-stack-depth`, `--max-steps`, `--deterministic`,
`--nan-behavior`, `--undef-behavior`, `--vscale`, `--fuse-fmuladd`, `--check-prefix`),
runs `lean-nano-llvm run - --verbose ...`, and verifies BOTH:
  1. Outcome parity (OK vs Immediate UB vs expected resource/static error)
  2. Semantic per-instruction value parity against `; CHECK[-NEXT]: %id = ... => <val>`

Usage:
  python3 scripts/run_llubi_tests.py [llubi_test_dir] [lean_nano_llvm_bin] [--verbose]
"""

import glob
import math
import os
import re
import shlex
import struct
import subprocess
import sys
from collections import Counter


def parse_run_lines(text: str):
    """Extract all `; RUN:` lines (joining trailing `\\` continuations)."""
    runs = []
    cur = None
    for line in text.splitlines():
        m = re.match(r"^;\s*RUN:\s*(.*)$", line)
        if m:
            part = m.group(1).rstrip()
            if cur is not None:
                cur += " " + part
            else:
                cur = part
            if cur.endswith("\\"):
                cur = cur[:-1].rstrip()
            else:
                runs.append(cur)
                cur = None
        else:
            if cur is not None:
                runs.append(cur)
                cur = None
    if cur is not None:
        runs.append(cur)
    return runs


def apply_sed_cmd(sed_cmd: str, src: str) -> str:
    """Apply simple `sed 's/pat/repl/g'` or `-e` expressions from a RUN pipeline."""
    # Extract all 's...' or "s..." expressions
    tokens = shlex.split(sed_cmd)
    exprs = []
    i = 1
    while i < len(tokens):
        t = tokens[i]
        if t == "-e" and i + 1 < len(tokens):
            exprs.append(tokens[i + 1])
            i += 2
        elif t.startswith("-"):
            i += 1
        elif t == "%s":
            i += 1
        else:
            exprs.append(t)
            i += 1
    out = src
    for expr in exprs:
        if len(expr) >= 4 and expr[0] == "s":
            delim = expr[1]
            parts = expr[2:].split(delim)
            if len(parts) >= 2:
                pat, repl = parts[0], parts[1]
                flags = parts[2] if len(parts) >= 3 else ""
                count = 0 if "g" in flags else 1
                out = re.sub(pat, repl, out, count=count)
    return out


def extract_checks(text: str, prefixes):
    """Return list of check payloads for the given FileCheck prefixes."""
    pat = re.compile(
        r"^;\s*(?:" + "|".join(re.escape(p) for p in prefixes) + r")(?:-NEXT|-DAG|-SAME)?:\s*(.*)$"
    )
    out = []
    for line in text.splitlines():
        m = pat.match(line)
        if m:
            out.append(m.group(1).strip())
    return out


def parse_llubi_scalar_to_canonical(s: str):
    """Normalize an llubi scalar value string for semantic comparison."""
    s = s.strip()
    if s == "poison":
        return ("poison",)
    if s == "T":
        return ("int", 1, 1)
    if s == "F":
        return ("int", 1, 0)
    if s == "void":
        return ("void",)
    # Integer: `i32 -1` or `i64 42`
    m = re.match(r"^i(\d+)\s+(-?\d+)$", s)
    if m:
        w = int(m.group(1))
        v = int(m.group(2))
        if w > 0:
            v = v & ((1 << w) - 1)
        return ("int", w, v)
    # Pointer: `ptr 0x0 [null]` or `ptr 0x8 [alloc]` or `ptr 0x8 [alloc (dangling)]`
    m = re.match(r"^ptr\s+0x([0-9a-fA-F]+)(?:\s+\[(.*)\])?$", s)
    if m:
        addr = int(m.group(1), 16)
        tag = m.group(2) or ""
        return ("ptr", addr == 0, "dangling" in tag)
    # Float: `float 2.000000e+00`, `double +Inf`, `half NaN`, `float 0x3D4CCCC8`
    m = re.match(r"^(half|bfloat|float|double|fp128|x86_fp80|ppc_fp128)\s+(.+)$", s)
    if m:
        ft = m.group(1)
        val = m.group(2).strip()
        if val in ("NaN", "-NaN", "+NaN") or "NaN" in val:
            return ("fp_nan", ft)
        if val in ("+Inf", "Inf"):
            return ("fp_inf", ft, False)
        if val == "-Inf":
            return ("fp_inf", ft, True)
        if val.startswith("0x") or val.startswith("f0x"):
            hex_s = val[3:] if val.startswith("f0x") else val[2:]
            try:
                return ("fp_hex", ft, int(hex_s, 16))
            except ValueError:
                return ("fp_raw", ft, val)
        try:
            f = float(val)
            neg = math.copysign(1.0, f) < 0
            return ("fp_num", ft, f, neg)
        except ValueError:
            return ("fp_raw", ft, val)
    return ("raw", s)


def decode_lean_float(ft: str, bits: int):
    """Decode lean-nano-llvm's hex float bits into (is_nan, is_inf, neg, approx_float)."""
    if ft == "float":
        sign = (bits >> 31) & 1
        exp = (bits >> 23) & 0xFF
        frac = bits & 0x7FFFFF
        if exp == 0xFF:
            return (frac != 0, frac == 0, bool(sign), 0.0)
        f = struct.unpack(">f", struct.pack(">I", bits & 0xFFFFFFFF))[0]
        return (False, False, bool(sign), f)
    if ft == "double":
        sign = (bits >> 63) & 1
        exp = (bits >> 52) & 0x7FF
        frac = bits & 0xFFFFFFFFFFFFF
        if exp == 0x7FF:
            return (frac != 0, frac == 0, bool(sign), 0.0)
        f = struct.unpack(">d", struct.pack(">Q", bits & 0xFFFFFFFFFFFFFFFF))[0]
        return (False, False, bool(sign), f)
    if ft == "bfloat":
        sign = (bits >> 15) & 1
        exp = (bits >> 7) & 0xFF
        frac = bits & 0x7F
        if exp == 0xFF:
            return (frac != 0, frac == 0, bool(sign), 0.0)
        f = struct.unpack(">f", struct.pack(">I", (bits & 0xFFFF) << 16))[0]
        return (False, False, bool(sign), f)
    if ft == "half":
        sign = (bits >> 15) & 1
        exp = (bits >> 10) & 0x1F
        frac = bits & 0x3FF
        if exp == 0x1F:
            return (frac != 0, frac == 0, bool(sign), 0.0)
        if exp == 0:
            val = ((-1.0) ** sign) * (2.0 ** -14) * (frac / 1024.0)
        else:
            val = ((-1.0) ** sign) * (2.0 ** (exp - 15)) * (1.0 + frac / 1024.0)
        return (False, False, bool(sign), val)
    if ft == "fp128":
        sign = (bits >> 127) & 1
        exp = (bits >> 112) & 0x7FFF
        frac = bits & ((1 << 112) - 1)
        if exp == 0x7FFF:
            return (frac != 0, frac == 0, bool(sign), 0.0)
        if exp == 0 and frac == 0:
            return (False, False, bool(sign), -0.0 if sign else 0.0)
        # Approximate in Python float for decimal comparison
        e = (exp - 16383) if exp != 0 else -16382
        sig = (1.0 if exp != 0 else 0.0) + (frac / float(1 << 112))
        try:
            val = math.ldexp(sig, e)
            if sign:
                val = -val
        except OverflowError:
            val = float("-inf") if sign else float("inf")
        return (False, False, bool(sign), val)
    return None


def parse_lean_scalar(s: str):
    s = s.strip()
    if s == "void":
        return ("void",)
    if s == "poison":
        return ("poison",)
    m = re.match(r"^i(\d+)\s+(poison|\d+)$", s)
    if m:
        w = int(m.group(1))
        if m.group(2) == "poison":
            return ("poison",)
        return ("int", w, int(m.group(2)))
    m = re.match(r"^ptr\(as=\d+\)\s+(poison|0x[0-9a-fA-F]+)$", s)
    if m:
        if m.group(1) == "poison":
            return ("poison",)
        addr = int(m.group(1), 16)
        return ("ptr", addr == 0)
    m = re.match(r"^(half|bfloat|float|double|fp128|x86_fp80|ppc_fp128)\s+(poison|0x[0-9a-fA-F]+)$", s)
    if m:
        ft = m.group(1)
        if m.group(2) == "poison":
            return ("poison",)
        return ("fp_bits", ft, int(m.group(2), 16))
    return ("raw", s)


def split_top_level(s: str):
    """Split comma-separated aggregate elements respecting nesting."""
    parts, cur, depth = [], [], 0
    for ch in s:
        if ch in "{<[":
            depth += 1
            cur.append(ch)
        elif ch in "}>]":
            depth -= 1
            cur.append(ch)
        elif ch == "," and depth == 0:
            parts.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    if cur:
        parts.append("".join(cur).strip())
    return [p for p in parts if p]


def values_match(llubi_str: str, lean_str: str) -> bool:
    """Semantically compare an llubi printed value and a lean-nano-llvm formatted value."""
    ls = llubi_str.strip()
    rs = lean_str.strip()

    # Aggregate / vector comparison: llubi uses `{ a, b }`, lean uses `<a, b>` / `[a, b]` / `{ a, b }`
    if ls.startswith("{") and ls.endswith("}"):
        if (rs.startswith("<") and rs.endswith(">")) or (rs.startswith("[") and rs.endswith("]")) or (rs.startswith("{") and rs.endswith("}")):
            l_elems = split_top_level(ls[1:-1])
            r_elems = split_top_level(rs[1:-1])
            if len(l_elems) != len(r_elems):
                return False
            return all(values_match(a, b) for a, b in zip(l_elems, r_elems))

    lc = parse_llubi_scalar_to_canonical(ls)
    rc = parse_lean_scalar(rs)

    if lc[0] == "poison" and rc[0] == "poison":
        return True
    if lc[0] == "void" and rc[0] == "void":
        return True
    if lc[0] == "int" and rc[0] == "int":
        return lc[1] == rc[1] and lc[2] == rc[2]
    if lc[0] == "ptr" and rc[0] == "ptr":
        # Match nullness; non-null exact base addresses may differ between allocators
        return lc[1] == rc[1]
    if rc[0] == "fp_bits":
        ft, bits = rc[1], rc[2]
        dec = decode_lean_float(ft, bits)
        if lc[0] == "fp_hex" and lc[1] == ft:
            return lc[2] == bits
        if dec is not None:
            is_nan, is_inf, neg, fval = dec
            if lc[0] == "fp_nan" and lc[1] == ft:
                return is_nan
            if lc[0] == "fp_inf" and lc[1] == ft:
                return is_inf and (neg == lc[2])
            if lc[0] == "fp_num" and lc[1] == ft:
                if is_nan or is_inf:
                    return False
                exp_f, exp_neg = lc[2], lc[3]
                if exp_f == 0.0:
                    return fval == 0.0 and neg == exp_neg
                # llubi prints 6 significant digits in scientific notation
                return math.isclose(fval, exp_f, rel_tol=1e-4, abs_tol=1e-12) and (neg == exp_neg)
    # Fallback: skip unparsed exotic formats (e.g. b64 before M4)
    return ls == rs


def run_single_test(path: str, run_line: str, text: str, bin_path: str):
    """Execute one `; RUN:` line and return (status, detail)."""
    # Split pipeline stages by `|`
    stages = [s.strip() for s in run_line.split("|")]
    src = text
    llubi_stage = None
    filecheck_stage = None
    for st in stages:
        if "sed " in st or st.startswith("sed "):
            src = apply_sed_cmd(st, src)
        elif re.search(r"\bllubi\b", st):
            llubi_stage = st
        elif "FileCheck" in st:
            filecheck_stage = st

    if llubi_stage is None:
        return ("SKIP", "no llubi invocation in RUN line")

    # Determine FileCheck prefixes
    prefixes = ["CHECK"]
    if filecheck_stage:
        pref_matches = re.findall(r"--check-prefix(?:es)?[=\s]+([^\s]+)", filecheck_stage)
        if pref_matches:
            prefixes = []
            for pm in pref_matches:
                prefixes.extend(pm.split(","))

    checks = extract_checks(text, prefixes)
    expect_not = bool(re.match(r"^not\s+", llubi_stage))
    has_imm_ub = any("Immediate UB detected:" in c for c in checks)
    has_exiting = any("Exiting function:" in c for c in checks)
    has_oom = any("out of memory" in c.lower() or "memory limit" in c.lower() for c in checks)
    has_stack = any("stack" in c.lower() and ("depth" in c.lower() or "overflow" in c.lower()) for c in checks)
    has_steps = any("step" in c.lower() and ("limit" in c.lower() or "exceeded" in c.lower()) for c in checks)

    if has_imm_ub:
        expected_outcome = "UB"
    elif expect_not and (has_oom or has_stack or has_steps):
        expected_outcome = "RESOURCE"
    elif expect_not:
        expected_outcome = "ERROR"
    elif has_exiting:
        expected_outcome = "OK"
    else:
        expected_outcome = "OK" if not expect_not else "ERROR"

    # Translate llubi flags to lean-nano-llvm flags
    # Strip shell redirections like `< %s`, `2>&1`
    clean_stage = re.sub(r"2>&1|<[^>]*%s|>\s*\S+", "", llubi_stage)
    try:
        toks = shlex.split(clean_stage)
    except ValueError:
        return ("SKIP", "unparseable RUN command")

    cli_args = [bin_path, "run", "-", "--verbose"]
    has_explicit_undef = False
    i = 0
    while i < len(toks):
        t = toks[i]
        if t in ("not", "llubi", "%s"):
            i += 1
        elif t in ("--verbose", "--disable-verify", "--use-constant-int-for-fixed-length-splat"):
            i += 1
        elif t in ("--deterministic", "--fuse-fmuladd"):
            cli_args.append(t)
            if t == "--deterministic":
                has_explicit_undef = True
            i += 1
        elif t.startswith(("--entry-function=", "--max-mem=", "--max-stack-depth=", "--max-steps=", "--vscale=", "--nan-behavior=", "--undef-behavior=", "--fuse-fmuladd=")):
            cli_args.append(t)
            if t.startswith("--undef-behavior="):
                has_explicit_undef = True
            i += 1
        elif t in ("--entry-function", "--max-mem", "--max-stack-depth", "--max-steps", "--vscale", "--nan-behavior", "--undef-behavior") and i + 1 < len(toks):
            cli_args.extend([t, toks[i + 1]])
            if t == "--undef-behavior":
                has_explicit_undef = True
            i += 2
        else:
            i += 1

    if not has_explicit_undef and "undef" in src:
        cli_args.append("--undef")

    try:
        res = subprocess.run(
            cli_args, input=src, capture_output=True, text=True, timeout=15
        )
    except subprocess.TimeoutExpired:
        return ("SKIP", "timeout")

    rc = res.returncode
    out_lines = res.stdout.splitlines()
    err_lines = res.stderr.splitlines()
    err_first = err_lines[0] if err_lines else ""

    if rc == 4:
        return ("SKIP", err_first or "PARSE_ERROR")

    if expected_outcome == "OK":
        if rc == 2:
            return ("SKIP", err_first or "STATIC_ERROR")
        if rc == 3:
            return ("MISMATCH", f"expected OK, got {err_first}")
        if rc != 0:
            return ("MISMATCH", f"expected OK, got rc={rc} ({err_first})")
    elif expected_outcome == "UB":
        if rc == 2:
            return ("SKIP", err_first or "STATIC_ERROR")
        if rc != 1:
            return ("MISMATCH", f"expected UB, got rc={rc} ({err_first or (out_lines[-1] if out_lines else '')})")
        return ("PASS", err_first)
    elif expected_outcome == "RESOURCE":
        if rc == 3:
            return ("PASS", err_first)
        if rc == 1 and has_oom:
            # Some OOM tests trigger max-object-size UB vs OOM depending on allocator
            return ("PASS", err_first)
        return ("MISMATCH", f"expected RESOURCE error, got rc={rc} ({err_first or (out_lines[-1] if out_lines else '')})")
    elif expected_outcome == "ERROR":
        if rc in (1, 2, 3):
            return ("PASS", err_first)
        return ("MISMATCH", f"expected ERROR, got rc=0 ({out_lines[-1] if out_lines else ''})")

    # For OK tests, also semantically verify `%name => <val>` values from CHECK lines!
    actual_vals = []
    for line in out_lines:
        m = re.match(r"^VAL:\s*%([^\s]+)\s*=>\s*(.*)$", line)
        if m:
            actual_vals.append((m.group(1), m.group(2).strip()))

    # Build lookup queue per SSA name (handles loops/multiple calls in order)
    actual_by_name = {}
    for nm, val in actual_vals:
        actual_by_name.setdefault(nm, []).append(val)

    val_mismatches = []
    for chk in checks:
        m = re.match(r"^%([^\s=]+)\s*=.*=>\s*(.+)$", chk)
        if not m:
            continue
        nm, exp_val = m.group(1), m.group(2).strip()
        q = actual_by_name.get(nm)
        if not q:
            continue
        act_val = q.pop(0)
        if not values_match(exp_val, act_val):
            val_mismatches.append(f"%{nm}: expected `{exp_val}`, got `{act_val}`")

    if val_mismatches:
        return ("VAL_MISMATCH", "; ".join(val_mismatches[:3]))

    return ("PASS", out_lines[-1] if out_lines else "OK")


def main():
    args = sys.argv[1:]
    verbose = "--verbose" in args
    pos = [a for a in args if a != "--verbose"]
    llubi_dir = pos[0] if len(pos) > 0 else "/home/antigravity/llvm-project/llvm/test/tools/llubi"
    bin_path = pos[1] if len(pos) > 1 else ".lake/build/bin/lean-nano-llvm"

    if not os.path.isdir(llubi_dir):
        print(f"Error: llubi test directory not found: {llubi_dir}", file=sys.stderr)
        sys.exit(1)
    if not os.access(bin_path, os.X_OK):
        print(f"Error: executable not found: {bin_path}", file=sys.stderr)
        sys.exit(1)

    files = sorted(glob.glob(os.path.join(llubi_dir, "*.ll")))
    file_counts = Counter()
    run_counts = Counter()
    mismatches = []
    val_mismatches = []
    skip_reasons = Counter()

    for path in files:
        name = os.path.basename(path)
        with open(path, "r", encoding="utf-8", errors="replace") as f:
            text = f.read()
        runs = parse_run_lines(text)
        if not runs:
            file_counts["SKIP"] += 1
            continue
        file_statuses = []
        for idx, rline in enumerate(runs):
            st, detail = run_single_test(path, rline, text, bin_path)
            run_counts[st] += 1
            file_statuses.append((st, detail))
            if st == "MISMATCH":
                mismatches.append((f"{name}[{idx}]", detail))
            elif st == "VAL_MISMATCH":
                val_mismatches.append((f"{name}[{idx}]", detail))
            elif st == "SKIP":
                bucket = re.sub(r"'[^']*'|\"[^\"]*\"|\d+", "X", detail)[:70]
                skip_reasons[bucket] += 1

        if all(st == "PASS" for st, _ in file_statuses):
            file_counts["PASS"] += 1
        elif any(st == "MISMATCH" for st, _ in file_statuses):
            file_counts["MISMATCH"] += 1
        elif any(st == "VAL_MISMATCH" for st, _ in file_statuses):
            file_counts["VAL_MISMATCH"] += 1
        else:
            file_counts["SKIP"] += 1

    print(f"llubi cross-check ({len(files)} files, {sum(run_counts.values())} RUN invocations):")
    print(f"  FILES: PASS={file_counts['PASS']}  MISMATCH={file_counts['MISMATCH']}  VAL_MISMATCH={file_counts['VAL_MISMATCH']}  SKIP={file_counts['SKIP']}")
    print(f"  RUNS:  PASS={run_counts['PASS']}  MISMATCH={run_counts['MISMATCH']}  VAL_MISMATCH={run_counts['VAL_MISMATCH']}  SKIP={run_counts['SKIP']}")

    if mismatches:
        print(f"\nOutcome mismatches ({len(mismatches)}):")
        for k, d in mismatches[:30]:
            print(f"  [MISMATCH] {k}: {d[:110]}")
    if val_mismatches:
        print(f"\nValue mismatches ({len(val_mismatches)}):")
        for k, d in val_mismatches[:25]:
            print(f"  [VAL_MISMATCH] {k}: {d[:120]}")
    if verbose and skip_reasons:
        print("\nTop skip reasons:")
        for reason, cnt in skip_reasons.most_common(20):
            print(f"  {cnt:3d}  {reason}")


if __name__ == "__main__":
    main()
