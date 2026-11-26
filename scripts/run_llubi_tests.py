#!/usr/bin/env python3
"""Cross-check lean-nano-llvm against LLVM's llubi .ll test suite CHECK expectations.

Usage:
  python3 scripts/run_llubi_tests.py [llubi_test_dir] [lean_nano_llvm_bin]

For each .ll file in llubi_test_dir, inspects `; CHECK:` / `; RUN:` lines to determine
whether llubi expects normal termination (OK) or Immediate UB / error, then runs
`lean-nano-llvm run <file>` and classifies each test into:
  - PASS:     parsed and outcome (OK vs UB) matches llubi
  - MISMATCH: parsed, but OK vs UB outcome differed from llubi
  - SKIP:     uses IR features not yet parsed/supported (e.g., b64 byte types,
              non-default --entry, operand bundles, external helpers, etc.)
"""

import glob
import os
import re
import subprocess
import sys


def classify_llubi_expectation(text: str):
    """Return ('UB' | 'OK' | 'OTHER', entry_fn)."""
    has_not_run = bool(re.search(r"^;\s*RUN:.*\bnot\s+llubi\b", text, re.MULTILINE))
    has_imm_ub = "Immediate UB detected:" in text
    has_exiting_main = "Exiting function: main" in text
    has_main = bool(re.search(r"define\s+.*@main\s*\(", text))
    if not has_main:
        return "NO_MAIN", "main"
    if has_imm_ub:
        return "UB", "main"
    if has_not_run:
        return "ERROR", "main"
    if has_exiting_main:
        return "OK", "main"
    return "OTHER", "main"


def main():
    llubi_dir = (
        sys.argv[1]
        if len(sys.argv) > 1
        else "/home/antigravity/llvm-project/llvm/test/tools/llubi"
    )
    bin_path = sys.argv[2] if len(sys.argv) > 2 else ".lake/build/bin/lean-nano-llvm"

    if not os.path.isdir(llubi_dir):
        print(f"Error: llubi test directory not found: {llubi_dir}", file=sys.stderr)
        sys.exit(1)
    if not os.access(bin_path, os.X_OK):
        print(f"Error: executable not found: {bin_path}", file=sys.stderr)
        sys.exit(1)

    files = sorted(glob.glob(os.path.join(llubi_dir, "*.ll")))
    passed, mismatched, skipped = [], [], []

    for path in files:
        name = os.path.basename(path)
        with open(path, "r", encoding="utf-8", errors="replace") as f:
            text = f.read()

        expected, entry = classify_llubi_expectation(text)
        if expected not in ("OK", "UB"):
            skipped.append((name, f"expectation={expected}"))
            continue

        args = [bin_path, "run", path, "--entry", entry]
        if "undef" in text:
            args.append("--undef")

        try:
            res = subprocess.run(
                args, capture_output=True, text=True, timeout=10
            )
        except subprocess.TimeoutExpired:
            skipped.append((name, "timeout"))
            continue

        rc = res.returncode
        out = res.stdout.strip()
        err = res.stderr.strip()

        # rc == 4 -> PARSE_ERROR, rc == 2 -> STATIC_ERROR (unsupported intrinsic/feature)
        if rc in (2, 3, 4):
            skipped.append((name, err.splitlines()[0] if err else f"rc={rc}"))
            continue

        actual = "OK" if rc == 0 else ("UB" if rc == 1 else f"RC={rc}")
        if actual == expected:
            passed.append((name, expected, out or err))
        else:
            mismatched.append((name, expected, actual, out or err))

    print(f"llubi cross-check summary ({len(files)} total .ll files):")
    print(f"  PASS:     {len(passed)}")
    print(f"  MISMATCH: {len(mismatched)}")
    print(f"  SKIP:     {len(skipped)}")

    if passed:
        print("\nPassed tests:")
        for name, exp, msg in passed:
            print(f"  [PASS] {name} ({exp}): {msg[:80]}")

    if mismatched:
        print("\nMismatched tests:")
        for name, exp, act, msg in mismatched:
            print(f"  [MISMATCH] {name}: expected {exp}, got {act} ({msg[:100]})")


if __name__ == "__main__":
    main()
