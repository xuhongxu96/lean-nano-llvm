#!/usr/bin/env bash
# Byte-exact regression tests of the llubi-compatible frontend (`lean-nano-llvm llubi`).
#
# Each Tests/llubi-regress/NAME.ll has a golden NAME.expected: the exit code, stdout and stderr
# of the pinned llubi (difftest/tools/pins.env) run as `llubi --verbose -` with the module on
# standard input. A test passes when our output is identical. `; XFAIL: <reason>` marks a known
# difference (difftest/BUGS.md); such a test fails (XPASS) once the difference is gone.
#
# Usage: scripts/run_llubi_regress.sh [--regen LLUBI]   (--regen rewrites the goldens with LLUBI)
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
BIN=${BIN:-$ROOT/.lake/build/bin/lean-nano-llvm}
DIR=$ROOT/Tests/llubi-regress

capture() { # capture CMD... < module  -> golden text
  local out err code
  out=$(mktemp); err=$(mktemp)
  set +e; "$@" --verbose - >"$out" 2>"$err"; code=$?; set -e
  printf 'exit: %s\n--- stdout\n' "$code"; cat "$out"; printf -- '--- stderr\n'; cat "$err"
  rm -f "$out" "$err"
}

if [ "${1:-}" = "--regen" ]; then
  for f in "$DIR"/*.ll; do capture "$2" <"$f" >"${f%.ll}.expected"; done
  echo "goldens regenerated with $2"; exit 0
fi

pass=0 xfail=0 fail=0
for f in "$DIR"/*.ll; do
  exp="${f%.ll}.expected"
  reason=$(grep -m1 '^; XFAIL:' "$f" | sed 's/^; XFAIL:[[:space:]]*//' || true)
  if diff -q <(capture "$BIN" llubi <"$f") "$exp" >/dev/null; then ok=1; else ok=0; fi
  name=$(basename "$f")
  if [ -n "$reason" ]; then
    if [ $ok = 1 ]; then echo "XPASS $name: matches llubi but is marked XFAIL; remove the marker"; fail=$((fail+1))
    else echo "XFAIL $name ($reason)"; xfail=$((xfail+1)); fi
  elif [ $ok = 1 ]; then echo "PASS $name"; pass=$((pass+1))
  else echo "FAIL $name"; diff <(capture "$BIN" llubi <"$f") "$exp" | head -20; fail=$((fail+1)); fi
done
echo ""; echo "llubi regression suite: $pass passed, $xfail expected failures, $fail failed."
[ $fail -eq 0 ]
