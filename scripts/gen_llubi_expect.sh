#!/usr/bin/env bash
# (Re)generate the `; LLUBI-*` expectation block of Tests/ll files from a reference llubi.
#
# Usage: scripts/gen_llubi_expect.sh LLUBI FILE.ll...
#   LLUBI: the pinned llubi (difftest/tools/build_oracles.sh builds it at
#          difftest/.oracles/bin/llubi, at the LLVM commit of difftest/tools/pins.env).
#
# The block records llubi's exit code, stdout and stderr for `llubi --verbose -` with the
# module on standard input. Any previous block is removed first; the new one is appended at the
# end of the file, so the line numbers llubi prints for the code are unchanged.
set -euo pipefail
LLUBI=$1; shift
for f in "$@"; do
  body=$(mktemp); out=$(mktemp); err=$(mktemp)
  grep -v -e '^; LLUBI-' -e '^; llubi expectations' "$f" | sed -e :a -e '/^\n*$/{$d;N;ba' -e '}' >"$body"
  set +e
  "$LLUBI" --verbose - <"$body" >"$out" 2>"$err"
  code=$?
  set -e
  {
    cat "$body"
    echo ""
    echo "; llubi expectations (scripts/gen_llubi_expect.sh, pinned llubi; do not edit by hand)"
    echo "; LLUBI-EXIT: $code"
    sed -e 's/^/; LLUBI-OUT: /' -e 's/^; LLUBI-OUT: $/; LLUBI-OUT:/' "$out"
    sed -e 's/^/; LLUBI-ERR: /' -e 's/^; LLUBI-ERR: $/; LLUBI-ERR:/' "$err"
  } >"$f"
  rm -f "$body" "$out" "$err"
  echo "updated $f (llubi exit $code)"
done
