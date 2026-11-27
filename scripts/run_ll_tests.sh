#!/usr/bin/env bash
set -euo pipefail

BIN="${1:-.lake/build/bin/lean-nano-llvm}"
if [[ ! -x "$BIN" ]]; then
  echo "Error: executable '$BIN' not found. Run 'lake build' first." >&2
  exit 1
fi

pass=0
fail=0
xfail=0

for f in Tests/ll/*.ll; do
  expect_exit=$(grep -m1 '^; EXPECT_EXIT:' "$f" | sed 's/^; EXPECT_EXIT:[[:space:]]*//')
  expect_out=$(grep -m1 '^; EXPECT_OUT:' "$f" | sed 's/^; EXPECT_OUT:[[:space:]]*//' || true)
  expect_err=$(grep -m1 '^; EXPECT_ERR:' "$f" | sed 's/^; EXPECT_ERR:[[:space:]]*//' || true)
  extra_args=$(grep -m1 '^; ARGS:' "$f" | sed 's/^; ARGS:[[:space:]]*//' || true)
  # `; XFAIL: <reason>`: a known bug. The EXPECT lines state the correct behaviour (llubi's);
  # the test counts as passing while it fails, and fails (XPASS) once the bug is fixed, so
  # that the marker is removed together with the fix.
  xfail_reason=$(grep -m1 '^; XFAIL:' "$f" | sed 's/^; XFAIL:[[:space:]]*//' || true)

  out_file=$(mktemp)
  err_file=$(mktemp)
  set +e
  # shellcheck disable=SC2086
  "$BIN" run "$f" $extra_args >"$out_file" 2>"$err_file"
  actual_exit=$?
  set -e
  actual_out=$(cat "$out_file")
  actual_err=$(cat "$err_file")
  rm -f "$out_file" "$err_file"

  ok=1
  if [[ "$actual_exit" != "$expect_exit" ]]; then
    echo "FAIL $f: expected exit $expect_exit, got $actual_exit (out='$actual_out', err='$actual_err')"
    ok=0
  fi
  if [[ -n "$expect_out" && "$actual_out" != *"$expect_out"* ]]; then
    echo "FAIL $f: expected stdout containing '$expect_out', got '$actual_out'"
    ok=0
  fi
  if [[ -n "$expect_err" && "$actual_err" != *"$expect_err"* ]]; then
    echo "FAIL $f: expected stderr containing '$expect_err', got '$actual_err'"
    ok=0
  fi

  if [[ -n "$xfail_reason" ]]; then
    if [[ "$ok" -eq 1 ]]; then
      echo "XPASS $f: passes but is marked XFAIL ($xfail_reason); remove the marker"
      fail=$((fail + 1))
    else
      echo "XFAIL $f ($xfail_reason)"
      xfail=$((xfail + 1))
    fi
  elif [[ "$ok" -eq 1 ]]; then
    echo "PASS $f (exit=$actual_exit)"
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
  fi
done

echo ""
echo "LL regression suite: $pass passed, $xfail expected failures, $fail failed."
if [[ "$fail" -ne 0 ]]; then
  exit 1
fi
