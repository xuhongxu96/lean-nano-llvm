#!/usr/bin/env bash
# Regression suite over Tests/ll/*.ll. Each file states its expectations in comments:
#
#   `lean-nano-llvm run` (semantics):
#     ; EXPECT_EXIT: <code>      required for this check
#     ; EXPECT_OUT: <text>       stdout contains <text>
#     ; EXPECT_ERR: <text>       stderr contains <text>
#     ; ARGS: <args>             extra arguments
#
#   `lean-nano-llvm llubi --verbose` (byte-exact llubi output, module on standard input):
#     ; LLUBI-EXIT: <code>       required for this check
#     ; LLUBI-OUT: <line>        one per stdout line, in order
#     ; LLUBI-ERR: <line>        one per stderr line, in order (`; LLUBI-ERR:` alone: empty line)
#   These lines are generated from the pinned llubi by scripts/gen_llubi_expect.sh and kept at the
#   end of the file, after the code, so they do not shift the line numbers llubi prints.
#
#   ; XFAIL: <reason>          a known bug: the expectations state the correct behaviour; the
#                              test counts as passing while it fails and fails (XPASS) once the
#                              bug is fixed, so that the marker is removed together with the fix.
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
  expect_exit=$(grep -m1 '^; EXPECT_EXIT:' "$f" | sed 's/^; EXPECT_EXIT:[[:space:]]*//' || true)
  expect_out=$(grep -m1 '^; EXPECT_OUT:' "$f" | sed 's/^; EXPECT_OUT:[[:space:]]*//' || true)
  expect_err=$(grep -m1 '^; EXPECT_ERR:' "$f" | sed 's/^; EXPECT_ERR:[[:space:]]*//' || true)
  extra_args=$(grep -m1 '^; ARGS:' "$f" | sed 's/^; ARGS:[[:space:]]*//' || true)
  llubi_exit=$(grep -m1 '^; LLUBI-EXIT:' "$f" | sed 's/^; LLUBI-EXIT:[[:space:]]*//' || true)
  xfail_reason=$(grep -m1 '^; XFAIL:' "$f" | sed 's/^; XFAIL:[[:space:]]*//' || true)

  if [[ -z "$expect_exit" && -z "$llubi_exit" ]]; then
    echo "FAIL $f: no expectations (EXPECT_EXIT or LLUBI-EXIT)"
    fail=$((fail + 1))
    continue
  fi

  ok=1
  if [[ -n "$expect_exit" ]]; then
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
  fi

  if [[ -n "$llubi_exit" ]]; then
    exp_out=$(mktemp); exp_err=$(mktemp); got_out=$(mktemp); got_err=$(mktemp)
    sed -n -e 's/^; LLUBI-OUT: //p' -e 's/^; LLUBI-OUT:$//p' "$f" >"$exp_out"
    sed -n -e 's/^; LLUBI-ERR: //p' -e 's/^; LLUBI-ERR:$//p' "$f" >"$exp_err"
    set +e
    "$BIN" llubi --verbose - <"$f" >"$got_out" 2>"$got_err"
    got_exit=$?
    set -e
    if [[ "$got_exit" != "$llubi_exit" ]]; then
      echo "FAIL $f: llubi mode: expected exit $llubi_exit, got $got_exit"
      ok=0
    fi
    if ! diff -q "$exp_out" "$got_out" >/dev/null; then
      echo "FAIL $f: llubi mode: stdout differs"; { diff "$exp_out" "$got_out" || true; } | head -8
      ok=0
    fi
    if ! diff -q "$exp_err" "$got_err" >/dev/null; then
      echo "FAIL $f: llubi mode: stderr differs"; { diff "$exp_err" "$got_err" || true; } | head -8
      ok=0
    fi
    rm -f "$exp_out" "$exp_err" "$got_out" "$got_err"
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
    echo "PASS $f"
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
