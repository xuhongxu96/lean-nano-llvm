#!/usr/bin/env bash
# Run LLVM's llubi test suite (llvm/test/tools/llubi) unmodified with lit + FileCheck, using
# lean-nano-llvm's llubi-compatible frontend (`lean-nano-llvm llubi`) in place of `llubi`.
#
# Usage: scripts/run_llubi_tests.sh [llubi_test_dir] [extra lit arguments...]
#
# Without a test directory (or $LLUBI_TEST_DIR), the tests are fetched (sparse, shallow) from
# llvm-project at $LLVM_COMMIT. Requires `lit` (pip install lit) and LLVM's `FileCheck` on PATH
# (or set FILECHECK=/path/to/FileCheck).
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
LLVM_COMMIT=${LLVM_COMMIT:-a58c4abbc75656510f992849285ea3a1da725bae}

DIR=${LLUBI_TEST_DIR:-}
if [ $# -gt 0 ] && [ -d "$1" ]; then
  DIR=$1
  shift
fi

if [ -z "$DIR" ]; then
  CHECKOUT="$ROOT/.lake/llvm-project"
  if [ ! -d "$CHECKOUT/llvm/test/tools/llubi" ]; then
    rm -rf "$CHECKOUT"
    git init -q "$CHECKOUT"
    git -C "$CHECKOUT" remote add origin https://github.com/llvm/llvm-project.git
    git -C "$CHECKOUT" sparse-checkout set llvm/test/tools/llubi
    git -C "$CHECKOUT" fetch -q --depth 1 --filter=blob:none origin "$LLVM_COMMIT"
    git -C "$CHECKOUT" checkout -q FETCH_HEAD
  fi
  DIR="$CHECKOUT/llvm/test/tools/llubi"
fi

exec lit -sv --param llubi_test_dir="$DIR" "$@" "$ROOT/Tests/llubi"
