#!/usr/bin/env bash
# Keeps incremental rebuilds narrow: test and proof files must import only the
# modules they use, so editing one tactic does not rebuild unrelated proofs.
#
# 1. No file under Tests/ imports the `LeanNanoLlvm` root or the
#    `LeanNanoLlvm.Refinement` umbrella.
# 2. Only files that use `llvm_disprove` import `LeanNanoLlvm.Refinement.Disprove`.
set -euo pipefail
cd "$(dirname "$0")/.."

status=0

if grep -rnE '^import LeanNanoLlvm(\.Refinement)?[[:space:]]*$' --include='*.lean' Tests; then
  echo "Error: import the specific module (e.g. LeanNanoLlvm.Refinement.Tactic), not an umbrella." >&2
  status=1
fi

while IFS= read -r f; do
  if ! grep -q 'llvm_disprove' "$f"; then
    echo "$f: imports LeanNanoLlvm.Refinement.Disprove but does not use llvm_disprove" >&2
    status=1
  fi
done < <(grep -rlE '^import LeanNanoLlvm\.Refinement\.Disprove[[:space:]]*$' --include='*.lean' Tests || true)

exit $status
