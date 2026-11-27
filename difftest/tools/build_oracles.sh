#!/usr/bin/env bash
# Build the two oracles used by the differential-testing campaign at pinned revisions:
#   * llubi    (llvm-project/llvm/tools/llubi), the UB-aware LLVM IR interpreter
#   * alive-tv (AliveToolkit/alive2), the refinement checker
# plus the LLVM utilities the corpus and mutation pipeline need (opt, llvm-as, llvm-dis,
# FileCheck). One LLVM build with RTTI (required by Alive2) serves both oracles, so that
# llubi and Alive2 parse IR with the same LLVM.
#
# Usage: difftest/tools/build_oracles.sh [PREFIX]   (default PREFIX: difftest/.oracles)
#
# Pins are read from difftest/tools/pins.env; the resulting versions (commit hashes, Z3
# version, compiler) are written to $PREFIX/versions.json for the paper's artifact section.
# Prerequisites: cmake, ninja, a C++20 compiler, re2c, Z3 >= 4.8.5 (libz3-dev), zlib.
set -euo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
# shellcheck source=pins.env
source "$HERE/pins.env"
PREFIX=${1:-$ROOT/difftest/.oracles}
JOBS=${JOBS:-$(nproc)}
mkdir -p "$PREFIX"
PREFIX=$(cd "$PREFIX" && pwd)

fetch() { # fetch DIR URL COMMIT
  local dir=$1 url=$2 commit=$3
  if [ ! -d "$dir/.git" ]; then
    git init -q "$dir"
    git -C "$dir" remote add origin "$url"
  fi
  if [ "$(git -C "$dir" rev-parse -q --verify HEAD 2>/dev/null || true)" != "$commit" ]; then
    git -C "$dir" fetch -q --depth 1 origin "$commit"
    git -C "$dir" checkout -q FETCH_HEAD
  fi
}

LLVM_SRC=${LLVM_SRC:-$PREFIX/src/llvm-project}
ALIVE2_SRC=${ALIVE2_SRC:-$PREFIX/src/alive2}
fetch "$LLVM_SRC" https://github.com/llvm/llvm-project.git "$LLVM_COMMIT"
fetch "$ALIVE2_SRC" https://github.com/AliveToolkit/alive2.git "$ALIVE2_COMMIT"

LLVM_BUILD=$PREFIX/build/llvm
cmake -S "$LLVM_SRC/llvm" -B "$LLVM_BUILD" -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DLLVM_ENABLE_ASSERTIONS=ON \
  -DLLVM_ENABLE_RTTI=ON \
  -DLLVM_ENABLE_EH=ON \
  -DLLVM_TARGETS_TO_BUILD=X86 \
  -DLLVM_ENABLE_PROJECTS= \
  -DLLVM_INCLUDE_BENCHMARKS=OFF \
  -DLLVM_INCLUDE_EXAMPLES=OFF \
  -DLLVM_ENABLE_ZSTD=OFF \
  -DLLVM_PARALLEL_LINK_JOBS=2 >/dev/null
ninja -C "$LLVM_BUILD" -j "$JOBS" llubi opt llvm-as llvm-dis llvm-extract FileCheck not count \
  LLVMPasses LLVMCodeGen LLVMX86CodeGen LLVMX86Desc LLVMX86Info LLVMBitWriter LLVMIRReader

ALIVE2_BUILD=$PREFIX/build/alive2
cmake -S "$ALIVE2_SRC" -B "$ALIVE2_BUILD" -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DBUILD_LLVM_UTILS=ON \
  -DCMAKE_PREFIX_PATH="$LLVM_BUILD" >/dev/null
ninja -C "$ALIVE2_BUILD" -j "$JOBS" alive-tv alive-exec

mkdir -p "$PREFIX/bin"
for t in llubi opt llvm-as llvm-dis llvm-extract FileCheck not count; do
  ln -sf "$LLVM_BUILD/bin/$t" "$PREFIX/bin/$t"
done
for t in alive-tv alive-exec; do
  ln -sf "$ALIVE2_BUILD/$t" "$PREFIX/bin/$t"
done

z3v=$(z3 --version 2>/dev/null || echo unknown)
cxxv=$(c++ --version | head -1)
cat >"$PREFIX/versions.json" <<JSON
{
  "llvm_commit": "$(git -C "$LLVM_SRC" rev-parse HEAD)",
  "llvm_commit_date": "$(git -C "$LLVM_SRC" log -1 --format=%cI)",
  "alive2_commit": "$(git -C "$ALIVE2_SRC" rev-parse HEAD)",
  "alive2_commit_date": "$(git -C "$ALIVE2_SRC" log -1 --format=%cI)",
  "z3": "$z3v",
  "cxx": "$cxxv",
  "llvm_build_flags": "Release, assertions ON, RTTI ON, EH ON, targets X86"
}
JSON
echo "Oracles installed in $PREFIX/bin; versions in $PREFIX/versions.json"
