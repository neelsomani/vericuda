#!/usr/bin/env bash

set -euo pipefail

BENCH_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_DIR="$(cd "$BENCH_DIR/.." && pwd)"
CUDA_ARCH="${1:-${CUDA_ARCH:-sm_80}}"
RUN_STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
RESULT_DIR="${2:-$BENCH_DIR/results/$RUN_STAMP}"

if [[ ! "$CUDA_ARCH" =~ ^sm_[0-9]+$ ]]; then
  echo "error: CUDA architecture must look like sm_80 or sm_89" >&2
  echo "usage: $0 [sm_NN] [result-directory]" >&2
  exit 2
fi

for command_name in nvidia-smi nvcc; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "error: required command not found: $command_name" >&2
    exit 1
  fi
done

mkdir -p "$RESULT_DIR"
RESULT_DIR="$(cd "$RESULT_DIR" && pwd)"

ATOMIC_BIN="$RESULT_DIR/atomic_reduce"
TREE_BIN="$RESULT_DIR/tree_reduce"
ATOMIC_CSV="$RESULT_DIR/atomic_histogram.csv"
TREE_CSV="$RESULT_DIR/tree_histogram.csv"
METADATA="$RESULT_DIR/environment.txt"
COMMANDS="$RESULT_DIR/commands.txt"

record_command() {
  printf '$' >> "$COMMANDS"
  printf ' %q' "$@" >> "$COMMANDS"
  printf '\n' >> "$COMMANDS"
}

{
  echo "UTC timestamp: $RUN_STAMP"
  echo "Repository: $REPO_DIR"
  echo "Git commit: $(git -C "$REPO_DIR" rev-parse HEAD 2>/dev/null || echo unknown)"
  echo "CUDA architecture: $CUDA_ARCH"
  echo "CUDA_VISIBLE_DEVICES: ${CUDA_VISIBLE_DEVICES:-<unset; CUDA default device>}"
  echo
  echo '$ nvidia-smi'
  nvidia-smi
  echo
  echo '$ nvidia-smi --query-gpu=name,uuid,driver_version --format=csv'
  nvidia-smi --query-gpu=name,uuid,driver_version --format=csv
  echo
  echo '$ nvcc --version'
  nvcc --version
} > "$METADATA"

: > "$COMMANDS"

record_command nvcc -std=c++17 -O3 -arch="$CUDA_ARCH" \
  "$BENCH_DIR/atomic_reduce.cu" -o "$ATOMIC_BIN"
nvcc -std=c++17 -O3 -arch="$CUDA_ARCH" \
  "$BENCH_DIR/atomic_reduce.cu" -o "$ATOMIC_BIN"

record_command nvcc -std=c++17 -O3 -arch="$CUDA_ARCH" \
  "$BENCH_DIR/tree_reduce.cu" -o "$TREE_BIN"
nvcc -std=c++17 -O3 -arch="$CUDA_ARCH" \
  "$BENCH_DIR/tree_reduce.cu" -o "$TREE_BIN"

record_command "$ATOMIC_BIN" --csv "$ATOMIC_CSV"
"$ATOMIC_BIN" --csv "$ATOMIC_CSV" | tee "$RESULT_DIR/atomic.log"

record_command "$TREE_BIN" --csv "$TREE_CSV"
"$TREE_BIN" --csv "$TREE_CSV" | tee "$RESULT_DIR/tree.log"

echo
echo "Benchmark complete."
echo "Results: $RESULT_DIR"
echo "Atomic histogram: $ATOMIC_CSV"
echo "Tree histogram:   $TREE_CSV"
echo "Metadata: $METADATA"
echo "Commands: $COMMANDS"
