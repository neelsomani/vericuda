#!/usr/bin/env bash

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

fail() {
  echo "[ptx-check] ERROR: $1" >&2
  exit 1
}

require_pattern() {
  local file="$1"
  local pattern="$2"
  local description="$3"
  grep -Eq "$pattern" "$file" || fail "$description ($file)"
}

require_count() {
  local file="$1"
  local pattern="$2"
  local minimum="$3"
  local description="$4"
  local count
  count="$(grep -Ec "$pattern" "$file" || true)"
  if (( count < minimum )); then
    fail "$description: expected at least $minimum, found $count ($file)"
  fi
}

require_function_count() {
  local file="$1"
  local function_name="$2"
  local pattern="$3"
  local minimum="$4"
  local description="$5"
  local count
  count="$(awk -v function_name="$function_name" -v pattern="$pattern" '
    /^[[:space:]]*\.visible[[:space:]]+\.func/ && index($0, function_name) {
      in_function = 1
      found_function = 1
    }
    in_function && $0 ~ pattern { count += 1 }
    in_function && /^[[:space:]]*}/ { in_function = 0 }
    END {
      if (!found_function) print -1
      else print count + 0
    }
  ' "$file")"
  if (( count < 0 )); then
    fail "could not find visible function containing '$function_name' ($file)"
  fi
  if (( count < minimum )); then
    fail "$description: expected at least $minimum, found $count in '$function_name' ($file)"
  fi
}

SAXPY_COQ="$ROOT_DIR/coq/examples/saxpy_gen.v"
ATOMIC_COQ="$ROOT_DIR/coq/examples/atomic_flag_gen.v"
SAXPY_PTX="$ROOT_DIR/target/saxpy.ptx"
ATOMIC_PTX="$ROOT_DIR/target/atomic_flag.ptx"

for required in "$SAXPY_COQ" "$ATOMIC_COQ" "$SAXPY_PTX" "$ATOMIC_PTX"; do
  [[ -f "$required" ]] || fail "missing generated artifact: $required"
done

# The straight-line SAXPY extraction contains two f32 loads and one f32 store.
# LLVM may unroll the real loop, so the emitted PTX can contain more operations;
# this check validates operation kinds, not one-to-one instruction counts.
require_count "$SAXPY_COQ" 'M\.SLoad .*M\.TyF32' 2 \
  "translated SAXPY trace is missing f32 loads"
require_count "$SAXPY_COQ" 'M\.SStore .*M\.TyF32' 1 \
  "translated SAXPY trace is missing an f32 store"
require_function_count "$SAXPY_PTX" 'saxpy' \
  '^[[:space:]]*ld\.f32[[:space:]]' 2 \
  "rustc PTX is missing generic-address f32 loads"
require_function_count "$SAXPY_PTX" 'saxpy' \
  '^[[:space:]]*st\.f32[[:space:]]' 1 \
  "rustc PTX is missing a generic-address f32 store"

# The atomic trace's semantic and SYS-scope tags must agree with the concrete
# sm_70 mnemonics emitted by rustc/LLVM.
require_pattern "$ATOMIC_COQ" 'M\.SAtomicLoadAcquire .*M\.TyU32' \
  "translated atomic trace is missing its acquire load"
require_pattern "$ATOMIC_COQ" 'M\.SAtomicStoreRelease .*M\.TyU32' \
  "translated atomic trace is missing its release store"
require_function_count "$ATOMIC_PTX" 'acquire_release' \
  '^[[:space:]]*ld\.acquire\.sys\.u32[[:space:]]' 1 \
  "rustc PTX is missing ld.acquire.sys.u32"
require_function_count "$ATOMIC_PTX" 'acquire_release' \
  '^[[:space:]]*st\.release\.sys\.u32[[:space:]]' 1 \
  "rustc PTX is missing st.release.sys.u32"

echo "[ptx-check] Coq event kinds match the memory-operation forms in emitted PTX"
