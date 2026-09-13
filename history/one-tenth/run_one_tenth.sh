#!/usr/bin/env bash
# Two arithmetic methods plus coefficient regressions; geometry is reviewed separately.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
ARB_PYTHON="${ARB_PYTHON:-/home/argustest/research/star-kakeya-wt-exact-ray-envelope/.venv/bin/python}"
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
for mode in normal optimized; do
  flags=(-B)
  if [[ "$mode" == optimized ]]; then flags+=(-O); fi
  printf '\n=== one-tenth %s ===\n' "$mode"
  if ! raw=$(timeout 60 "$ARB_PYTHON" "${flags[@]}" "$ROOT/low-source-b2/integrated-low/check.py"); then
    printf '%s\n' "$raw"
    exit 1
  fi
  if [[ "$raw" != *"NEW MIXED CERTIFICATE PASSES;"* ]]; then
    printf '%s\nMissing final IL certificate marker\n' "$raw"
    exit 1
  fi
  printf 'PASS original Fraction-series IL certificate (its rejected precursor is retained in the source log).\n'
  timeout 60 "$ARB_PYTHON" "${flags[@]}" "$ROOT/test_one_tenth.py"
  timeout 60 "$ARB_PYTHON" "${flags[@]}" "$ROOT/verify_one_tenth.py"
done
printf '\nPASS_ONE_TENTH_REPLAY: rational series and Arb; handwritten geometry/reviews remain separate.\n'
