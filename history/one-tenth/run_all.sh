#!/usr/bin/env bash
# Arithmetic/finite-map replay only; does not promote candidate root accounting.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
ARB_PYTHON="${ARB_PYTHON:-/home/argustest/research/star-kakeya-wt-exact-ray-envelope/.venv/bin/python}"
SYMPY_PYTHON="${SYMPY_PYTHON:-/home/argustest/.hermes/hermes-agent/venv/bin/python}"
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
for mode in normal optimized; do
  flags=(-B)
  if [[ "$mode" == optimized ]]; then flags+=(-O); fi
  printf '\n=== %s ===\n' "$mode"
  timeout 60 "$ARB_PYTHON" "${flags[@]}" "$ROOT/baseline/run.py"
  timeout 60 "$SYMPY_PYTHON" "${flags[@]}" "$ROOT/separator/run.py"
  timeout 60 "$SYMPY_PYTHON" "${flags[@]}" "$ROOT/rootmap/check_rootmap.py"
  timeout 60 "$SYMPY_PYTHON" "${flags[@]}" "$ROOT/rootmap/test_rootmap.py"
  timeout 60 "$SYMPY_PYTHON" "${flags[@]}" "$ROOT/test_closeout.py"
  timeout 60 "$SYMPY_PYTHON" "${flags[@]}" "$ROOT/verify_closeout.py"
done
printf '\nPASS_CLOSEOUT_REPLAY: reviewed scoped roots=34/441; continuum 0.1 remains unproved.\n'
