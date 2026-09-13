#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$ROOT/results"
python3 "$ROOT/checker.py" | tee "$ROOT/results/checker-output.txt"
python3 "$ROOT/validator.py" | tee "$ROOT/results/validator-output.txt"
python3 "$ROOT/mutations.py" | tee "$ROOT/results/mutations-output.txt"
if [[ "${PAIRED_CFS_SKIP_TESTS:-0}" != "1" ]]; then
  python3 -m unittest discover -s "$ROOT/tests" -v 2>&1 | tee "$ROOT/results/test-output.txt"
  python3 -O -m unittest discover -s "$ROOT/tests" -v 2>&1 | tee "$ROOT/results/test-opt-output.txt"
fi
