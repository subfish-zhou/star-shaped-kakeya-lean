#!/usr/bin/env bash
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$HERE/results"
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH="$HERE" python3 -m unittest discover -s "$HERE/tests" -v 2>&1 | tee "$HERE/results/test-output.txt"
PYTHONDONTWRITEBYTECODE=1 python3 "$HERE/paired_persistence.py" --output "$HERE/results/scout.json" | tee "$HERE/results/scout-output.txt"
