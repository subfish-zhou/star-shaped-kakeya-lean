#!/usr/bin/env bash
# Fetch the locked public dependencies and their upstream Mathlib cache.
# Compile the small pinned cache bootstrap one module at a time, never the
# StarKakeyaLower/Mathlib library aggregates. Requires elan, Python 3, Git, curl.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
export MATHLIB_NO_CACHE_ON_UPDATE=1
export RAYON_NUM_THREADS="${RAYON_NUM_THREADS:-4}"
python3 -c 'import json; from pathlib import Path; a=json.loads(Path("lake-manifest.json").read_text()); b=json.loads(Path("dependencies.lock.json").read_text()); assert a==b, "dependency manifest differs from release lock"'
# This explicit order is the complete non-toolchain Cache.Main import closure
# at the locked Mathlib/Batteries revisions. No simultaneous Lean builds.
for module in \
  Batteries.Data.Array.Match \
  Batteries.Data.String.Basic \
  Batteries.Data.String.Matcher \
  Cache.Lean \
  Cache.IO \
  Cache.Hashing \
  Cache.Init \
  Cache.Requests \
  Cache.Main
do
  lake build "$module"
done
lake exe cache get
