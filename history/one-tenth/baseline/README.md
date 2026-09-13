# Replaying the seven-row lower bound

Start with [PROOF.md](PROOF.md). It retains the exact public floor
**0.082812499999972190** for arbitrary star-shaped unit-chord Kakeya outer area.
The only arithmetic input is the tiny [witness.json](witness.json); the radial
table is explicit in the proof and reconstructed in `verifier.rows`.

## One runner, no writes

Verified environment: Python 3.11.15, python-flint 0.9.0; Arb precision 192 bits.
The approved interpreter is the one named in `../ADMISSION.md`.
From any working directory run (each process is bounded to 60 seconds):

```sh
PYTHONDONTWRITEBYTECODE=1 timeout 60 /home/argustest/research/star-kakeya-wt-exact-ray-envelope/.venv/bin/python -B /home/argustest/research/star-kakeya-wt-01-short-baseline/research/one-tenth/baseline/run.py
PYTHONDONTWRITEBYTECODE=1 timeout 60 /home/argustest/research/star-kakeya-wt-exact-ray-envelope/.venv/bin/python -B -O /home/argustest/research/star-kakeya-wt-01-short-baseline/research/one-tenth/baseline/run.py
```

After integration, change only the absolute package path. The interpreter needs
python-flint; all other imports are standard-library or the two local modules.
Neither replay reads the original archive or Git, invokes an optimizer, nor
rewrites a witness/receipt. `-B` prevents bytecode cache writes. The runner
rejects zero or changed test discovery counts, and reports deterministic stdout:

```text
PASS: 7 focused tests
PASS: 7 fixed rows; exact maximum source load = 1
Arb precision: 192 bits
PASS: low > 0.082812499999972190
PASS: positive+terminal > 0.082812499999972190
PASS: pole+terminal > 0.082812499999972190
PASS: first-tail > 0.082812499999972190
PASS: later-tail > 0.082812499999972190
Paper + outward arithmetic only; no Lean claim.
```

Both normal and optimized replay returned exit 0 and byte-identical stdout.
The tests cover: exact source saturation plus a 10⁻³⁰ overload; changed price;
changed arithmetic; seven exact row loads; rejected float/boolean inputs and
lowered target; exact tail seams and zero intervals; all five branch receipts
and rejection of missing branch coverage. Critical checks use exceptions and
unittest methods, never removable Python `assert` statements.

## What was checked, and what was not

* The source-overload, wrong-price and wrong-arithmetic tests were each observed
  RED before their implementation, then GREEN. The remaining tests lock the
  frozen witness and explicit tail/branch identities. In-memory mutation controls
  also disabled each of the three load-bearing guards without changing files:
  source overload was killed by 1 failing test, wrong price by 2, and wrong
  arithmetic by 1, identically in normal and `-O` modes.
* Endpoint support and rational load checks use `Fraction` throughout. Arb is
  only used for outward elementary functions and strict bound comparisons;
  summing rounded rational Arb balls is not used to establish a unit load.
* The original 132-cell witness was read from its immutable Git object and
  coalesced using exact Fractions; it is exactly the seven live rows plus a
  zero suffix. [PROVENANCE.md](PROVENANCE.md) records that separate comparison.
* Geometry, Borel recovery, polar integration and the countable source sum are
  the human proof's responsibility. This is not a proof-assistant certificate,
  not an independent formal verification, and not a proof of optimality.
* Work follows the existing one-tenth Stage 1 admission: fixed witness only,
  no parameter search, tiny exact/Arb checks, ≤60 seconds per process. The exit
  is the closed proof and local commit, not a larger numerical campaign.

The old normalized tree, admission, other closeout lanes and 0.25 research were
not modified. No publication or push is part of this deliverable.
