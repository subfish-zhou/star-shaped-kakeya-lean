# Shared-terminal strict certificate v2

Certified candidate parameters: H=1/5, M0=99/100, R=8/5. The v2 verifier checks the positive continuum, exact pole continuum, first tail, every later dyadic tail scale, and radial source load. The common price scale is normalized from `999999/1000000` to exactly `1`; this adds no geometric column and does not change the theorem menu.

The v1 three-point pole reduction is obsolete and must not be used. For h=0, v2 checks every event where M or M-1 crosses a radial-grid endpoint; between events the sliding-window receipt is concave, so event endpoints contain the minimum.

## Exact-tree replay

From the repository root, use the approved external Arb environment and gate
its lexical `sys.prefix` before replay:

```bash
PYTHON=/home/argustest/research/star-kakeya-wt-exact-ray-envelope/.venv/bin/python
EXPECTED_PREFIX=/home/argustest/research/star-kakeya-wt-exact-ray-envelope/.venv
test "$($PYTHON -c 'import sys; print(sys.prefix)')" = "$EXPECTED_PREFIX"
$PYTHON -B archive/shared-terminal-082812/reproduce_v2.py
```

That external venv is an execution-environment requirement providing
`python-flint`; it is not an artifact dependency. The replay code, witness,
receipt, and hash ledger are all tracked in this worktree, and the tests copy
only those tracked candidate artifacts into temporary directories.

Expected strict lower:

    pi*c >= 0.0828124999999721904111374192974978881...

The conservative public release floor is 0.082812499999972190. Hashes are frozen in `hash_ledger_v2.json`.
