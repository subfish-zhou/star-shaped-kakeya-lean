# Completed analytic capacity audit — reproducibility and status

Base: `8a710b938769f984bd5c3b775de42ed98a4a9454`.
Owned path only: `research/one-tenth/endpoint-geometry-b1/capacity-interface/`.
Baseline proof, verifier, prices, accepted floor and other lanes unchanged.

## Delivered conclusions

* Full-price dyadic half-band coefficient is the four-piece exact formula in
  PROOF.md Lemma 1. It reaches 1/10 iff R>=5/2. At equality its first band
  is saturated; improving only low cannot repair the old 53/640 tail.
* Cutoff scope is explicit: R=8/5 can instead start its tail at 5/8, paying
  419/4096, but this takes away the complete old finite-high endpoint window.
* At R=5/2 the old whole finite-high endpoint window has no common N<r<M
  support; old full terminal payment is 17053/300000<1/10.
* Even CONDITIONAL validity of the proposed common ratio kernel only gives
  199287/2500000<1/10 at full price. A fixed two-tier ratio split has
  all-ones dual capacity 691507/3750000<1/5, before spending on low.
* Lemma 2 is an exact necessary/sufficient source-price feasibility condition
  for any finite menu of NEW valid physical-union kernels. Equations
  (17)–(19) give fixed reserve or mixed-cut sufficient targets. No missing
  union theorem is silently inferred from per-label geometry.

## Exact replay

Run from the assigned repository root (no install, no generated files):

```sh
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  timeout 60s /home/argustest/research/star-kakeya-wt-exact-ray-envelope/.venv/bin/python \
  -B research/one-tenth/endpoint-geometry-b1/capacity-interface/checks.py
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  timeout 60s /home/argustest/research/star-kakeya-wt-exact-ray-envelope/.venv/bin/python \
  -B -O research/one-tenth/endpoint-geometry-b1/capacity-interface/checks.py
```

Both final runs returned exit code 0, `status: PASS`, twelve fixed controls.
Their internally measured exact arithmetic times were
0.0009162146598100662 s and 0.0009213229641318321 s. The code uses explicit
exceptions rather than assertions, and no numerical search or quadrature.
It is standalone standard-library Fraction arithmetic; the named interpreter
is the authorized environment, not an external baseline runtime dependency.

Exact fresh-tail outputs in the preregistered order:

| R | A(R) |
|---|---|
| 3/4 | 3/128 |
| 1 | 1/24 |
| 5/4 | 119/1920 |
| 3/2 | 5/64 |
| 8/5 | 53/640 |
| 2 | 3/32 |
| 5/2 | 1/10 |
| 3 | 5/48 |

The checker also verifies empty/upper-truncated bands, the exact old and
conditional finite-high integrals, reserve weighted means 4/5 and 2000/7301,
the conditional two-tier deficit 58493/3750000, and the old-cutoff early-tail
threshold a²<=21/50. It does not establish the conditional ratio geometry.

## Admission/resource closeout

Status: **completed**; success stop reached, no extension or optimization.
One bounded SymPy invocation simplified the already-derived branch primitives,
derivatives, and ratio integral. Two normal/optimized pairs replayed the same
fixed controls (the first pair preceded a small checker cleanup). All three
foreground arithmetic tool calls used timeout 60 seconds; no timeout occurred,
no calls were concurrent, and the cumulative 240-second limit was not approached.
No LP, grid, solver, search, campaign, baseline replay, or 0.25 work was run.

Audit note: the first replay additionally checked a redundant negative-lower-
radius clipping assertion within guard control 9. It was removed to match the
preregistered guard text before the final replay. No parameter exploration or
mathematical inference relied on it. The initial symbolic print for an
old-cutoff prefix used the already-truncated half-band integral; the final
proof correctly restores the omitted inner cap. Formula (6) is independently
checked against direct clipped integration in control 12.

`git diff --check` and the explicit baseline path comparison returned clean
before staging. Only the owned new directory was untracked. The final local
commit and clean status are reported in the handoff rather than self-pinned
inside this file.

## Remaining mathematical issue

OPEN: a new arbitrary-selector physical-union kernel theorem satisfying
PROOF.md (13) and the source gate (15), or the explicit fixed reserves (17),
or the mixed-cut alternative (19). A stronger low estimate by itself, or
just proving the proposed common ratio formula, does not complete 1/10.
