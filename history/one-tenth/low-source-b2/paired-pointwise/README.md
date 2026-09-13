# B2 paired-pointwise result

**PL FALSE — exact realizable positive-measure counterexample.**

At r=1/4 the Borel family in `COUNTEREXAMPLE.md` has

- `|V|=43/1000`;
- actual physical section `S_r(V)=[0,1/100] union [pi+1/40,pi+7/200]`;
- `|S_r(V)|=1/50 < 43/2000 = min(11/15,1-2r)|V|`;
- exact violation margin `3/2000`;
- unit chords, one common center, `|h|<1/5`, `M<99/100` for every q in V;
- both central lobes realized by the two actual endpoints on fixed physical rays; near endpoints in the exterior families are genuinely below r, not discarded.

The central two-lobe chords fill a positive-measure gap in the direction cut while adding no angle outside the two existing physical hosts. Cross-label overlap, including overlap of differently named endpoints, is included before measuring. No artificial independent arc pairs or finite-point cuts are used.

## Artifacts

- `COUNTEREXAMPLE.md`: theorem and complete uniform analytic proof of exact unit realization and literal union equality.
- `ADMISSION-LOCAL.md`: one fixed control, preregistered before execution.
- `check.py`: minimal rational-margin and polynomial-identity replay; no trigonometric numerical sampling.
- `CHECK-RESULT.txt`: real normal and optimized execution output; both PASS.

## Execution ledger and stop rule

- Base SHA: `d9a3f3c1b9718fd68b9f95cf10bb2cdd32bb16da`.
- B1 inherited control count: 25 distinct controls (its replay history remains upstream).
- This lane: **1 new fixed control**, **2 executions** of the same fixture, total arithmetic subprocess wall time **0.049974 seconds**.
- No optimizer, grid, scout, LP, SMT, numerical quadrature, or parameter tuning.
- The first certified literal counterexample ended all PL candidate work. The second execution is only assertion-disabled artifact verification.
- Files changed only in this directory; accepted sources unchanged. Local commit only, no push.

## Mathematical boundary

This refutes PL, not IL. An independent IL proof may still close the conditional bridge. No new universal area bound or counterexample to area 1/10 is claimed. B1 theorems and the retained global lower bound are untouched. The analytic proof is ready for independent parent review; the rational checker does not replace that review.
