# Evidence boundary

## Confirmed in this snapshot

- Paper-level strict theorem:

\[
\mathcal L_2^*(E)>\frac{100\pi}{5599}>\frac{\pi}{56}.
\]

- Exact rational parameter identities and Case I/Case II/height margins.
- Exact mutation controls that fail after a declared weakening.
- Independent 180-bit Arb fixed-parameter witness above \(100/5599\).
- Fresh-context adversarial audit of the complete paper proof.
- Successful compilation of all enclosed Lean modules before packaging, for the
  production target `lake build` (= `lake build +StarKakeyaLower`), the audit
  target `lake build StarKakeyaLowerAudit`, and the full library.
- An unconditional Lean theorem
  `StarKakeyaLower.universal_strong_lower_bound : UniversalStrongLowerBound`,
  i.e. `ofReal (π * 100 / 5599) < volume.toOuterMeasure E` for every
  star-shaped Kakeya set `E`.
- Axiom audit of the final theorem and of every audited component reporting only
  Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound`.

## Not confirmed

- No global optimum of the corrected one-threshold parameter family is proved.
- Numerical search output is not an analytic or computer-assisted global theorem.
- The cross-radius and multiscale/Bellman routes remain open.
- No publication, peer review, originality, or priority claim is made.

## Status vocabulary

`proved-draft` means the paper proof and its load-bearing analytic bridges are
closed locally and independently audited.  It does not mean the result has
been externally refereed.

`symbolic-proof` applies only to the literal exact algebra certified by each
script.  It does not by itself prove the geometric/measure-theoretic theorem.

`interval-candidate` applies to the fixed Arb witness.  It proves the displayed
fixed parameter lower bound, not a family supremum.

`open-exact-gap` records a named theorem-strength bridge rather than hiding it
behind a conditional theorem or numerical plot.  It no longer applies to the
universal Lean theorem, which is closed; it applies to the global optimum of the
parameter family and to the cross-radius/Bellman routes.
