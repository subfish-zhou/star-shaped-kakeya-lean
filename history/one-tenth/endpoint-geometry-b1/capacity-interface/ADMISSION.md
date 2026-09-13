# Capacity-interface fixed-control admission

Parent admission: ../ADMISSION.md, campaign_id one-tenth-endpoint-geometry-20260905-b1.
Scope: analytic proof/interface audit; no LP, optimizer, grid, search, new geometric theorem from samples, or changes to baseline.

Target: derive the exact full-price fresh dyadic-tail coefficient, its one-tenth cutoff, and source-once feasibility gates for NEW low/finite-high kernels.
Current state: accepted terminal kernel is min(1/2,(m-r)_+)/(pi R); mixed low/high improvements are not admitted. The sharper ratio kernel is CONDITIONAL only.
Role: expose a necessary tail restriction and finite-high/source competition before any optimization is admitted.
Necessity/pure theory: all general conclusions are proved analytically. Computation only checks algebraic primitives and twelve preselected boundary/obstruction controls; it is not a proof search.
Algorithm: stdlib exact Fraction piecewise polynomial integration; one bounded SymPy simplification of already-derived identities. No quadrature or parameter loops beyond this fixed list and primitive pieces.
Budget: each arithmetic invocation timeout <=60 s, at most one concurrent; cumulative <=240 s. Planned one symbolic identity invocation plus normal/optimized checker replays, each expected <2 s. Stop on first timeout for an objective; no retry/reparameterization. Previous arithmetic in this lane: none.
Proof exit: human lemma plus exact reproducible arithmetic; any new union kernel remains explicitly conditional.
Success stop: formulas and source-capacity gates verified; no extra cases after success.
Failure stop: mismatch => correct analytic derivation, but no enlargement/search; missing universal geometry => OPEN.
Artifacts: this directory only, PROOF.md, checks.py, RESULTS.md.
Checkpoints: this preregistration precedes arithmetic; final results log actual execution and scope.

## Twelve fixed rational controls (exhaustive authorized list)

1. Fresh band R=3/4: uncapped collar branch, all r<1.
2. R=1: first branch seam.
3. R=5/4: r=1 crossing and cap below 1.
4. R=3/2: cap meets r=1.
5. R=8/5: recover accepted exact first-tail coefficient.
6. R=2: lower band endpoint meets r=1.
7. R=5/2: exact one-tenth threshold and saturation.
8. R=3: above-threshold reserve fraction.
9. R=5/2, truncated interval [3,4]: zero; [0,3] clips at R. These are one truncation-guard control.
10. Fixed old finite-high m=99/100,R=5/2: full-price old terminal ceiling; conditional ratio full and reserved ceilings; common endpoint-window obstruction.
11. Fixed conditional ratio two-tier split [99/100,3/2] and [3/2,5/2], source [0,5/4]: all-ones dual source competition.
12. R=8/5, prefix split at a=5/8: exact early-tail alternative and formula for maximal a (squared threshold 21/50), showing the half-band cutoff is architecture-specific.

Symbolic simplification of the three piecewise identities, monotonicity derivatives, and integral gate constants is separate from these fixed rational controls; it performs no sampling or search. Normal and optimized runs replay the same twelve controls, not twelve additional inputs.
