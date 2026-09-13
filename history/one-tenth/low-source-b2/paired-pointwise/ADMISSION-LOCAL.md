# Paired-pointwise lane: exact literal two-host counterexample admission

campaign_id: one-tenth-endpoint-geometry-20260905-b1
mode: proof / exact falsification only
target_statement_or_unknown: PL at r=1/4 on a positive-measure Borel cut, with actual two endpoints and physical angular union.
role_in_argument: Refute the sufficient pointwise candidate only; IL remains independent.
current_theoretical_state: Accepted B1 section formula. A hand-derived two-host family has tangent-limit source length 2 epsilon and direction length (43/10) epsilon. The exact trigonometric lift below has a strict margin.
necessity_analysis: No numerical exploration is needed. One fixed rational control verifies the elementary rational margins and polynomial identity in the fully specified analytic lift. It is not a search or a general proof by sampling.
pure_theory_alternatives: Scalar endpoint addition does not control the union. The construction instead fills the gap between two individually expanded hosts by chords joining their inner endpoint rays; the near lobe lands in the other existing physical host.
algorithm_or_solver: Python Fraction and (optionally) SymPy exact arithmetic, no optimization, grid, scouts, LP, SAT, SMT, or numerical quadrature. Analytic sine/tangent bounds prove the continuum inclusions uniformly.
cumulative_scale: B1 inherited 25 distinct controls (6+7+12), with its earlier replays retained upstream. B2 paired-pointwise lane: zero prior arithmetic executions; exactly ONE new fixed control registered here.
elapsed_resources: 0 arithmetic subprocess seconds in this lane before registration.
additional_budget: At most 8 new controls authorized, but this lane admits just 1. Each arithmetic subprocess <=60 seconds; cumulative <=180 seconds; one arithmetic subprocess at a time. Normal and optimized replays, if used, are executions of the same fixed control.
expected_wall_time: under 5 seconds per tiny exact replay.
expected_information_gain: PASS verifies the rational guards supporting the analytic realizability lift; FAIL blocks this construction. No output is interpreted as a universal PL proof.
success_stop: Stop work on PL immediately after exact realizable counterexample is certified. Complete only documentation, replay, and local commit.
failure_stop: A timeout stops this symbolic objective; do not switch parameters and repeat. No parameter tuning after a failed check.
checkpoints: One fixed-control execution, then verification/readback and commit.
artifacts: This directory only: COUNTEREXAMPLE.md, check.py, CHECK-RESULT.txt, README.md.
proof_exit: A theorem giving S_{1/4}(V)=A union B, |S|=2 epsilon < (1/2)|V|=(43/20)epsilon, with all chords unit, Borel, height<=1/5, and M<99/100.

## Completed checkpoint (appended after execution)

status: completed; first literal counterexample found, PL candidate work stopped.
actual_new_controls: 1 (B2-PL-01)
actual_executions: 2 (normal and optimized replay of the same fixed control)
actual_arithmetic_wall_seconds: 0.049974 total (0.024552 + 0.025422)
actual_result: Every rational guard passed; exact defect 3/2000. The continuum proof is in COUNTEREXAMPLE.md, not inferred from finite sampling.
remaining_work: independent parent review only; no further PL exploration authorized or performed.

## The sole registered fixed control

Set epsilon=1/100, r=1/4, far-only longitudinal length a=4/5, outer halo delta=2/5, host separation d=5/2, gap g=d-1=3/2. Physical hosts are A=[0,epsilon] and B=[pi+(5/2)epsilon,pi+(7/2)epsilon]. The cut is V=[-(2/5)epsilon,(39/10)epsilon] modulo pi. Piecewise family:

* q/epsilon in [-2/5,7/5]: one far endpoint aimed at the nearest point of A, longitudinal a=4/5; near radius<r.
* q/epsilon in [7/5,21/10]: the actual unit chord between rays epsilon and pi+(5/2)epsilon.
* q/epsilon in [21/10,39/10]: the analogous one-far-endpoint family for B, with oriented far direction q+pi.

Uniform bounds to check: tan(eta)<=eta/(1-epsilon^2) for eta<=delta epsilon; sin(eta+epsilon)>=(eta+epsilon)(1-epsilon^2); (16/5)delta < (1+delta)(1-epsilon^2)^2. Far-only h<epsilon and M<99/100, N<r. For central chords, let w=min(u,v), u+v=3/2, 2/5<=w<=3/4. The identity

(1+w)/4 - (2/3)w(3/2-w) = (2/3)(w-9/16)^2 + 5/128

and 5/128 > (7/8)epsilon^2 prove both lobes remain in their hosts. Endpoint bounds use sin(g epsilon)>=g epsilon(1-epsilon^2); check M <= (11/15)/(1-epsilon^2) < 99/100, N >= ((2/5)/(3/2))(1-epsilon^2)>1/4; h <= (3/8)epsilon/(1-epsilon^2)<1/5. Finally |V|=(43/10)epsilon and the strict PL defect is (3/20)epsilon.
