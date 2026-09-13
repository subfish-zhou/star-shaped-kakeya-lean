# Coupled-arcs lane: fixed replay admission

campaign_id: one-tenth-endpoint-geometry-20260905-b1 (coupled-arcs lane)
mode: proof; pure geometric proof with a tiny deterministic arithmetic replay
base: 8a710b938769f984bd5c3b775de42ed98a4a9454
owned_path: research/one-tenth/endpoint-geometry-b1/coupled-arcs/
target_statement_or_unknown: For arbitrary selected unit chords with common star center, m<=M<=R, prove the physical circular-section coefficient inf_M min(1/2,(M-r)_+)/M, with the original factor 1/pi.
role_in_argument: Improve the accepted direct terminal-collar all-cut estimate, not the low endpoint kernel or a new global area floor.
current_theoretical_state: The component proof can use a uniform lower bound on each collar's length/radius ratio. The ratio increases before its clipping point and decreases afterwards. No source allocation or numerical search is needed.
necessity_analysis: The theorem is proved analytically; exact arithmetic only catches transcription errors in its branch formula, strict/equal boundaries, and a fixed old-price gain. These tiny deterministic checks are not a finite-case proof of the geometry.
pure_theory_alternatives: Used as the main argument: connected angular collars, open-component covering, and elementary piecewise monotonicity. No solver or large computation admitted.
algorithm_or_solver: Python standard-library Fraction; fixed inputs, explicit expected outputs, exact polynomial antiderivative; no grid, adaptive points, optimizer, CAS or quadrature.
cumulative_scale: No prior arithmetic in this lane. Six individually fixed rational kernel controls below, plus one fixed rational integral identity (seven controls total, below the lane limit twelve). Normal and optimized replays repeat the same controls, not new inputs.
elapsed_resources: Zero arithmetic subprocess wall before this admission.
additional_budget: At most two sequential arithmetic subprocesses, each hard timeout 60 seconds; cumulative <=240 seconds; concurrency one. Stop this objective on the first timeout. Intended cumulative wall below two seconds.
expected_wall_time: Less than one second per replay; only fixed rational operations.
expected_information_gain: A mismatch blocks the written formula or replay until analytically diagnosed. Success verifies transcription only; the universal proof remains human mathematics.
success_stop: Both fixed replays pass; write result, inspect scoped diff, and commit locally.
failure_stop: First timeout, any need for numerical search, or a missing union-level proof. No expanding the experiment.
checkpoints: Domain and union proof derived before this admission; inspect output after each replay and audit scope before committing.
artifacts: PROOF.md, replay.py, REPLAY.md in the owned subtree.
proof_exit: A complete universal all-cut joint-collar lemma with its exact comparison region; parent independently reviews before promoting it to a new schedule.

## Preregistered controls

Write pi*k_old=min(1/2,(m-r)_+)/R and pi*k_joint=min(1/(2R),(1-r/m)_+).

1. (m,R,r)=(1,2,1/3): old=joint=1/4 (old plateau).
2. (1,2,1/2): old=joint=1/4 (strict-improvement boundary).
3. (1,2,3/4): old=1/8, joint=1/4 (new switching boundary).
4. (1,2,7/8): old=1/16, joint=1/8 (both descending).
5. (1,2,1): old=joint=0 (support boundary).
6. (1,1,3/4): old=joint=1/4 (collapsed M interval).
7. Fixed accepted finite-high window m=99/100, R=8/5: joint switching radius exceeds 5/8. On [49/100,5/8], the accepted terminal price is one and its pi-scaled payment gain is exactly (1/R)*integral r*(r-49/100) dr. Compare endpoint evaluation of r^3/3-(49/100)*r^2/2 with the independent substitution d=5/8-49/100, giving [(49/100)*d^2/2+d^3/3]/R. No new price is chosen and no other baseline payment is recalculated.
