# Admission: arbitrary-selector endpoint geometry for the one-tenth target

campaign_id: one-tenth-endpoint-geometry-20260905-b1
mode: proof (analytic derivation with tiny fixed exact controls; no numerical search)
target_statement_or_unknown: Does retaining the realizable joint endpoint data and full radial filling yield a strictly stronger arbitrary-selector all-cut source estimate than the frozen low/terminal kernels, with credible capacity to reach outer area 0.1?
role_in_argument: First new geometric lemma after accepted short closeout; not completion of the centered C2+C5 atlas.
current_theoretical_state: Closeout e90b49191092738ad4efc1ef1e454e8acc66804c retains universal paper/Arb floor0.082812499999972190 and scoped34/441. Fixed H=1/5,M0=99/100 old low kernel has full-price ceiling below0.1. No new universal kernel or bound is yet certified.
necessity_analysis: Need source-level all-cut statements before any schedule optimization. Restoring actual unit-chord constraints may help; they are known identities, not automatically a new theorem. Exact controls distinguish wrong geometry or impossible payment from a useful derived estimate.
pure_theory_alternatives: This IS the theory-first replacement for enlarged scalar menus and generic guard boxes. Numerical optimization of the old fixed kernels is expressly excluded.
algorithm_or_solver: Hand derivation, exact Fraction/SymPy identities and fixed Arb comparisons only; no optimizer, random/grid scout, LP/MILP, CAD, SMT, interval cover or Lean build.
cumulative_scale: This is not a restart of any old scout or cell campaign. Prior old campaign budgets remain consumed/frozen. New batch authorizes at most12 individually preregistered rational controls per lane (36 total), no search loops; deterministic simplification of derived identities is separate.
elapsed_resources: No Stage2 numerical evaluation performed before this admission.
additional_budget: Three independent lanes; every arithmetic subprocess <=60seconds, <=240seconds cumulative arithmetic wall per lane, <=1 arithmetic subprocess per lane. Stop after one timeout at the same symbolic objective, do not reparameterize and retry within this batch.
expected_wall_time: One bounded reasoning batch; arithmetic is intended to be seconds, not the main work.
expected_information_gain: Either one explicit valid improved all-cut inequality and its exact domain, or a decisive literal obstruction/quantifier gap showing why a proposed improvement fails. Mere restatement or more digits is not a successful geometric result.
success_stop: A complete analytically derived candidate with a strict improvement regime, or the first exact counterexample to that candidate; stop calculation and write the proof/obstruction.
failure_stop: Budget reached, missing source-once step, numerical search needed, or equivalence to the old lossy bound without a new estimate. Return explicit OPEN/BLOCK, not a renamed lemma.
checkpoints: At domain derivation, before every nontrivial control, and before any claim about composition or area0.1.
artifacts: Separate endpoint-domain/, coupled-arcs/, and capacity-interface/ subdirectories under research/one-tenth/endpoint-geometry-b1/ in isolated worktrees; local commits only.
proof_exit: Parent checks literal geometry and arithmetic, independent adversarial review before accepting a new universal estimate. Only afterward admit a small schedule experiment if the proven estimate can actually change the target.

## Literal domain and known identities to retain

Let selected unit chords be `(s-1/2)u+h n` to `(s+1/2)u+h n`, with one common star center0 and arbitrary direction-indexed s,h. For a prospective contradiction below area0.1, every selected triangle has |h|<1/5. Use the open-cover/Borel-recovery interface already proved in baseline/PROOF.md, rerunning the height dichotomy after recovery. No measurable or continuous original selector is assumed.

For far/near endpoint radii M,N:

- `sqrt(M^2-h^2)=|s|+1/2>=1/2`, so `M^2-h^2>=1/4`;
- `N^2=M^2+1-2sqrt(M^2-h^2)`;
- when M<1, the chord straddles its perpendicular foot;
- minimum radius along the whole chord is not always N: it is |h| if |s|<=1/2 and N otherwise.

These constraints must not be independently relaxed without a stated direction and cost. Physical source is the literal triangle union in E, not a sum of triangle masses or a free symmetrization. Far-lift choices, antipodal copies and RP1 normalization must be accounted exactly.

## Three independent questions

1. Endpoint-domain lane: reconstruct actual circular sections and endpoint/height coupling, derive uniform Borel-cut lower kernels on jointly feasible regimes; compare to old endpoint-window and low estimates. Identify whether radial filling below the closest segment radius gives usable payments. No pointwise-per-label bound may be integrated as an all-cut union theorem without proof.
2. Coupled-arcs lane: attempt a stronger single physical-union estimate retaining both endpoint lobes/ideal anchors or variable-length terminal collars. Test the candidate improvement `inf_M min(1/2,(M-r)_+)/M` versus taking minimum numerator and maximum denominator independently. It is a candidate to prove or refute, not an admitted theorem. Avoid moving infima through integrals or summing repeated source banks.
3. Capacity-interface lane: audit what a new low estimate would actually need to close0.1, including the unchanged first-tail obstruction and the finite-high source budget. Derive analytic necessary/sufficient gates without optimizing prices. In particular, determine the exact cutoff requirement for full-price fresh dyadic-tail area coefficient; a better low branch alone may still leave the high/tail bottleneck.

## Non-goals and isolation

No 0.25 research or edits. No C2+C5 residual sweep. Do not modify accepted closeout or original artifacts. Each worker writes only its own absolute-path subtree, commits locally, never pushes, and leaves the candidate's missing universal steps explicit.
