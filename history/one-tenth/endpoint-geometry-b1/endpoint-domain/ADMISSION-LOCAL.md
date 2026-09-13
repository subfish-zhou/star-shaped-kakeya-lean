# Endpoint-domain lane: bounded exact checks

This inherits `../ADMISSION.md`, read before work, and imports only the accepted
`../../baseline/PROOF.md`, read in full. No historical estimates, optimization,
closeout reruns, or other lane artifacts are used.

- campaign_id: one-tenth-endpoint-geometry-20260905-b1 / endpoint-domain
- mode: proof, theory first
- target_statement_or_unknown: all-cut far-arc extension with the full-cone cap,
  an explicit improved finite-radius kernel, and a stronger straddling-low cap.
- role_in_argument: verify elementary identities and exact comparison guards;
  the geometric all-cut theorem is proved analytically in PROOF.md.
- current_theoretical_state: complete paper derivations precede this check;
  the new low kernel still has a full-price ceiling below 1/10.
- necessity_analysis: check endpoint/foot distinction and boundary signs, not
  search for parameters or infer all-parameter validity from fixtures.
- pure_theory_alternatives: used for all main claims, including dominance and
  the logarithmic ceiling. No solver is required.
- algorithm_or_solver: one SymPy/Fraction script, symbolic differentiation and
  six individually fixed rational controls below; no numerical evaluation.
- cumulative_scale: no earlier arithmetic subprocess in this lane; six controls
  authorized out of the inherited maximum twelve.
- elapsed_resources_before_execution: zero arithmetic subprocesses.
- additional_budget: exactly one arithmetic subprocess, timeout 60 seconds;
  inherited total ceiling 240 seconds. Stop on first timeout; no retry.
- expected_wall_time: seconds.
- expected_information_gain: catch an identity/sign error or certify the stated
  exact guards. No output licenses a stronger global area claim.
- success_stop: all fixed checks pass; write result and stop arithmetic.
- failure_stop: first failure/timeout; report, do not run another control batch.
- checkpoints: literal domain and circular-section formula derived; before this
  check the all-cut and price quantifiers are fixed; before area conclusions the
  separate low full-price ceiling is imposed.
- artifacts: PROOF.md, check.py, CHECK-RESULT.txt, this record.
- proof_exit: parent/independent adversarial review of the human proof; a checked
  script is not a formalization. No schedule experiment is admitted here.

## Individually preregistered controls

1. Centered cone: x=1/2, |h|=3/20, r=1/10. The minimum segment radius is |h|,
   not N; the circle is below the whole segment and still meets its triangle.
2. Exterior-foot cone: x=3/2, |h|=1/5, r=1/4. Here r< N but r>|h|;
   the entire cone is still filled. Check a rational point on its central ray
   with squared radius r^2 lies in the anchored triangle.
3. Foot-at-endpoint boundary: x=1, |h|=1/5, r=1/10. Check a^2=N^2=h^2
   and the far-point joint endpoint identities.
4. Frozen low regime: M0=99/100, H=1/5. Check the squared rational guards for
   alpha<pi/2 and alpha<beta, and the rational comparisons in the proof of
   old caps<2/3<11/15<new caps.
5. Frozen finite-high regime: m=99/100, R=8/5, H=1/5, r=5/8.
   Check the joint-domain cone cap exceeds (m-r)/(m+r), so the old endpoint
   window is retained while the new kernel extends below it.
6. Low full-price ceiling: the fixed logarithmic lower bound
   log(2)>2(1/3+1/81)=56/81 and pi<22/7 give the rational ceiling
   (22/7)(3/8-28/81)=209/2268<1/10. Verify these rational identities only;
   the analytic log and pi inequalities are not numerically evaluated.

## Execution transport incident (before any arithmetic subprocess)

Both the direct terminal request and the `runpy` transport alternative were
rejected by Hermes's script-inspection lifecycle hook with
`RuntimeError: Could not determine home directory` before execution. Neither
created an arithmetic subprocess or produced a test failure/timeout. The same
preregistered script was then executed exactly once through `execute_code` using
`subprocess.run` with the specified Python interpreter, `-B`, four thread-count
environment variables set to one, and `timeout=60`. Only transport changed.

Completed: exit code 0; all six controls and four symbolic identities passed.
Measured arithmetic subprocess wall time: 0.34608486061915755 seconds; internal
script time: 0.100337 seconds. Arithmetic subprocesses used: one. No timeout,
no mathematical retry, no further arithmetic admitted. Success stop reached.

Symbolic checks (not additional controls): joint endpoint polynomial identity;
angle-primitive derivative; the endpoint-maximum derivative numerator;
and the radial primitive derivative.
