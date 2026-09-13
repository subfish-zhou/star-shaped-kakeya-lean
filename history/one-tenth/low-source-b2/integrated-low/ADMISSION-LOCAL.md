# Integrated-low local admission

campaign_id: one-tenth-endpoint-geometry-20260905-b1
round: b2-low-source / integrated-low
base: d9a3f3c1b9718fd68b9f95cf10bb2cdd32bb16da
mode: analytic proof with tiny fixed exact controls

Read first: ../ADMISSION.md; ../../ADMISSION.md; ../../endpoint-geometry-b1/CONDITIONAL_TENTH_BRIDGE.md; accepted endpoint-domain/PROOF.md.

## Theory before arithmetic

New candidate: count *actual eligible endpoint anchors*, not one source copy per triangle lobe. For a threshold m select each endpoint whose radius is at least m. Their ideal anchors form disjoint physical lifts of direction subsets. A single application of the accepted interval-union lemma to ALL their real circular bases gives a bound proportional to the endpoint-count measure E(m). For low chords, E(2/5)>=|L|+|B|, E(1/2)>=|L|, E(3/5)>=|L|-|B|, where B={N>=2/5}. Cone caps must be included. This is a potentially stronger integrated method than the common-uniform single-far kernel.

Preregistered control 1 (only control presently admitted): evaluate the three fixed disjoint radial banks [0,1/5], [1/5,7/20], [7/20,1/2] using thresholds 2/5,1/2,3/5 respectively. Use the rigorously justified conservative two-endpoint cone cap 2/3 in the first bank. The later banks are above all heights and need no cone cap. Report the two endpoint-class coefficients 2*C4+C5 and C4+C5+C6 relative to 1/(10*pi). This control tests this exact fixed certificate ONLY. Failure stops this fixed certificate, not the general endpoint-threshold theorem. No parameter sweep or optimization will follow a failure.

## Resources and interpretation

Historical B1 controls: 25 distinct, inherited and not rerun. Local before execution: 0 controls, 0 arithmetic subprocesses, 0 seconds. Lane hard limit: <=8 distinct fixed controls, each subprocess <=60 seconds, total arithmetic <=180 seconds, one at a time. Current authorization: one control and one execution, expected <5 seconds. Use approved SymPy Python with -B, thread counts 1; no bytecode, no solver, search, grid, LP, SMT, random scout, numerical optimization or broad quadrature.

Necessity: human algebra already proves the proposed eligible-anchor measure identity and fixed integrals; tiny arithmetic determines whether this particular fixed bank closes IL or only yields an intermediate theorem. Logarithms will be bounded by their positive atanh series with an explicit geometric tail; pi by 223/71<pi<22/7. Any decimal is diagnostic only. A failure or timeout stops this fixed certificate immediately. Completion consists of a human proof of the actual endpoint-count theorem, plus either a valid IL certificate or an explicit OPEN gap. No samples establish a continuum union theorem.

## Checkpoint after control 1; distinct new source-once candidate

Control 1 executed once in 0.001318 seconds (script clock). Its exact fixed pure-price certificate fails on the balanced coefficient; it is retired. This was not a literal geometric counterexample. No threshold or radial breakpoint is changed, and no search or optimization is admitted.

Theory repair: on the already-fixed outer bank [7/20,1/2], the accepted far-radius-1/2 estimate pays ALL directions; denote its integral by D5. Split this same bank at prices lambda=C4/C6 for the far-radius-3/5 U subfamily and 1-lambda for all directions at threshold 1/2. This is an algebraically specified cancellation, not a numerical weight search: the B coefficient is C4-lambda*C6=0. The resulting common coefficient is C*=2*C4+C5+(1-C4/C6)*D5. Prices are admissible exactly when 0<C4<C6. Unlike the retired certificate, the all-direction reserve stays available in the outer bank. All thresholds and radial boundaries remain those preregistered in control 1.

Preregistered control 2: check 0<C4<C6; evaluate D5=integral_[7/20,1/2] r(1/2-r)/(1/2+r)dr; prove C*>637/20000>71/2230>=1/(10*pi), and verify the exact cancellation formula and the rational pi-margin 637*(223/71)/20000-1/10. The final replay also checks the four closed-form polynomial constants and logarithm ratios against these same already-fixed integrals (not new control points). No other parameter or control point is admitted. Expected <5 seconds. Run final checker normally and with -O, counted separately. This control is a tiny exact verification of a prederived complete source-once theorem, not evidence replacing its continuum proof. If it fails or times out, stop this new certificate without adjustments.

## Completion

Status: completed; new mixed certificate and full continuum IL proof written in PROOF.md, pending independent review. The failed pure-price precursor is retained as a method failure only. Success stop triggered: no further mathematical controls or tuning.

Actual local budget: 2 distinct fixed controls; 4 arithmetic launches including both final normal/optimized replays. Cumulative in-script arithmetic time 0.007017 seconds. Final two tool calls together 0.096838 seconds wall; earlier interpreter startup was not separately clocked. All launches used timeout 60s, -B, thread counts 1, and returned without timeout. Historical B1 25 controls remain untouched. Exact output is in CHECK-RESULT.txt.

One Markdown closed-form typo for D5 was corrected from 109/800 to 69/800 before the final two runs; the checker independently verifies all four polynomial constants and logarithm ratios. No mathematical control failed after the source-once complementary-price repair.

Writes only in this subtree; local commit only. No accepted source edits, old campaigns, 0.25 work, or Lean.
