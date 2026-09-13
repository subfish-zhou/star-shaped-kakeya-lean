# Star-shaped Kakeya lower-bound campaign — current state

Provider: `[Codex]`

Date: 2026-07-31

## Hard verdict

- Campaign terminal state: `theorem-closed / optimum-open`.
- Strongest universal paper theorem:

\[
\mathcal L_2^*(E)>\frac{100\pi}{5599}>\frac{\pi}{56}.
\]

- Paper status: `proved-draft`, confirmed by a fresh-context adversarial
  audit.
- Universal Lean theorem: `proved`.  `StarKakeyaLower.universal_strong_lower_bound
  : UniversalStrongLowerBound` is unconditional, with the standard axiom
  footprint `propext, Classical.choice, Quot.sound`.
- Global optimum of the corrected one-threshold family: `open`.
- Beyond-framework cross-radius and multiscale improvements:
  `open-exact-gap`.
- No theorem-library result is registered.

The four evidence axes are:

- `mathematical_status`: the strict \(100\pi/5599\) theorem is
  `proved-draft` on paper and `proved` in Lean; the global family optimum
  remains open;
- `evidence_type`: analytic geometry and outer-measure proofs, exact symbolic
  certificates, an independent Arb fixed witness, numerical scouting kept
  separate, and a complete Lean formalization of the lower-bound theorem;
- `project_status`: `theorem-closed / optimum-open`;
- `originality`: not established and not claimed.

## Source and correction record

The load-bearing primary source is Shaoqi Li,
*An Improved Lower Bound for Star-Shaped Kakeya Sets*,
arXiv:2509.05711v2, 29 May 2026, published in
*Annales Fennici Mathematici* 51 (2026), 377--392,
DOI `10.54330/afm.185132`.

The read-only local PDF is
`../star-shaped-kakeya-upper-bound/sources/li-2026.pdf`, with SHA-256
`294b1f852bea222b4331d78fbe2a55617367f40e3b9e9da4737ba284448c87c8`.
Li proves \(\pi/98\), not \(\pi/56\) or \(100\pi/5599\).

The project audit found and repaired four load-bearing issues:

1. Li's Vitali factor \(3\) can be removed by an arbitrary-family
   same-centre circle-dilation theorem.
2. The actual endpoint statement is

\[
J_\Gamma
\subset
D_{g(r)}^\pi(q(\theta_\Gamma)),
\qquad
q:\mathbb T_{2\pi}\to\mathbb T_\pi.
\]

3. The sliced set required by Lemma 2.5 is

\[
E_{\rm all}=\bigcup_\alpha\Delta_\alpha,
\]

not a smaller confined-direction union.
4. Directly citing Li Theorem 3.5 at \(\rho>1/2\) is outside its printed
   Section 3 scope.  A new projective-angle separation, epsilon-greedy
   selection, residual radial fan, and two-bound minimax proof supplies the
   corrected parametric theorem.

The direct iteration suggested in Li Remark 4.1 remains blocked: the confined
direction family pays \(p\) times the baseline and does not justify the
printed full-direction recurrence.

## Stronger fixed theorem

The exact parameters are

\[
a=\frac{1123}{10000},\qquad
r_\lambda=\frac{581}{2500},\qquad
r_0=\frac{2453}{5000},\qquad
p=\frac{83301}{100000},\qquad
\lambda=\frac{2582}{3783}.
\]

They satisfy

\[
\lambda a+(1-\lambda)r_0=r_\lambda,
\qquad
0<a<r_\lambda<r_0<\frac12.
\]

The exact Case I, Case II, and height margins over \(100/5599\) are
respectively

\[
\frac{139158989937085958631189100903645702101397}
{664352167944649011863150962260700000000000000000},
\]

\[
\frac{227923075074420651443585972857}
{74854501574905182351967200000000000},
\]

and

\[
\frac{22458464102067615300}
{1758977726744925234219353}.
\]

All are strictly positive.  A deliberately weakened logarithmic tail makes
the Case I margin strictly negative.  The exact verifier returns
`SYMBOLIC_PROOF_OK`, its `sv_review` gate is clean, and the fresh adversarial
audit confirmed the analytic branch, logarithm, radical, arcsine, and
measure-theoretic assembly.

The self-contained proof is `STRONGER-100-OVER-5599-PROOF.md`.

## Independent Arb witness

At the independent rational point

\[
(a,r_\lambda,r_0,p)
=
\left(
\frac{11226427}{10^8},
\frac{23237119}{10^8},
\frac{49059291}{10^8},
\frac{8329}{10^4}
\right),
\]

180-bit Arb arithmetic with 65,536 exact rational radial cells gives the
safe lower bounds

\[
H\geq0.017867413503103172,\qquad
A\geq0.017866278155401827,\qquad
B\geq0.017868746401806637.
\]

The fixed proof path uses exact `Fraction` endpoints and an Arb-native hull;
it contains no Python-float conversion.  Changing only
\(p=8329/10000\) to \(8330/10000\) makes the Case II branch strictly fail
the \(100/5599\) target.

This is a fixed-witness interval certificate, not a global optimum proof.

## Lean state

The package is `04-lean/`, library root `StarKakeyaLower`.  Three build targets:

```bash
lake build                                       # production root (= lake build +StarKakeyaLower)
lake build StarKakeyaLowerAudit                  # audit receipts only
lake build StarKakeyaLower StarKakeyaLowerAudit  # full library
```

The production root imports `StarKakeyaLower.UniversalAssembly` and nothing
else; `StarKakeyaLower.Audit` is a separate Lake target so that auditing is
never a production dependency.  The axiom audit reports only Mathlib's standard
`propext`, `Classical.choice`, and `Quot.sound`, for the final theorem and for
every audited component.

The final theorem is

```lean
theorem StarKakeyaLower.universal_strong_lower_bound :
    ∀ (E : Set Plane), StarShapedKakeya E →
      ENNReal.ofReal (Real.pi * 100 / 5599) < volume.toOuterMeasure E
```

with no endpoint, containment, or Li Lemma 2.5 premise.

Compiled unconditional layers:

- `ArithmeticKernel`, `NonIterativeKernel`, `StrongerKernel`: old and new exact
  rational parameters, positive margins, mutation controls, and the fixed
  stronger tuple's strict radical/quotient domain certificate.  `ArithmeticKernel`
  is the independent `π/56` rational kernel; it is deliberately *not* in the
  production closure and is reached only from the audit target;
- `GreedyResidual`: the finite zero-supremum stop and infinite selected-height
  convergence arguments, including the literal residual `sSup = 0` corollary;
- `AnalyticKernel`, `AnalyticBranches`: the positive logarithm series,
  alternating arctangent bounds, branch endpoint inequalities, derivative, and
  one exact interval primitive;
- `CircleDilation`, `QuotientCircle`: the arbitrary-family/countable-component
  real-line outer-measure kernel, same-centre containment, and the unconditional
  quotient-circle dilation bound `volume_iUnion_quotientCenteredDilate_le`
  together with its hybrid open/closed variant;
- `PolarOuterMeasure`: unconditional polar slicing for arbitrary (possibly
  nonmeasurable) plane sets, plus the `polarSector` lower bound;
- `PolarProjectiveOuter`, `CaseIAssemblyConditional`: the two-to-one
  polar/projective projection by two fundamental cuts, the selected-base union
  below the literal planar polar section, the radial integral into
  `E_all ∩ originOpenDisk r₀`, and the zero-safe hybrid pointwise contract
  `FirstArcPointwiseHybridCriticalContainment`;
- `LiGeometry`: support coordinates, the polar trace of a support triangle, the
  closed trace decomposition, `FirstArcData`, `JGamma`, and the support-parameter
  primitives (`SupportParameter`, `DirectedSupportParameter`,
  `planeNormSq_supportPoint`, `supportNeedle_baseEndpoints_mem_triangle`,
  `supportTraceFirstArcData?_zeroHeight_projectiveCenter_radius`);
- `LiLemma23`, `StrongLiLemma25`: the exterior area calculus and the proved
  Li Lemma 2.5 outer statement (no longer a conditional);
- `CaseIEndpointAnalytic`, `CaseIEndpointR1Analytic`, `Figure5EndpointEnvelope`,
  `Figure5LocalContact`, `UniversalFirstArc`, `UniversalEndpointClosure`: the
  paper's three-branch `g`, the `R₁` endpoint envelope analysis, the Figure-5
  base-endpoint geometry and upper-gap source, and the pointwise local-contact
  closure of the Case-I endpoint containment;
- `ParametricCaseII`, `CaseIIGeometry`, `CaseIISelection`, `CaseIIAnalytic`:
  the single-triangle weight, epsilon coefficient, negative minimax coefficient,
  exact two-bound elimination, and `strongCaseII_radius_branch`;
- `UniversalNeedleAdapter`, `UniversalAssembly`: the raw-to-physical needle
  adapter, the arbitrary-set `Plane`/`CoordinatePlane` outer-measure bridge, the
  literal paper-radius control flow, and the final unconditional theorem;
- `NegativeControls`: audit-only regression guards (currently the exterior
  arcsine-dispatch counterexample);
- `Audit`: `#print axioms` coverage of the final theorem and of the
  load-bearing components.

No file contains `sorry`, `admit`, a custom `axiom`, or `native_decide`.

## Closed Lean bridges

All three bridges that were listed as open in earlier revisions of this file
are now closed:

1. the unconditional arbitrary-family quotient-circle dilation theorem
   (`volume_iUnion_quotientCenteredDilate_le`, including common-cut, wrapped,
   punctured-circle, exact-period and saturated branches);
2. the universal Case-I endpoint package, now
   `caseIEndpointPointwiseTheorem_proof`, built from the pointwise first-arc
   endpoint containment of `UniversalEndpointClosure`;
3. Li Lemma 2.5 on its stated domain `3/20 ≤ r ≤ 1/2`, now `strongLiLemma25`.

Consequently `strong_lower_bound_of_endpoint_pointwise` has no remaining
parameter, and `universal_strong_lower_bound` carries no premise.

The legacy all-support-graph, extrema, and conditional-endpoint scaffolds that
supported earlier attempts (`LiEndpointFatality`, `CaseIEndpointPointwise`,
`UniversalSupportHeight`, and the `Actual*`/`Raw*` endpoint-law families in
`CaseIEndpointAnalytic`/`Figure5EndpointEnvelope`) have been deleted; the small
number of primitives they still owned was moved into `LiGeometry`.

## Optimization and beyond-framework gaps

The numerical family scout finds approximately

\[
\sup_{\rm observed}\mathcal C
\approx0.017867413377227158.
\]

No global interval cover has been completed.  The exact missing R6 artifact
is a finite outward-rounded decomposition of every legal parameter triple,
including curved radical/domain and branch-switch boundaries, with a finite
prune log and certified global ceiling.

The beyond-framework routes were advanced to two explicit missing lemmas:

- a uniform cross-radius incompatibility inequality that exploits the fact
  that one triangle cannot attain the worst section geometry independently
  at every radius;
- an outer-measure Bellman inequality coupling the nested direction
  distributions across scales without reusing the same direction mass.

Neither lemma is proved.  Their exact scopes and reopen conditions are in
`ROUND-5-LITERATURE-AND-BEYOND-FRAMEWORK.md`.

## Resume order

Read:

1. `CAMPAIGN-CONTRACT.md`;
2. `STRONGER-100-OVER-5599-PROOF.md`;
3. `ROUND-2-LI-THEOREM-AUDIT.md`;
4. `ROUND-5-LITERATURE-AND-BEYOND-FRAMEWORK.md`;
5. `LEAN-CAMPAIGN-CONTRACT.md`;
6. `APPROACH-PORTFOLIO.md`.

The quotient-circle/endpoint-geometry adapter now includes direction-indexed
needle coordinates, normalized polar arcs and their transports, and a minimal
first-arc data contract at one fixed common radius.  The contract permits an
empty second arc and requires the present arcs to be disjoint maximal connected
components whose union is the complete trace; deterministic length ordering
chooses component zero on a tie.  For a fixed target polar arc `Γ`, `JGamma Γ`
means exactly `{α | firstArc α ⊆ Γ}`.  No family-containment consequence is
claimed.  The misleading old single-triangle “final containment” declaration
was replaced by `endpointConfiguration_envelope_subset_sameCentre_dilate`,
which explicitly says that its input is already endpoint data.

The compiled PASS scope also includes exact support coordinates, rotation of
support points and filled triangles, the one- and two-component `FirstArcData`
constructors, and the definitional `mem_JGamma_iff`.  The theorem
`endpointEnvelopeAlgebra_subset_sameCentre_dilate` is deliberately only pure
set/interval algebra: it assumes an arbitrary set is already contained in the
endpoint envelope.  Its containment step is factored through the elementary
set-transitivity lemma `subset_dilate_of_subset_endpointEnvelope`; neither
theorem contains raw-family geometry or constructs a selector.

Li's critical-endpoint theorem from a raw Kakeya family — construct the trace
data at the chosen common radius and prove that the selected first-arc endpoints
are the support contacts, with the interior/exterior endpoint relations and the
ratio estimate — is now proved, by the pointwise local-contact route of
`Figure5LocalContact` and `UniversalEndpointClosure` rather than by a global
extremum argument.  What remains open is the *global optimum* of the parameter
family and the beyond-framework improvements, not the theorem itself.
