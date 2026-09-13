import StarKakeyaLower.UniversalAssembly
import StarKakeyaLower.BallSplit
import StarKakeyaLower.AnnularGeometry
import StarKakeyaLower.AnnularGreedy
import StarKakeyaLower.AnnularGreedyInfinite
import StarKakeyaLower.AnnularCaseI
import StarKakeyaLower.AnnularKernel
import StarKakeyaLower.AnnularAnalytic
import StarKakeyaLower.AnnularCaseIIntegral
import StarKakeyaLower.EndpointConfinedExit
import StarKakeyaLower.AnnularEndpoint
import StarKakeyaLower.AnnularAssembly
import StarKakeyaLower.EndpointCapacityGeometry
import StarKakeyaLower.EndpointCapacityFractionalCover
import StarKakeyaLower.EndpointCapacitySliverCover
import StarKakeyaLower.EndpointCapacitySliverGeometry
import StarKakeyaLower.EndpointCapacityNeedleAdapter
import StarKakeyaLower.EndpointCapacityRadialSuperlevel
import StarKakeyaLower.EndpointCapacitySingleNeedleSliver
import StarKakeyaLower.EndpointCapacityFixedWindow
import StarKakeyaLower.EndpointCapacityUniversal
import StarKakeyaLower.EndpointCapacityLayerCake
import StarKakeyaLower.EndpointCapacityLogBound
import StarKakeyaLower.EndpointCapacityClasses
import StarKakeyaLower.EndpointCapacityWitness32Data
import StarKakeyaLower.EndpointCapacityHighGeometry
import StarKakeyaLower.EndpointCapacityHighLedger
import StarKakeyaLower.EndpointCapacityLeftLimit
import StarKakeyaLower.EndpointCapacityPayment
import StarKakeyaLower.EndpointCapacityWitness32Arithmetic
import StarKakeyaLower.EndpointCapacityLowSchedule
import StarKakeyaLower.EndpointCapacityHighAggregate
import StarKakeyaLower.EndpointCapacityHighConcrete
import StarKakeyaLower.EndpointCapacityLowConcrete
import StarKakeyaLower.EndpointCapacityFinalAssembly
import StarKakeyaLower.EndpointCapacityFinal141
import StarKakeyaLower.EndpointCapacityFinal3527

/-!
# `StarKakeyaLower` — production root

Importing this module gives **four** unconditional lower bounds,
together with every declaration each of them depends on:

* `StarKakeyaLower.Witness3527.universal_certifiedCoefficient_mul_pi`
  — the selector-independent endpoint-capacity bound at the exact minimum
  four-term rational surrogate coefficient times `π`, closed by the frozen
  64-class schedule in `EndpointCapacityFinal3527`; the short strict rational
  `3527/50000` theorem is retained only as an internal certificate corollary;
* `StarKakeyaLower.Witness141.universal_one_forty_one_over_two_thousand`
  — the strict selector-independent `141/2000` endpoint-capacity bound, closed
  by `EndpointCapacityFinal141`;

* `StarKakeyaLower.universal_strong_lower_bound : UniversalStrongLowerBound`
  — the published `100π/5599` bound, closed by `UniversalAssembly`;
* `StarKakeyaLower.universal_annular_lower_bound : UniversalAnnularLowerBound`
  — the joint inner/outer bound `π · 131/6250 = 131π/6250`, closed by the
  milestone-M7 module `AnnularAssembly`.

The N=64 certified headline is `certifiedCoefficient · π ≈ 0.07054486807936307`;
the literal full fraction is frozen in `EndpointCapacityWitness64Data`.  It
strictly improves the earlier N=32 endpoint-capacity bound `141/2000 = 0.0705`.
Also,
`131/6250 = 0.020 96` strictly exceeds `100/5599 ≈ 0.017 86`, so the annular
route is the stronger of those two older routes.  The latter two proofs share no
assembly step: no declaration used by one is used by the other, and the M7 import
closure contains
no module carrying the frozen `100π/5599` witness constants.

`UniversalAssembly` is the only import that contributes to
`universal_strong_lower_bound`, and `AnnularAssembly` is the only import that
contributes to `universal_annular_lower_bound`; each transitively re-exports its
own production dependency closure.

`StarKakeyaLower.BallSplit`, `StarKakeyaLower.AnnularGeometry`,
`StarKakeyaLower.AnnularGreedy`, `StarKakeyaLower.AnnularGreedyInfinite`,
`StarKakeyaLower.AnnularCaseI`, `StarKakeyaLower.AnnularKernel`,
`StarKakeyaLower.AnnularAnalytic`, `StarKakeyaLower.AnnularCaseIIntegral`,
`StarKakeyaLower.EndpointConfinedExit` and
`StarKakeyaLower.AnnularEndpoint` are the component modules of the
joint inner/outer route.  `StarKakeyaLower.EndpointCapacityGeometry` is the
first CLEAN geometry module for the later finite radial-schedule route; it
proves only the coordinate unit-chord gap `M² ≥ m² + 1/4`.
`StarKakeyaLower.EndpointCapacityFractionalCover` proves the application-level
finite fractional-cover lemma for pairwise-disjoint, arbitrary nonmeasurable
atoms and their weighted class unions.
`StarKakeyaLower.EndpointCapacitySliverCover` adds the zero-safe generic
quotient-circle covering adapter.  `EndpointCapacitySliverGeometry` proves the
positive/negative support-chord arcsine windows, the paper dilation factor, and
the squared-radius side-selection theorem for an arbitrary unit chord.
`EndpointCapacityNeedleAdapter` lifts these statements to the literal triangle
of a `DirectionNeedle`.  `EndpointCapacityRadialSuperlevel` defines the correct
strict outside-radius target and its generic projective covering adapter.
`EndpointCapacitySingleNeedleSliver` constructs positive-height owner
certificates on both signed sides plus the zero-height hybrid singleton.
`EndpointCapacityFixedWindow` performs the arbitrary, nonmeasurable family
selection and proves the reciprocal-coefficient fixed-window Theorem A.
`EndpointCapacityUniversal` specializes it to the canonical arbitrary selector,
first in the exact selected-triangle-union form and then as a centered-set
monotonicity corollary.  `EndpointCapacityLayerCake` proves radial down-closure
of the selected union and converts finite strict-superlevel steps into planar
outer measure.  `EndpointCapacityLogBound` supplies the single in-kernel
atanh/log tail bound used by the frozen rational schedule.
`EndpointCapacityClasses` provides the initial/half-open nearest-radius classes,
their disjointness, and their unit-chord-gap eligibility wrappers.
`EndpointCapacityWitness32Data` freezes the rational witness and kernel-checks
its geometry, radial budgets, and final rational comparisons.
`EndpointCapacityHighGeometry` and `EndpointCapacityHighLedger` prove the exact
foot-outside bound, high-class eligibility, and pairwise-disjoint high ledgers.
`EndpointCapacityLeftLimit` removes the strict-threshold mismatch by proving
left-limit equality a.e. and the exact left-limit layer-cake bound.
`EndpointCapacityPayment` and `EndpointCapacityWitness32Arithmetic` identify
the radial kernel's logarithmic antiderivative and kernel-check all 32 frozen
payments above the common coefficient.
`EndpointCapacityLowSchedule` and `EndpointCapacityHighAggregate` formalize the
finite fractional-cover and countable disjoint-ledger assembly cores.
`EndpointCapacityFinalAssembly` combines the local low/high integrals before
paying planar outer measure once, then closes direction coverage, selected-set
containment, the height dichotomy, and final arithmetic.
`EndpointCapacityHighConcrete` and `EndpointCapacityLowConcrete` supply the
complete frozen local payments.  `EndpointCapacityFinal141` discharges the two
local inputs and proves the unconditional strict bound
`ENNReal.ofReal (141 / 2000) < volume.toOuterMeasure E` for every
`StarShapedKakeya E`.
The annular components prove no new unconditional lower bound on their own and
none of them
is used by `universal_strong_lower_bound`; they are now consumed by
`AnnularAssembly`, and are still listed here individually so that the default
`lake build` keeps every one of them compiling.  None of them imports any
module carrying the frozen witness constants.

`StarKakeyaLower.AnnularKernel` fixes the production parameter tuple and
discharges `PROOF.md` Hypothesis B; `StarKakeyaLower.AnnularAnalytic` pays the
arcsine enclosure and the exterior gates C1/C3/C4; and
`StarKakeyaLower.AnnularCaseIIntegral` is the two-active-segment radial
integral certificate, which discharges the `hg`, `hmeas` and `hI` inputs of the
confined M5 interface and the interior gate C2 (`annTarget < annILower`).  The
integral module reads the parameter tuple from `AnnularKernel` and adds no
constant of its own beyond the two rational branch cuts and the stored segment
bounds.

The audit-only `StarKakeyaLower.AnnularIntegralControls` is deliberately *not*
imported here: like `StarKakeyaLower.NegativeControls` it is reached only from
`StarKakeyaLower.Audit`.

`StarKakeyaLower.EndpointConfinedExit` (milestone M6) is the contract-pinning
bridge: it feeds the parameterised endpoint exits `endpointTraceFor` and
`endpointCriticalFor` into the M5 confined wrapper at an arbitrary
`Figure5EndpointDomain`.  It also proves nothing unconditional and is not used
by `universal_strong_lower_bound`, and — like the modules above — it imports no
module carrying the frozen witness constants: the whole Figure-5 endpoint chain
is parameterised into the CLEAN `…EnvelopeCore` / `…LocalContactCore` /
`…EndpointClosureCore` modules, and the `100π/5599` tuple lives only in
`StarKakeyaLower.Figure5FrozenPackage` and the three historical facades built on
it, which keep the pre-M6 API unchanged.

`StarKakeyaLower.AnnularEndpoint` (milestone M6, endpoint/confined) instantiates
that interface at the production tuple `(annA, annR₀, annR₁, annPaperG)`:
`annFigure5Domain`, `annFigure5AnalyticPackage` and the confined exit
`annular_confined_lower_bound`, whose only hypothesis is the confined branch of
the height dichotomy.  Its single deep gate `ann_base_ray_gap` is proved from
scratch by exact rational cuts against `annPaperG`; the module deliberately does
**not** reach `StarKakeyaLower.StrongerKernel` or
`StarKakeyaLower.Figure5FrozenPackage`, because `base_ray_frozen_analytic`
(the `t = 7/100` polynomial split of the frozen tuple) is false at `annA`.
It proves no unconditional lower bound on its own and is not used by
`universal_strong_lower_bound`; it is the interior half of the M7 ledger.

`StarKakeyaLower.AnnularAssembly` (milestone M7) is the final assembly.  It
imports exactly four modules — `BallSplit` (the M1 Carathéodory split),
`AnnularGreedyInfinite` (the M4 exterior exit), `AnnularAnalytic` (the M6
numeric/analytic gates C1/C3/C4) and `AnnularEndpoint` (the M6 endpoint/confined
exit, which transitively supplies the M6 interior gate C2) — and splits on the
height dichotomy at `annA`.  The high branch is paid by gate (C1) against
`high_branch_outerMeasure`; the confined branch lowers the interior coefficient
`annILower` and the exterior coefficient `annCExt` to their minimum
`annJointCoefficient`, adds the two ledgers along the M1 split at radius
`annR₀`, and multiplies by the direction mass `L_in + L_out ≥ π`.  That mass
bound is obtained from circle coverage and outer-measure subadditivity only:
neither direction class is assumed measurable, and no `ℝ≥0∞` cancellation is
used — the strict step is `ENNReal.mul_lt_mul_left` with explicit `≠ 0` and
`≠ ⊤` side conditions supplied by `π ≤ L_in + L_out ≤ 2π`.

The `#print axioms` receipts live in `StarKakeyaLower.Audit`, which is a separate
build target on purpose so that auditing never becomes a production dependency.
-/
