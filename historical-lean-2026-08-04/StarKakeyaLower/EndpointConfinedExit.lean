import StarKakeyaLower.AnnularCaseI
import StarKakeyaLower.UniversalEndpointClosureCore

/-!
# The endpoint exit of the confined branch, at an arbitrary parameter tuple

This module contains no geometry and no analysis.  It exists to *pin the
contract*: it plugs the two generic endpoint exits of `UniversalEndpointClosure`
(`endpointTraceFor`, `endpointCriticalFor`) and the package's `hg` gate
(`endpointOneLeG`) into the milestone-M5 confined wrapper
`universal_positive_confined_lower_bound_of_trace_containment`, at an arbitrary
`Figure5EndpointDomain`.

The residual hypotheses are exactly the two *scalar* items M6 still owes and
which are deliberately out of scope here: the `AEMeasurable` side condition on
`fun r => r / g r` and the `∫⁻` radial certificate `I_lower`.  No parameter
tuple, no numeral and no integral constant occurs below.

The import closure of this module carries no frozen witness constant: the whole
Figure-5 endpoint chain (`Figure5EndpointDomain`, `SupportFirstArcSelector`,
`Figure5EndpointEnvelopeCore`, `Figure5LocalContactCore`, `UniversalFirstArc`,
`UniversalEndpointClosureCore`) is parameterised, and the `100π/5599` tuple is
confined to `Figure5FrozenPackage` and the three historical facades that sit on
top of it.
-/

open Set MeasureTheory
open scoped ENNReal

namespace StarKakeyaLower

noncomputable section

/-- **The confined lower bound at an arbitrary endpoint domain.**

Given a clean endpoint domain `P`, its analytic package `HP`, a star-shaped
Kakeya set with no support needle of height `P.a` at the centre, and a radial
certificate `I_lower` for `∫⁻ r in [P.a, P.r0], r / P.g r`, the interior mass of
the class `A_in_radius P.R1` is transported to the outer measure of `E` in the
closed ball of radius `P.r0`.

Every endpoint input of `universal_positive_confined_lower_bound_of_trace_containment`
is discharged here: `htrace` by `endpointTraceFor`, `hcritical` by
`endpointCriticalFor`, `hg` by `endpointOneLeG` and `hmass` by
`directionAngleOuter_le_directionOuterMass_const` at the *constant* class. -/
theorem confined_lower_bound_of_endpointDomain
    {E : Set Plane} (K : StarShapedKakeya E)
    (P : Figure5EndpointDomain) (HP : Figure5EndpointAnalyticPackage P)
    (hhigh : ¬ ∃ theta : Direction,
      P.a ≤ (K.needleFamily theta).height K.center)
    {I_lower : ℝ≥0∞}
    (hmeas : AEMeasurable (fun r => ENNReal.ofReal (r / P.g r))
      (volume.restrict (Icc P.a P.r0)))
    (hI : I_lower ≤ ∫⁻ r in Icc P.a P.r0, ENNReal.ofReal (r / P.g r)) :
    I_lower * directionAngleOuter (K.A_in_radius P.R1) ≤
      volume.toOuterMeasure (E ∩ Metric.closedBall K.center P.r0) :=
  universal_positive_confined_lower_bound_of_trace_containment K
    P.a_pos.le (P.a_pos.le.trans P.a_le_r0)
    (endpointTraceFor P K hhigh)
    (endpointOneLeG P HP)
    (directionAngleOuter_le_directionOuterMass_const K P.R1)
    (endpointCriticalFor P HP K hhigh)
    hmeas hI

end

end StarKakeyaLower
