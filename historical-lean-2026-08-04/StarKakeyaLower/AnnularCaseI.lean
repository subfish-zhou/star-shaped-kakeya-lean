import StarKakeyaLower.UniversalNeedleAdapter

/-!
# The confined branch at a variable interior mass

This is the physical wrapper of the generic radial core.  It takes the raw
radial estimate `outerMeasure_inner_ge_caseI_lintegral_of_raw`, feeds it the
variable-mass quotient `annularCaseIQ`, factors the mass out of the radial
integral with `lintegral_annularCaseIQ_eq_mul`, and transports the resulting
coordinate estimate back to `Plane` *restricted to the closed ball around the
star centre* using `outerMeasure_centeredCoordinate_image_inter_closedBall`.

Everything below is conditional, and deliberately so.  The first-arc trace, the
pointwise critical containment on the direction class `A`, the mass bound
`L_in ≤ directionOuterMass (A r)` and the scalar radial lower bound `I_lower`
are all *hypotheses*: this module certifies none of them.  There is no mass
split and no numeric constant anywhere in this file, and no endpoint theorem is
invoked.

The import closure of this module carries no frozen witness constant.
-/

open Set MeasureTheory
open scoped ENNReal

namespace StarKakeyaLower

noncomputable section

/-- Aggregate mass at every radius of the interval, in the exact shape consumed
by `outerMeasure_inner_ge_caseI_lintegral_of_raw`. -/
theorem annular_aggregateMass_on_Icc {a r₀ : ℝ} {g : ℝ → ℝ}
    {A : ℝ → Set ProjectiveDirection} {L_in : ℝ≥0∞}
    (hg : ∀ r ∈ Icc a r₀, 1 ≤ g r)
    (hmass : ∀ r ∈ Icc a r₀, L_in ≤ directionOuterMass (A r)) :
    ∀ r ∈ Icc a r₀,
      ENNReal.ofReal (g r) * annularCaseIQ L_in g r ≤ directionOuterMass (A r) :=
  fun r hr => annular_aggregateMass_of_directionOuterMass (hg r hr) (hmass r hr)

/-- The coordinate-side confined estimate at a variable interior mass: the raw
radial theorem applied to `annularCaseIQ`, with the mass factored out of the
integral and the supplied scalar lower bound inserted. -/
theorem lintegral_lower_bound_inner_of_raw_variable_mass
    {a r₀ : ℝ} {g : ℝ → ℝ} {A : ℝ → Set ProjectiveDirection}
    {L_in I_lower : ℝ≥0∞} (ha : 0 ≤ a)
    (N : (d : ProjectiveDirection) → DirectionNeedle d)
    (htrace : ∀ r ∈ Icc a r₀, ∀ d, FirstArcData (N d).triangle r)
    (hg : ∀ r ∈ Icc a r₀, 1 ≤ g r)
    (hmass : ∀ r ∈ Icc a r₀, L_in ≤ directionOuterMass (A r))
    (hcritical : ∀ r (hr : r ∈ Icc a r₀),
      FirstArcPointwiseHybridCriticalContainment
        (directionNeedleFamilyOfRaw N (htrace r hr)) (A r) (g r))
    (hmeas : AEMeasurable (fun r => ENNReal.ofReal (r / g r))
      (volume.restrict (Icc a r₀)))
    (hI : I_lower ≤ ∫⁻ r in Icc a r₀, ENNReal.ofReal (r / g r)) :
    I_lower * L_in ≤
      volume.toOuterMeasure
        (directionTriangleUnion N Set.univ ∩ originClosedDisk r₀) := by
  have hraw := outerMeasure_inner_ge_caseI_lintegral_of_raw ha N htrace A g
    (annularCaseIQ L_in g) hg (annular_aggregateMass_on_Icc hg hmass) hcritical
  rw [lintegral_annularCaseIQ_eq_mul hg hmeas] at hraw
  refine le_trans ?_ hraw
  rw [mul_comm I_lower L_in]
  exact mul_le_mul_right hI L_in

/-- **The generic physical confined lower bound.**

This is the single proof of the confined branch; the two named corollaries below
merely instantiate the raw family and hand it the matching restricted
containment.  Nothing is duplicated.

Given, on the radial interval `[a, r₀]`,

* first-arc trace data for the raw family `N`,
* pointwise hybrid critical containment on the direction class `A r`,
* the mass bound `L_in ≤ directionOuterMass (A r)`,
* the measurability licence for the radial integrand,
* a scalar lower bound `I_lower ≤ ∫⁻ r in [a, r₀], ofReal (r / g r)`, and
* a restricted containment of the confined triangle union into the confined
  centred image of `E`,

the part of `E` inside the closed ball of radius `r₀` around the star centre has
outer measure at least `I_lower * L_in`.

The interior mass `L_in` is a genuine variable of type `ℝ≥0∞`; no finiteness is
assumed and no mass split is hardwired.  `0 ≤ r₀` is load bearing for the
restricted transport, and it is not derivable from `0 ≤ a` alone since the
integration interval may be empty. -/
theorem confined_lower_bound_of_raw_of_restricted_containment
    {E : Set Plane} (K : StarShapedKakeya E)
    {a r₀ : ℝ} {g : ℝ → ℝ} {A : ℝ → Set ProjectiveDirection}
    {L_in I_lower : ℝ≥0∞} (ha : 0 ≤ a) (hr₀ : 0 ≤ r₀)
    (N : (d : ProjectiveDirection) → DirectionNeedle d)
    (htrace : ∀ r ∈ Icc a r₀, ∀ d, FirstArcData (N d).triangle r)
    (hg : ∀ r ∈ Icc a r₀, 1 ≤ g r)
    (hmass : ∀ r ∈ Icc a r₀, L_in ≤ directionOuterMass (A r))
    (hcritical : ∀ r (hr : r ∈ Icc a r₀),
      FirstArcPointwiseHybridCriticalContainment
        (directionNeedleFamilyOfRaw N (htrace r hr)) (A r) (g r))
    (hmeas : AEMeasurable (fun r => ENNReal.ofReal (r / g r))
      (volume.restrict (Icc a r₀)))
    (hI : I_lower ≤ ∫⁻ r in Icc a r₀, ENNReal.ofReal (r / g r))
    (hconfined : directionTriangleUnion N Set.univ ∩ originClosedDisk r₀ ⊆
      (centeredCoordinate K '' E) ∩ originClosedDisk r₀) :
    I_lower * L_in ≤
      volume.toOuterMeasure (E ∩ Metric.closedBall K.center r₀) := by
  refine (lintegral_lower_bound_inner_of_raw_variable_mass ha
    N htrace hg hmass hcritical hmeas hI).trans ?_
  refine le_trans (measure_mono hconfined) ?_
  exact le_of_eq (outerMeasure_centeredCoordinate_image_inter_closedBall K hr₀)

/-- **The conditional confined lower bound at a variable interior mass**, for the
canonical signed support family `universalDirectionNeedle K`.  A corollary of
`confined_lower_bound_of_raw_of_restricted_containment` with no new content. -/
theorem universal_confined_lower_bound_of_trace_containment
    {E : Set Plane} (K : StarShapedKakeya E)
    {a r₀ : ℝ} {g : ℝ → ℝ} {A : ℝ → Set ProjectiveDirection}
    {L_in I_lower : ℝ≥0∞} (ha : 0 ≤ a) (hr₀ : 0 ≤ r₀)
    (htrace : ∀ r ∈ Icc a r₀, ∀ d,
      FirstArcData (universalDirectionNeedle K d).triangle r)
    (hg : ∀ r ∈ Icc a r₀, 1 ≤ g r)
    (hmass : ∀ r ∈ Icc a r₀, L_in ≤ directionOuterMass (A r))
    (hcritical : ∀ r (hr : r ∈ Icc a r₀),
      FirstArcPointwiseHybridCriticalContainment
        (directionNeedleFamilyOfRaw (universalDirectionNeedle K) (htrace r hr))
        (A r) (g r))
    (hmeas : AEMeasurable (fun r => ENNReal.ofReal (r / g r))
      (volume.restrict (Icc a r₀)))
    (hI : I_lower ≤ ∫⁻ r in Icc a r₀, ENNReal.ofReal (r / g r)) :
    I_lower * L_in ≤
      volume.toOuterMeasure (E ∩ Metric.closedBall K.center r₀) :=
  confined_lower_bound_of_raw_of_restricted_containment K ha hr₀
    (universalDirectionNeedle K) htrace hg hmass hcritical hmeas hI
    (universalDirectionTriangleUnion_inter_originClosedDisk_subset K)

/-- **The conditional confined lower bound at a variable interior mass**, for the
positively oriented support family `universalPositiveNeedle K`.

This is the form the existing endpoint chain can feed: `universalArcData` and
`universal_hybrid_containment` produce trace data and pointwise critical
containment for `universalPositiveNeedle`, not for the signed family.  The
hypotheses and the conclusion otherwise match
`universal_confined_lower_bound_of_trace_containment` exactly, and the proof is
again the generic theorem above. -/
theorem universal_positive_confined_lower_bound_of_trace_containment
    {E : Set Plane} (K : StarShapedKakeya E)
    {a r₀ : ℝ} {g : ℝ → ℝ} {A : ℝ → Set ProjectiveDirection}
    {L_in I_lower : ℝ≥0∞} (ha : 0 ≤ a) (hr₀ : 0 ≤ r₀)
    (htrace : ∀ r ∈ Icc a r₀, ∀ d,
      FirstArcData (universalPositiveNeedle K d).triangle r)
    (hg : ∀ r ∈ Icc a r₀, 1 ≤ g r)
    (hmass : ∀ r ∈ Icc a r₀, L_in ≤ directionOuterMass (A r))
    (hcritical : ∀ r (hr : r ∈ Icc a r₀),
      FirstArcPointwiseHybridCriticalContainment
        (directionNeedleFamilyOfRaw (universalPositiveNeedle K) (htrace r hr))
        (A r) (g r))
    (hmeas : AEMeasurable (fun r => ENNReal.ofReal (r / g r))
      (volume.restrict (Icc a r₀)))
    (hI : I_lower ≤ ∫⁻ r in Icc a r₀, ENNReal.ofReal (r / g r)) :
    I_lower * L_in ≤
      volume.toOuterMeasure (E ∩ Metric.closedBall K.center r₀) :=
  confined_lower_bound_of_raw_of_restricted_containment K ha hr₀
    (universalPositiveNeedle K) htrace hg hmass hcritical hmeas hI
    (universalPositiveTriangleUnion_inter_originClosedDisk_subset K)

/-! ## How M6/M7 are meant to instantiate this interface

The direction class is *constant* in the radius on the confined branch: the
paper takes `A r = K.A_in_radius R₁` for every `r`, and the interior mass is the
angular outer measure of that class.  The instantiation helper below is the
exact bridge, and it is the only place where the constant-class choice is
recorded; no parameter tuple is fixed here.  M6 still owes `htrace`,
`hcritical`, a concrete `g` with its `hg`/`hmeas`, and a concrete `I_lower`.
-/

/-- The interior mass of a *constant* inner-radius class, in the exact shape the
confined interface consumes.  Combined with `directionOuterMass_eq_directionAngleOuter`
this says: taking `L_in = directionAngleOuter (K.A_in_radius R₁)` and
`A r = K.A_in_radius R₁` discharges the `hmass` hypothesis by `le_refl`. -/
theorem directionAngleOuter_le_directionOuterMass_const
    {E : Set Plane} (K : StarShapedKakeya E) (R₁ : ℝ) {a r₀ : ℝ} :
    ∀ r ∈ Icc a r₀,
      directionAngleOuter (K.A_in_radius R₁) ≤
        directionOuterMass ((fun _ : ℝ => K.A_in_radius R₁) r) :=
  fun _ _ => (directionOuterMass_eq_directionAngleOuter (K.A_in_radius R₁)).ge

end

end StarKakeyaLower
