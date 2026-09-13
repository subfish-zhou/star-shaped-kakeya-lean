import StarKakeyaLower.Trichotomy
import StarKakeyaLower.CaseIStrongIntegral
import StarKakeyaLower.CaseIEndpointMassIntegral
import StarKakeyaLower.CaseIIAnalytic
import StarKakeyaLower.StrongLiLemma25
import StarKakeyaLower.UniversalNeedleAdapter
import StarKakeyaLower.UniversalEndpointClosure
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Universal lower-bound assembly

This is the paper's literal radius trichotomy.  The proof first separates the
high-triangle alternative, and only under `no high` splits the direction mass
between `A_in_radius strongR₁` and its complement.  The exterior branch is
closed by `strongCaseII_radius_branch`; it is not an assembly hypothesis.

The inner-radius branch is closed by `caseIEndpointPointwiseTheorem_proof`,
which constructs the raw pointwise first-arc endpoint containment from
`UniversalEndpointClosure`.  Aggregate mass (using the inner-radius class `B`
supplied by the branch hypothesis `hin`), the radial integral, Li Lemma 2.5 and
Case II are all discharged by proved theorems as well.

Consequently `universal_strong_lower_bound : UniversalStrongLowerBound` below
carries no endpoint premise.
-/

open Set MeasureTheory
open scoped ENNReal

namespace StarKakeyaLower

noncomputable section

/-- The final unconditional statement.  It is proved at the end of this file by
`universal_strong_lower_bound`. -/
def UniversalStrongLowerBound : Prop :=
  ∀ (E : Set Plane), StarShapedKakeya E →
    ENNReal.ofReal (Real.pi * 100 / 5599) < volume.toOuterMeasure E

/-- The coordinate equivalence preserves the exact planar Lebesgue
normalization. -/
theorem planeCoordinateEquiv_measurePreserving :
    MeasurePreserving planeCoordinateEquiv := by
  exact coordinatePlaneEquiv_measurePreserving.symm coordinatePlaneEquiv

/-- The coordinate change preserves outer measure for arbitrary sets. -/
theorem outerMeasure_centeredCoordinate_image {E : Set Plane}
    (K : StarShapedKakeya E) :
    volume.toOuterMeasure (centeredCoordinate K '' E) =
      volume.toOuterMeasure E := by
  let τ : Plane ≃ᵐ Plane := MeasurableEquiv.addRight (-K.center)
  have hτ : MeasurePreserving τ := measurePreserving_add_right volume (-K.center)
  have hcoord : MeasurePreserving planeCoordinateEquiv :=
    planeCoordinateEquiv_measurePreserving
  have hcomp : MeasurePreserving (τ.trans planeCoordinateEquiv) := hτ.trans hcoord
  have himage : centeredCoordinate K '' E = (τ.trans planeCoordinateEquiv) '' E := by
    ext z
    simp only [centeredCoordinate, mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, ?_⟩
      change planeCoordinateEquiv (x - K.center) =
        planeCoordinateEquiv (x + -K.center)
      rw [sub_eq_add_neg]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, ?_⟩
      change planeCoordinateEquiv (x + -K.center) =
        planeCoordinateEquiv (x - K.center)
      rw [sub_eq_add_neg]
  rw [himage]
  have hpre := hcomp.measure_preimage_equiv
    ((τ.trans planeCoordinateEquiv) '' E)
  rw [preimage_image_eq E (τ.trans planeCoordinateEquiv).injective] at hpre
  exact hpre.symm

/-! ## The Case-I endpoint certificate -/

/-- The paper's inner-radius direction class at radius `R₁`. -/
abbrev StarShapedKakeya.innerRadiusClass {E : Set Plane} (K : StarShapedKakeya E) :
    Set ProjectiveDirection := K.A_in_radius strongR₁

/-- The Case-I endpoint certificate.  The physical-to-raw needle, triangle
transport, and height adapter are canonical theorems, so none of them is
retained as certificate data.  The sole field packages the genuine first arcs
at each needed radius together with the pointwise principal containment on the
inner-radius class `B = A_in_radius strongR₁`. -/
structure CaseIEndpointPointwiseCertificate {E : Set Plane}
    (K : StarShapedKakeya E) where
  endpoint : ∃ trace : ∀ r ∈ Icc strongA strongR₀, ∀ d,
      FirstArcData (universalPositiveNeedle K d).triangle r,
    ∀ r (hr : r ∈ Icc strongA strongR₀),
      FirstArcPointwiseHybridCriticalContainment
        (directionNeedleFamilyOfRaw (universalPositiveNeedle K) (trace r hr))
        K.innerRadiusClass (strongPaperG r)

/-- The sole universal-geometric/endpoint gap in the radius Case-I branch.
Both branch assumptions are explicit: no triangle is high, and the paper's
inner-radius class has at least `pπ` outer direction mass. -/
def CaseIEndpointPointwiseTheorem : Prop :=
  ∀ (E : Set Plane) (K : StarShapedKakeya E),
    (¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center) →
    ENNReal.ofReal (strongP * Real.pi) ≤
      StarShapedKakeya.directionOuterMeasure (K.A_in_radius strongR₁) →
    Nonempty (CaseIEndpointPointwiseCertificate K)

/-! ## Closed arithmetic and Case-I transport -/

/-- Exact strict comparison for the unconditional high branch. -/
theorem strong_target_lt_high_threshold :
    ENNReal.ofReal (Real.pi * strongTarget) <
      ENNReal.ofReal (strongA / 2) := by
  apply (ENNReal.ofReal_lt_ofReal_iff (by
    norm_num [strongA] : 0 < strongA / 2)).2
  have hpi : Real.pi < strongPiUpper := by
    convert Real.pi_lt_d20 using 1 <;> norm_num [strongPiUpper]
  have hmargin : strongTarget < strongA / (2 * strongPiUpper) := by
    have h := strong_height_rational_margin_exact
    have hpos : 0 < strongA / (2 * strongPiUpper) - strongTarget := by
      rw [h]
      positivity
    linarith
  have hupper : 0 < strongPiUpper := Real.pi_pos.trans hpi
  calc
    Real.pi * strongTarget < strongPiUpper * strongTarget := by
      exact mul_lt_mul_of_pos_right hpi (by norm_num [strongTarget])
    _ < strongPiUpper * (strongA / (2 * strongPiUpper)) :=
      mul_lt_mul_of_pos_left hmargin hupper
    _ = strongA / 2 := by field_simp

/-- Invoke the correct conditional Case-I theorem and transport its coordinate
outer-measure estimate back to `Plane`.  The aggregate radial mass is supplied
by the inner-radius branch hypothesis `hin`, which is therefore genuinely
consumed here; the direction set `A(r)` is the inner-radius class `B`, not the
full circle. -/
theorem strong_caseI_of_endpoint_certificate {E : Set Plane}
    (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    (hin : ENNReal.ofReal (strongP * Real.pi) ≤
      StarShapedKakeya.directionOuterMeasure (K.A_in_radius strongR₁))
    (D : CaseIEndpointPointwiseCertificate K) :
    ENNReal.ofReal (Real.pi * strongTarget) < volume.toOuterMeasure E := by
  obtain ⟨trace, critical⟩ := D.endpoint
  have hone : ∀ r ∈ Icc strongA strongR₀, 1 ≤ strongPaperG r := by
    intro r hr
    exact one_le_strongPaperG
      ((by norm_num [strongA] : 0 ≤ strongA).trans hr.1)
      (hr.2.trans_lt (by norm_num [strongR₀]))
  have hinner : ENNReal.ofReal (Real.pi * strongP) ≤
      directionOuterMass K.innerRadiusClass := by
    rw [show Real.pi * strongP = strongP * Real.pi by ring]
    exact hin
  have hmass : ∀ r (hr : r ∈ Icc strongA strongR₀),
      ENNReal.ofReal (strongPaperG r) * strongCaseIQ r ≤
        directionOuterMass K.innerRadiusClass := by
    intro r hr
    exact strongCaseI_aggregateMass_of_directionOuterMass
      ((by norm_num [strongA] : 0 ≤ strongA).trans hr.1)
      (hr.2.trans_lt (by norm_num [strongR₀])) hinner
  have hintegral : ENNReal.ofReal (Real.pi * strongP * strongILower) ≤
      ∫⁻ r in Icc strongA strongR₀, ENNReal.ofReal r * strongCaseIQ r :=
    strongCaseI_lintegral_ge_of_integral_ge strongILower_le_integral
  have hcoordinate := strongCaseI_conditional_area_lower_bound_strong
    (a := strongA) strongParameterDomain.a_pos.le (universalPositiveNeedle K) trace
    (fun _ => K.innerRadiusClass) strongPaperG strongCaseIQ hone hmass critical
    hintegral (universalPositiveNeedle_height_le_of_no_high hhigh)
  exact hcoordinate.trans_le <|
    (measure_mono (universalPositiveTriangleUnion_subset K)).trans_eq
      (outerMeasure_centeredCoordinate_image K)

/-! ## Paper radius assembly -/

/-- Conditional only on the two explicitly listed Case-I source theorems.
The proof first performs `by_cases high`; under `no high` it performs the radius
mass split.  The `A_out_radius` branch calls the proved
`strongCaseII_radius_branch` directly. -/
theorem strong_lower_bound_of_caseI
    (hEndpoint : CaseIEndpointPointwiseTheorem) :
    UniversalStrongLowerBound := by
  intro E K
  rw [show Real.pi * 100 / 5599 = Real.pi * strongTarget by
    rw [strongTarget]
    ring]
  by_cases hhigh : ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center
  · exact strong_target_lt_high_threshold.trans_le
      (K.high_branch_outerMeasure hhigh)
  · by_cases hin : ENNReal.ofReal (strongP * Real.pi) ≤
        StarShapedKakeya.directionOuterMeasure (K.A_in_radius strongR₁)
    · let D := Classical.choice (hEndpoint E K hhigh hin)
      exact strong_caseI_of_endpoint_certificate K hhigh hin D
    · have hout : ENNReal.ofReal ((1 - strongP) * Real.pi) ≤
          StarShapedKakeya.directionOuterMeasure (K.A_out_radius strongR₁) := by
        rcases K.direction_radius_trichotomy strongA strongR₁ strongP
          strongParameterDomain.p_pos.le strongParameterDomain.p_lt_one.le with
          hhigh' | hin' | hout'
        · exact False.elim (hhigh hhigh')
        · exact False.elim (hin hin')
        · exact hout'
      exact strongCaseII_radius_branch K hhigh hout

/-- **The Case-I endpoint theorem, proved.**  The support family, its
orientation normalization, its first-arc trace data, the target normalization
and the comparison height are all constructed from the raw
`StarShapedKakeya` data; nothing is assumed. -/
theorem caseIEndpointPointwiseTheorem_proof : CaseIEndpointPointwiseTheorem := by
  intro E K hhigh _hin
  exact ⟨⟨⟨fun r hr => universalArcData K hhigh hr,
    fun r hr => universal_hybrid_containment K hhigh hr⟩⟩⟩

/-- Final unconditional assembly.  The Case-I endpoint input is discharged
internally by `caseIEndpointPointwiseTheorem_proof`; no endpoint premise
remains. -/
theorem strong_lower_bound_of_endpoint_pointwise : UniversalStrongLowerBound :=
  strong_lower_bound_of_caseI caseIEndpointPointwiseTheorem_proof

/-- The paper's strong planar lower bound, unconditionally. -/
theorem universal_strong_lower_bound : UniversalStrongLowerBound :=
  strong_lower_bound_of_endpoint_pointwise

end

end StarKakeyaLower
