import StarKakeyaLower.EndpointCapacityNeedleAdapter

/-!
# Endpoint-capacity strict radial superlevels

The radial-sliver theorem controls directions that occur somewhere outside a
strict radius, not one fixed radial section.  This module defines that target
and connects it to the existing projective quotient-circle covering theorem.
-/

open Set MeasureTheory Real
open scoped ENNReal

namespace StarKakeyaLower

noncomputable section

/-- Polar directions represented in `E` at some radius strictly larger than
`r0`. -/
def radialSuperlevelPolar (E : Set CoordinatePlane) (r0 : ℝ) : Set PolarAngle :=
  {φ | ∃ theta rho : ℝ,
    (theta : PolarAngle) = φ ∧ r0 < rho ∧ polarPoint rho theta ∈ E}

/-- Oriented angular outer mass of the strict radial superlevel, measured on the
standard real polar cut. -/
def radialSuperlevelOuter (E : Set CoordinatePlane) (r0 : ℝ) : ℝ≥0∞ :=
  volume.toOuterMeasure (polarCarrierCut (radialSuperlevelPolar E r0))

/-- Strict radial superlevels are monotone in the underlying planar set. -/
theorem radialSuperlevelOuter_mono
    {E F : Set CoordinatePlane} {r0 : ℝ} (hEF : E ⊆ F) :
    radialSuperlevelOuter E r0 ≤ radialSuperlevelOuter F r0 := by
  apply measure_mono
  intro theta htheta
  exact ⟨htheta.1, by
    rcases htheta.2 with ⟨alpha, rho, halpha, hrho, hp⟩
    exact ⟨alpha, rho, halpha, hrho, hEF hp⟩⟩

/-- Projecting the strict radial superlevel to unoriented directions cannot
increase its outer mass beyond the oriented standard-cut mass. -/
theorem volume_projectedRadialSuperlevel_le
    (E : Set CoordinatePlane) (r0 : ℝ) :
    volume (polarToProjective '' radialSuperlevelPolar E r0) ≤
      radialSuperlevelOuter E r0 := by
  exact volume_projectedPolar_le_cutOuter _

/-- Generic quotient-cover consequence with an arbitrary projective target set.
This is the target-set version of the fixed-section adapter. -/
theorem projectiveOuter_ge_of_hybridSliverFamilyContainment
    {ι : Type*} {U A : Set ProjectiveDirection} {g : ℝ}
    {x rad : ι → ℝ} {q : ℝ≥0∞}
    (hg : 1 ≤ g) (hrad : ∀ i, 0 ≤ rad i)
    (hcover : HybridSliverFamilyContainment A g x rad)
    (hmass : ENNReal.ofReal g * q ≤ volume A)
    (hbase : (⋃ i, quotientHybridCenteredArc Real.pi (x i) (rad i)) ⊆ U) :
    q ≤ volume U := by
  have hcovered : volume A ≤
      volume (⋃ i, quotientHybridCenteredDilate g Real.pi (x i) (rad i)) :=
    measure_mono hcover
  have hdilate := volume_iUnion_quotientHybridCenteredDilate_le
    g Real.pi hg x rad hrad
  have hbaseMeasure :
      volume (⋃ i, quotientHybridCenteredArc Real.pi (x i) (rad i)) ≤ volume U :=
    measure_mono hbase
  have hmul : ENNReal.ofReal g * q ≤ ENNReal.ofReal g * volume U :=
    hmass.trans
      (hcovered.trans (hdilate.trans (mul_le_mul_right hbaseMeasure _)))
  exact (ENNReal.mul_le_mul_iff_right
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith)))
    ENNReal.ofReal_ne_top).mp hmul

/-- Hybrid sliver covering specialized to the strict radial superlevel target. -/
theorem radialSuperlevelOuter_ge_of_hybridSliverFamilyContainment
    {ι : Type*} {E : Set CoordinatePlane} {r0 g : ℝ}
    {A : Set ProjectiveDirection} {x rad : ι → ℝ} {q : ℝ≥0∞}
    (hg : 1 ≤ g) (hrad : ∀ i, 0 ≤ rad i)
    (hcover : HybridSliverFamilyContainment A g x rad)
    (hmass : ENNReal.ofReal g * q ≤ volume A)
    (hbase : (⋃ i, quotientHybridCenteredArc Real.pi (x i) (rad i)) ⊆
      polarToProjective '' radialSuperlevelPolar E r0) :
    q ≤ radialSuperlevelOuter E r0 :=
  (projectiveOuter_ge_of_hybridSliverFamilyContainment
    hg hrad hcover hmass hbase).trans
      (volume_projectedRadialSuperlevel_le E r0)

end

end StarKakeyaLower
