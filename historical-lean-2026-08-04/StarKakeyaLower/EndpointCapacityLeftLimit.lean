import StarKakeyaLower.EndpointCapacityLayerCake
import Mathlib.Topology.Order.LeftRightLim

/-!
# Strict radial profiles and left limits

The fixed-window theorem is stated at every strict threshold `r₀ < r`.  Its
natural endpoint value is therefore the left limit of the antitone strict
radial-superlevel profile.  Monotone functions differ from this left limit at
only countably many points, hence not on a Lebesgue-relevant set.
-/

open Set Filter MeasureTheory Function
open scoped ENNReal Topology

namespace StarKakeyaLower

noncomputable section

/-- Strict radial-superlevel outer mass decreases with the threshold. -/
theorem radialSuperlevelOuter_antitone (E : Set CoordinatePlane) :
    Antitone (radialSuperlevelOuter E) := by
  intro r s hrs
  apply OuterMeasure.mono
  intro theta htheta
  exact ⟨htheta.1, by
    rcases htheta.2 with ⟨alpha, rho, halpha, hsrho, hp⟩
    exact ⟨alpha, rho, halpha, lt_of_le_of_lt hrs hsrho, hp⟩⟩

/-- An antitone `ENNReal` profile equals its left limit Lebesgue-a.e. -/
theorem Antitone.leftLim_ae_eq_volume
    {q : ℝ → ℝ≥0∞} (hq : Antitone q) :
    q.leftLim =ᵐ[volume] q := by
  filter_upwards [hq.countable_not_continuousAt.ae_notMem volume] with u hu
  simp only [not_not] at hu
  exact hq.continuousWithinAt_Iio_iff_leftLim_eq.1 hu.continuousWithinAt

/-- Concrete a.e. left-limit identity for strict radial-superlevel mass. -/
theorem radialSuperlevelOuter_leftLim_ae_eq (E : Set CoordinatePlane) :
    (radialSuperlevelOuter E).leftLim =ᵐ[volume]
      radialSuperlevelOuter E :=
  Antitone.leftLim_ae_eq_volume (radialSuperlevelOuter_antitone E)

/-- Layer-cake integral of the left-limit radial profile is bounded by planar
outer measure for every radially down-closed set, away from radius zero. -/
theorem leftLim_radialSuperlevel_lintegral_le_outerMeasure
    {E : Set CoordinatePlane} (hE : RadiallyDownClosed E)
    {a b : ℝ} (ha : 0 < a) :
    (∫⁻ r in Icc a b,
      ENNReal.ofReal r * (radialSuperlevelOuter E).leftLim r) ≤
      volume.toOuterMeasure E := by
  have hae :
      (fun r => ENNReal.ofReal r * (radialSuperlevelOuter E).leftLim r) =ᵐ[
        volume.restrict (Icc a b)]
      (fun r => ENNReal.ofReal r * radialSuperlevelOuter E r) := by
    change ∀ᵐ r ∂volume.restrict (Icc a b),
      ENNReal.ofReal r * (radialSuperlevelOuter E).leftLim r =
        ENNReal.ofReal r * radialSuperlevelOuter E r
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [radialSuperlevelOuter_leftLim_ae_eq E] with r hr
    intro _
    rw [hr]
  rw [MeasureTheory.lintegral_congr_ae hae]
  apply lintegral_le_outerMeasure_of_le_angleOuter E ha.le
  intro r hr
  exact radialSuperlevelOuter_le_angleOuter hE (ha.trans_le hr.1) le_rfl

/-- Canonical selected-triangle specialization of the left-limit layer cake. -/
theorem StarShapedKakeya.selectedTriangleUnion_leftLim_lintegral_le
    {E : Set Plane} (K : StarShapedKakeya E)
    {a b : ℝ} (ha : 0 < a) :
    (∫⁻ r in Icc a b,
      ENNReal.ofReal r *
        (radialSuperlevelOuter
          (directionTriangleUnion (universalPositiveNeedle K) Set.univ)).leftLim r) ≤
      volume.toOuterMeasure
        (directionTriangleUnion (universalPositiveNeedle K) Set.univ) :=
  leftLim_radialSuperlevel_lintegral_le_outerMeasure
    K.radiallyDownClosed_selectedTriangleUnion ha

/-- Exact selector-level fixed-window theorem at the left limit `q(r-)`. -/
theorem StarShapedKakeya.endpointCapacity_fixedWindow_leftLim
    {E : Set Plane} (K : StarShapedKakeya E)
    (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    ENNReal.ofReal ((R - r) / (R + r)) *
        volume (endpointCapacityWindowDirections K r R) ≤
      (radialSuperlevelOuter
        (directionTriangleUnion (universalPositiveNeedle K) Set.univ)).leftLim r := by
  let q := radialSuperlevelOuter
    (directionTriangleUnion (universalPositiveNeedle K) Set.univ)
  have hq : Antitone q := radialSuperlevelOuter_antitone _
  rw [show q.leftLim r = sInf (q '' Iio r) from
    leftLim_eq_of_tendsto (neBot_iff.mp inferInstance) (hq.tendsto_nhdsLT r)]
  apply le_sInf
  intro z hz
  rcases hz with ⟨r0, hr0, rfl⟩
  exact K.endpointCapacity_fixedWindow r0 r R hr hrR hr0

end

end StarKakeyaLower
