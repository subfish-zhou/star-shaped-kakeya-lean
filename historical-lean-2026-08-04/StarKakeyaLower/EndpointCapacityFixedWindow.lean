import StarKakeyaLower.EndpointCapacitySingleNeedleSliver

/-!
# Arbitrary-family fixed-window radial sliver theorem

This is the family assembly of the radial-sliver argument.  Certificate choice
is purely classical over the subtype of eligible projective directions; no
measurability of that choice is asserted or used.
-/

open Set MeasureTheory Real
open scoped ENNReal

namespace StarKakeyaLower

noncomputable section

/-- Every admissible needle has a zero-, positive-, or negative-side sliver
certificate. -/
theorem DirectionNeedle.exists_fixedWindowSliverCertificate
    {d : ProjectiveDirection} (N : DirectionNeedle d)
    {r0 r R : ℝ} (hr : 0 < r) (hrR : r < R) (hr0 : r0 < r)
    (hh : 0 ≤ N.height)
    (hinner : N.nearestRadiusSq ≤ r ^ 2)
    (houter : R ^ 2 ≤ N.maxEndpointRadiusSq) :
    Nonempty (SingleNeedleSliverCertificate N r R r0) := by
  by_cases hz : N.height = 0
  · exact ⟨N.zeroHeightSliverCertificate hz hr hrR hinner houter hr0⟩
  · have hhpos : 0 < N.height := lt_of_le_of_ne hh (Ne.symm hz)
    have hhr : N.height ≤ r := by
      have ht : 0 ≤ (unitChordNearestParameter N.centre) ^ 2 := sq_nonneg _
      rw [DirectionNeedle.nearestRadiusSq] at hinner
      nlinarith
    rcases unitChord_radial_side_selection
        (c := N.centre) (h := N.height) (r := r) (R := R)
        hr.le hrR.le
        (by simpa [DirectionNeedle.nearestRadiusSq] using hinner)
        (by simpa [DirectionNeedle.maxEndpointRadiusSq] using houter) with
      hpos | hneg
    · exact ⟨N.positiveSliverCertificate hhpos hhr hrR
        hpos.1 hpos.2 hr0⟩
    · exact ⟨N.negativeSliverCertificate hhpos hhr hrR
        hneg.1 hneg.2 hr0⟩

/-- Arbitrary-family fixed-window radial sliver theorem, in the division-free
form useful for `ℝ≥0∞`. -/
theorem volume_le_radialSuperlevelOuter_mul_of_fixedWindowNeedles
    (A : Set ProjectiveDirection)
    (N : ∀ d, DirectionNeedle d)
    (E : Set CoordinatePlane) (r0 r R : ℝ)
    (hr : 0 < r) (hrR : r < R) (hr0 : r0 < r)
    (hh : ∀ d ∈ A, 0 ≤ (N d).height)
    (hinner : ∀ d ∈ A, (N d).nearestRadiusSq ≤ r ^ 2)
    (houter : ∀ d ∈ A, R ^ 2 ≤ (N d).maxEndpointRadiusSq)
    (htriangle : ∀ d ∈ A, (N d).triangle ⊆ E) :
    volume A ≤ ENNReal.ofReal ((R + r) / (R - r)) *
      radialSuperlevelOuter E r0 := by
  classical
  let cert : ∀ i : A, SingleNeedleSliverCertificate (N i.1) r R r0 :=
    fun i => Classical.choice ((N i.1).exists_fixedWindowSliverCertificate
      hr hrR hr0 (hh i.1 i.2) (hinner i.1 i.2) (houter i.1 i.2))
  let x : A → ℝ := fun i => (cert i).center
  let rad : A → ℝ := fun i => (cert i).radius
  have hrad : ∀ i, 0 ≤ rad i := fun i => (cert i).radius_nonneg
  have hcover : HybridSliverFamilyContainment A
      (radialWindowDilation r R) x rad := by
    intro d hd
    refine Set.mem_iUnion.2 ⟨⟨d, hd⟩, ?_⟩
    exact (cert ⟨d, hd⟩).direction_mem
  have hbase : (⋃ i, quotientHybridCenteredArc Real.pi (x i) (rad i)) ⊆
      polarToProjective '' radialSuperlevelPolar E r0 := by
    intro q hq
    rcases Set.mem_iUnion.1 hq with ⟨i, hi⟩
    have hqN := (cert i).base_subset hi
    rcases hqN with ⟨phi, hphi, rfl⟩
    refine ⟨phi, ?_, rfl⟩
    rcases hphi with ⟨theta, rho, htheta, hrho, hp⟩
    exact ⟨theta, rho, htheta, hrho, htriangle i.1 i.2 hp⟩
  have hg : 1 ≤ radialWindowDilation r R := by
    have hden : 0 < R - r := sub_pos.2 hrR
    rw [radialWindowDilation]
    apply (le_div_iff₀ hden).2
    linarith
  calc
    volume A ≤ volume (⋃ i, quotientHybridCenteredDilate
        (radialWindowDilation r R) Real.pi (x i) (rad i)) :=
      measure_mono hcover
    _ ≤ ENNReal.ofReal (radialWindowDilation r R) *
        volume (⋃ i, quotientHybridCenteredArc Real.pi (x i) (rad i)) :=
      volume_iUnion_quotientHybridCenteredDilate_le
        (radialWindowDilation r R) Real.pi hg x rad hrad
    _ ≤ ENNReal.ofReal (radialWindowDilation r R) *
        volume (polarToProjective '' radialSuperlevelPolar E r0) :=
      mul_le_mul_right (measure_mono hbase) _
    _ ≤ ENNReal.ofReal (radialWindowDilation r R) *
        radialSuperlevelOuter E r0 :=
      mul_le_mul_right (volume_projectedRadialSuperlevel_le E r0) _
    _ = ENNReal.ofReal ((R + r) / (R - r)) *
        radialSuperlevelOuter E r0 := rfl

/-- Paper coefficient form of the arbitrary-family fixed-window theorem. -/
theorem ofReal_windowRatio_mul_volume_le_radialSuperlevelOuter
    (A : Set ProjectiveDirection)
    (N : ∀ d, DirectionNeedle d)
    (E : Set CoordinatePlane) (r0 r R : ℝ)
    (hr : 0 < r) (hrR : r < R) (hr0 : r0 < r)
    (hh : ∀ d ∈ A, 0 ≤ (N d).height)
    (hinner : ∀ d ∈ A, (N d).nearestRadiusSq ≤ r ^ 2)
    (houter : ∀ d ∈ A, R ^ 2 ≤ (N d).maxEndpointRadiusSq)
    (htriangle : ∀ d ∈ A, (N d).triangle ⊆ E) :
    ENNReal.ofReal ((R - r) / (R + r)) * volume A ≤
      radialSuperlevelOuter E r0 := by
  have hupper := volume_le_radialSuperlevelOuter_mul_of_fixedWindowNeedles
    A N E r0 r R hr hrR hr0 hh hinner houter htriangle
  have hRm : 0 < R - r := sub_pos.2 hrR
  have hRp : 0 < R + r := by linarith
  have ha : 0 ≤ (R - r) / (R + r) := (div_pos hRm hRp).le
  have hprod :
      ((R - r) / (R + r)) * ((R + r) / (R - r)) = 1 := by
    field_simp
  calc
    ENNReal.ofReal ((R - r) / (R + r)) * volume A ≤
        ENNReal.ofReal ((R - r) / (R + r)) *
          (ENNReal.ofReal ((R + r) / (R - r)) *
            radialSuperlevelOuter E r0) :=
      mul_le_mul_right hupper _
    _ = (ENNReal.ofReal ((R - r) / (R + r)) *
          ENNReal.ofReal ((R + r) / (R - r))) *
            radialSuperlevelOuter E r0 := by rw [mul_assoc]
    _ = radialSuperlevelOuter E r0 := by
      rw [← ENNReal.ofReal_mul ha, hprod]
      simp

end

end StarKakeyaLower
