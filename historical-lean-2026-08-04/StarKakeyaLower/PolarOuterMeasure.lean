import StarKakeyaLower.LiGeometry
import StarKakeyaLower.StarKakeyaSet
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Outer-measure polar slicing

This file is independent of Li's endpoint lemma.  Sections are taken in the
standard cut `(-π,π)`; omitting the cut point loses no angular measure.  The
main theorem is deliberately stated for arbitrary sets, using outer measure
(and a measurable minorant of the radial section bound), so no measurability
of a Kakeya set or of its sections is silently assumed.
-/

open Set MeasureTheory Real
open scoped ENNReal

namespace StarKakeyaLower

noncomputable section

/-- Polar angles at radius `r` whose points belong to `E`, in the standard
one-turn cut used by Mathlib's polar-coordinate change of variables. -/
def polarAngleSection (E : Set CoordinatePlane) (r : ℝ) : Set ℝ :=
  {θ | θ ∈ Ioo (-Real.pi) Real.pi ∧ polarPoint r θ ∈ E}

/-- Angular outer measure of an arbitrary polar section. -/
def angleOuter (E : Set CoordinatePlane) (r : ℝ) : ℝ≥0∞ :=
  volume.toOuterMeasure (polarAngleSection E r)

/-- Parametric outer arc length.  This is the pullback definition of length on
an `r`-circle: angular Lebesgue outer measure multiplied by `|r|`. -/
def circleArcOuterLength (r : ℝ) (A : Set ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal |r| * volume.toOuterMeasure A

/-- Arc length on a radius-`r` circle is `|r|` times angular outer measure.
The nonnegative-radius form is provided immediately below. -/
theorem circleArcOuterLength_eq (r : ℝ) (A : Set ℝ) :
    circleArcOuterLength r A = ENNReal.ofReal |r| * volume.toOuterMeasure A := rfl

/-- The usual radius-times-angle formula. -/
theorem circleArcOuterLength_eq_of_nonneg {r : ℝ} (hr : 0 ≤ r) (A : Set ℝ) :
    circleArcOuterLength r A = ENNReal.ofReal r * volume.toOuterMeasure A := by
  simp [circleArcOuterLength, abs_of_nonneg hr]

@[simp] theorem polarCoord_symm_eq_polarPoint (r θ : ℝ) :
    polarCoord.symm (r, θ) = polarPoint r θ := by
  rfl

set_option maxHeartbeats 800000 in
/-- Measurable-set polar slicing on a radial interval.  This is the Tonelli
form used to pass from a measurable hull to arbitrary-set outer measure. -/
theorem radial_lintegral_angleOuter_le_of_measurable
    {U : Set CoordinatePlane} (hU : MeasurableSet U) {a b : ℝ} (ha : 0 ≤ a) :
    (∫⁻ r in Icc a b, ENNReal.ofReal r * angleOuter U r) ≤ volume U := by
  have hpolar := lintegral_comp_polarCoord_symm (U.indicator (1 : CoordinatePlane → ℝ≥0∞))
  have hind : ∫⁻ z : CoordinatePlane, U.indicator (1 : CoordinatePlane → ℝ≥0∞) z = volume U := by
    simpa using lintegral_indicator_one hU
  rw [hind] at hpolar
  rw [← hpolar]
  have htarget : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := rfl
  rw [htarget]
  have hprod := setLIntegral_prod
    (s := Ioi (0 : ℝ)) (t := Ioo (-Real.pi) Real.pi)
    (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * U.indicator (1 : CoordinatePlane → ℝ≥0∞)
      (polarCoord.symm p))
    (by
      apply Measurable.aemeasurable
      exact measurable_fst.ennreal_ofReal.mul
        ((measurable_const.indicator hU).comp
          (continuous_polarCoord_symm.comp continuous_id).measurable) : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * U.indicator (1 : CoordinatePlane → ℝ≥0∞)
        (polarCoord.symm p))
      ((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi)))
  rw [show (∫⁻ (p : ℝ × ℝ) in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 • U.indicator (1 : CoordinatePlane → ℝ≥0∞) (polarCoord.symm p)) =
      ∫⁻ (p : ℝ × ℝ) in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 * U.indicator (1 : CoordinatePlane → ℝ≥0∞) (polarCoord.symm p) by
        congr 1]
  change (∫⁻ r in Icc a b, ENNReal.ofReal r * angleOuter U r) ≤
    ∫⁻ (p : ℝ × ℝ) in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 * U.indicator (1 : CoordinatePlane → ℝ≥0∞) (polarCoord.symm p)
      ∂(volume.prod volume)
  rw [hprod]
  let F : ℝ → ℝ≥0∞ := fun r =>
    ∫⁻ θ in Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal r * U.indicator (1 : CoordinatePlane → ℝ≥0∞) (polarCoord.symm (r, θ))
  have hsection (r : ℝ) (hr : r ∈ Icc a b) :
      ENNReal.ofReal r * angleOuter U r = F r := by
    have hpre : MeasurableSet ((fun θ : ℝ => polarCoord.symm (r, θ)) ⁻¹' U) :=
      hU.preimage (continuous_polarCoord_symm.comp
        (continuous_const.prodMk continuous_id)).measurable
    have hsec : MeasurableSet (polarAngleSection U r) := by
      simpa only [polarAngleSection, setOf_and] using measurableSet_Ioo.inter hpre
    simp only [angleOuter, Measure.toOuterMeasure_apply]
    simp only [F]
    have hindicator : Measurable
        (fun θ : ℝ => U.indicator (1 : CoordinatePlane → ℝ≥0∞) (polarCoord.symm (r, θ))) :=
      (measurable_const.indicator hpre)
    rw [lintegral_const_mul _ hindicator]
    congr 1
    rw [← lintegral_indicator measurableSet_Ioo]
    rw [← lintegral_indicator_one hsec]
    apply lintegral_congr
    intro θ
    by_cases hcut : θ ∈ Ioo (-Real.pi) Real.pi
    · rcases hcut with ⟨hl, hu⟩
      by_cases hmem : polarPoint r θ ∈ U
      · have hcoord : (r * Real.cos θ, r * Real.sin θ) ∈ U := by
          simpa [polarPoint, scaleCoordinatePlane, unitDirection] using hmem
        simp [Set.indicator, polarAngleSection, hl, hu, hmem, hcoord]
      · have hcoord : (r * Real.cos θ, r * Real.sin θ) ∉ U := by
          simpa [polarPoint, scaleCoordinatePlane, unitDirection] using hmem
        simp [Set.indicator, polarAngleSection, hl, hu, hmem, hcoord]
    · simp [Set.indicator, polarAngleSection, hcut]
  calc
    (∫⁻ r in Icc a b, ENNReal.ofReal r * angleOuter U r) =
        ∫⁻ r in Icc a b, F r :=
      setLIntegral_congr_fun measurableSet_Icc hsection
    _ ≤ ∫⁻ r in Ioi (0 : ℝ), F r := by
      apply lintegral_mono' (Measure.restrict_mono' (by
        have hne : ∀ᵐ r : ℝ ∂volume, r ≠ 0 := ae_iff.mpr (by
          simpa only [not_ne_iff, setOf_eq_eq_singleton] using
            (measure_singleton (μ := volume) (0 : ℝ)))
        filter_upwards [hne] with r hr0 hr
        exact lt_of_le_of_ne (ha.trans hr.1) (Ne.symm hr0)) le_rfl) le_rfl
    _ = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal r * U.indicator (1 : CoordinatePlane → ℝ≥0∞)
          (polarCoord.symm (r, θ)) := rfl

/-- **Unconditional outer-polar theorem.**  For an arbitrary (possibly
nonmeasurable) set, every measurable radial minorant of its angular outer
sections integrates to at most the planar outer measure. -/
theorem lintegral_le_outerMeasure_of_le_angleOuter
    (E : Set CoordinatePlane) {a b : ℝ} (ha : 0 ≤ a)
    (h : ℝ → ℝ≥0∞)
    (hle : ∀ r ∈ Icc a b, h r ≤ angleOuter E r) :
    (∫⁻ r in Icc a b, ENNReal.ofReal r * h r) ≤ volume.toOuterMeasure E := by
  let U := toMeasurable volume E
  have hEU : E ⊆ U := subset_toMeasurable volume E
  have hsec (r : ℝ) : angleOuter E r ≤ angleOuter U r := by
    apply OuterMeasure.mono
    intro θ hθ
    exact ⟨hθ.1, hEU hθ.2⟩
  calc
    (∫⁻ r in Icc a b, ENNReal.ofReal r * h r)
        ≤ ∫⁻ r in Icc a b, ENNReal.ofReal r * angleOuter U r := by
          apply setLIntegral_mono' measurableSet_Icc
          exact fun r hr => mul_le_mul_left' ((hle r hr).trans (hsec r)) _
    _ ≤ volume U := radial_lintegral_angleOuter_le_of_measurable
      (measurableSet_toMeasurable volume E) ha
    _ = volume E := measure_toMeasurable E
    _ = volume.toOuterMeasure E := (Measure.toOuterMeasure_apply volume E).symm

/-- Pointwise section bounds imply the outer-area bound; this is the convenient
Li A.2 interface. -/
theorem outerMeasure_ge_lintegral_of_angleOuter_ge
    (E : Set CoordinatePlane) {a b : ℝ} (ha : 0 ≤ a)
    (h : ℝ → ℝ≥0∞)
    (hle : ∀ r ∈ Icc a b, h r ≤ angleOuter E r) :
    (∫⁻ r in Icc a b, ENNReal.ofReal r * h r) ≤ volume.toOuterMeasure E :=
  lintegral_le_outerMeasure_of_le_angleOuter E ha h hle

/-! ## Arbitrary-angle radial sectors -/

/-- Angular outer measure in Mathlib's standard one-turn polar cut.  Intersecting
with the cut makes this definition meaningful for every `Θ : Set ℝ`, without a
measurability or normalization hypothesis. -/
def angleSetOuter (Θ : Set ℝ) : ℝ≥0∞ :=
  volume.toOuterMeasure (Θ ∩ Ioo (-Real.pi) Real.pi)

/-- The closed radial sector of radius `rho`, with centre `o` and arbitrary
(possibly nonmeasurable) angle set `Θ`. -/
def polarSector (o : CoordinatePlane) (rho : ℝ) (Θ : Set ℝ) : Set CoordinatePlane :=
  {z | ∃ r ∈ Icc (0 : ℝ) rho,
    ∃ θ ∈ Θ ∩ Ioo (-Real.pi) Real.pi, z = o + polarPoint r θ}

private theorem lintegral_radius_mul_const {rho : ℝ} (hrho : 0 ≤ rho) (c : ℝ≥0∞) :
    (∫⁻ r in Icc (0 : ℝ) rho, ENNReal.ofReal r * c) =
      ENNReal.ofReal (rho ^ 2 / 2) * c := by
  rw [lintegral_mul_const c (show Measurable (fun r : ℝ => ENNReal.ofReal r) from
    measurable_id.ennreal_ofReal)]
  congr 1
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le hrho]
    rw [integral_id]
    norm_num
  · exact continuous_id.integrableOn_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hr.1

private theorem polarSector_zero_outerMeasure_ge {rho : ℝ} (hrho : 0 ≤ rho) (Θ : Set ℝ) :
    ENNReal.ofReal (rho ^ 2 / 2) * angleSetOuter Θ ≤
      volume.toOuterMeasure (polarSector 0 rho Θ) := by
  rw [← lintegral_radius_mul_const hrho]
  apply outerMeasure_ge_lintegral_of_angleOuter_ge _ (a := 0) (b := rho) le_rfl
    (fun _ => angleSetOuter Θ)
  intro r hr
  apply OuterMeasure.mono
  intro θ hθ
  rcases hθ with ⟨hΘ, hcut⟩
  exact ⟨hcut, r, hr, θ, ⟨hΘ, hcut⟩, by simp⟩

/-- **Arbitrary-angle radial-fan bound.** A radial sector has at least the
expected polar area.  The angle set may be nonmeasurable, the radius may be
zero, and the centre is arbitrary. -/
theorem polarSector_outerMeasure_ge (o : CoordinatePlane) {rho : ℝ}
    (hrho : 0 ≤ rho) (Θ : Set ℝ) :
    ENNReal.ofReal (rho ^ 2 / 2) * angleSetOuter Θ ≤
      volume.toOuterMeasure (polarSector o rho Θ) := by
  have hzero := polarSector_zero_outerMeasure_ge hrho Θ
  rw [Measure.toOuterMeasure_apply] at hzero ⊢
  calc
    _ ≤ volume (polarSector 0 rho Θ) := hzero
    _ = volume (polarSector o rho Θ) := by
      rw [← measure_preimage_add volume o (polarSector o rho Θ)]
      congr 1
      ext z
      simp only [polarSector, mem_preimage, mem_setOf_eq]
      constructor
      · rintro ⟨r, hr, θ, hθ, heq⟩
        exact ⟨r, hr, θ, hθ, by simpa using heq⟩
      · rintro ⟨r, hr, θ, hθ, heq⟩
        refine ⟨r, hr, θ, hθ, ?_⟩
        calc
          z = polarPoint r θ := add_left_cancel heq
          _ = 0 + polarPoint r θ := by simp

/-- Raw angular-outer-measure form when the arbitrary angle set is already in
the standard polar cut.  No measurability of `Θ` is assumed. -/
theorem polarSector_outerMeasure_ge_of_subset_cut (o : CoordinatePlane) {rho : ℝ}
    (hrho : 0 ≤ rho) (Θ : Set ℝ) (hΘ : Θ ⊆ Ioo (-Real.pi) Real.pi) :
    ENNReal.ofReal (rho ^ 2 / 2) * volume.toOuterMeasure Θ ≤
      volume.toOuterMeasure (polarSector o rho Θ) := by
  simpa [angleSetOuter, inter_eq_left.mpr hΘ] using
    polarSector_outerMeasure_ge o hrho Θ

/-! ## Euclidean-space adapter for Case II -/

/-- The volume-preserving coordinate equivalence from the Euclidean-space
model used by needles to the product model used by polar coordinates. -/
private def planeCoordinates : Plane ≃ᵐ CoordinatePlane :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

private theorem planeCoordinates_measurePreserving :
    MeasurePreserving planeCoordinates volume volume :=
  (MeasureTheory.volume_preserving_finTwoArrow ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

private theorem outerMeasure_preimage_le_of_measurePreserving
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μα : Measure α} {μβ : Measure β} {f : α → β}
    (hf : MeasurePreserving f μα μβ) (A : Set β) :
    μα.toOuterMeasure (f ⁻¹' A) ≤ μβ.toOuterMeasure A := by
  calc
    μα.toOuterMeasure (f ⁻¹' A) ≤
        μα.toOuterMeasure (f ⁻¹' toMeasurable μβ A) :=
      μα.toOuterMeasure.mono (preimage_mono (subset_toMeasurable μβ A))
    _ = μα (f ⁻¹' toMeasurable μβ A) := by
      rw [Measure.toOuterMeasure_apply]
    _ = μβ (toMeasurable μβ A) :=
      hf.measure_preimage (measurableSet_toMeasurable μβ A).nullMeasurableSet
    _ = μβ.toOuterMeasure A := by
      rw [Measure.toOuterMeasure_apply, measure_toMeasurable]

/-- The closed radial sector in the Euclidean-space model used by the needle
family. -/
def euclideanPolarSector (o : Plane) (rho : ℝ) (Θ : Set ℝ) : Set Plane :=
  {z | ∃ r ∈ Icc (0 : ℝ) rho,
    ∃ θ ∈ Θ ∩ Ioo (-Real.pi) Real.pi, z = o + r • angleVector θ}

private theorem planeCoordinates_preimage_polarSector
    (o : Plane) (rho : ℝ) (Θ : Set ℝ) :
    planeCoordinates ⁻¹' polarSector (planeCoordinates o) rho Θ =
      euclideanPolarSector o rho Θ := by
  ext z
  simp only [mem_preimage, polarSector, euclideanPolarSector, mem_setOf_eq]
  constructor
  · rintro ⟨r, hr, θ, hθ, heq⟩
    refine ⟨r, hr, θ, hθ, ?_⟩
    apply planeCoordinates.injective
    apply Prod.ext
    · simpa [planeCoordinates, polarPoint, scaleCoordinatePlane, unitDirection,
        angleVector] using congrArg Prod.fst heq
    · simpa [planeCoordinates, polarPoint, scaleCoordinatePlane, unitDirection,
        angleVector] using congrArg Prod.snd heq
  · rintro ⟨r, hr, θ, hθ, rfl⟩
    refine ⟨r, hr, θ, hθ, ?_⟩
    have h0 : Matrix.vecHead o.ofLp = o.ofLp 0 := rfl
    have h1 : Matrix.vecHead (Matrix.vecTail o.ofLp) = o.ofLp 1 := rfl
    apply Prod.ext <;>
      simp [planeCoordinates, polarPoint, scaleCoordinatePlane, unitDirection, angleVector,
        h0, h1]

/-- Arbitrary-angle radial-fan bound in the Euclidean-space model. -/
theorem euclideanPolarSector_outerMeasure_ge (o : Plane) {rho : ℝ}
    (hrho : 0 ≤ rho) (Θ : Set ℝ) :
    ENNReal.ofReal (rho ^ 2 / 2) * angleSetOuter Θ ≤
      volume.toOuterMeasure (euclideanPolarSector o rho Θ) := by
  refine (polarSector_outerMeasure_ge (planeCoordinates o) hrho Θ).trans ?_
  have h := outerMeasure_preimage_le_of_measurePreserving
    planeCoordinates_measurePreserving.symm (euclideanPolarSector o rho Θ)
  rw [show planeCoordinates.symm ⁻¹' euclideanPolarSector o rho Θ =
      polarSector (planeCoordinates o) rho Θ by
    rw [← planeCoordinates_preimage_polarSector]
    ext z
    simp] at h
  exact h

/-- Standard-cut form of the Euclidean radial-fan bound. -/
theorem euclideanPolarSector_outerMeasure_ge_of_subset_cut (o : Plane) {rho : ℝ}
    (hrho : 0 ≤ rho) (Θ : Set ℝ) (hΘ : Θ ⊆ Ioo (-Real.pi) Real.pi) :
    ENNReal.ofReal (rho ^ 2 / 2) * volume.toOuterMeasure Θ ≤
      volume.toOuterMeasure (euclideanPolarSector o rho Θ) := by
  simpa [angleSetOuter, inter_eq_left.mpr hΘ] using
    euclideanPolarSector_outerMeasure_ge o hrho Θ

end

end StarKakeyaLower
