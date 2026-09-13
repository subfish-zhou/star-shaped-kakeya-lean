import StarKakeyaLower.OneTenthCircleReceipt
import StarKakeyaLower.PolarOuterMeasure

/-!
# The actual open-envelope polar bank

The bank is the physical section of the SAME measurable planar set `G`.
No measurability of a generated union, star-shapedness of `G`, finite volume,
or boundedness of the original Kakeya set is used. Haar volume on the physical
circle has mass `2*pi`, not one and not `pi`.
-/

open Set MeasureTheory Real
open scoped ENNReal

namespace StarKakeyaLower.OneTenth
noncomputable section

/-- A Borel representative is used only to establish measurability, not to
replace the physical section or to identify antipodal points. -/
def physicalRepresentative (q : PolarAngle) : ℝ :=
  (AddCircle.measurableEquivIoc (2*Real.pi) (-Real.pi) q : ℝ)

@[simp] theorem physicalRepresentative_coe (q : PolarAngle) :
    (physicalRepresentative q : PolarAngle) = q :=
  (AddCircle.measurableEquivIoc (2*Real.pi) (-Real.pi)).symm_apply_apply q

theorem measurable_physicalRepresentative : Measurable physicalRepresentative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc (2*Real.pi) (-Real.pi)).measurable

theorem continuous_real_polar : Continuous (fun p : ℝ × ℝ => polarPoint p.1 p.2) :=
  continuous_polarCoord_symm

/-- Joint Borel measurability in radius and the actual physical angle. -/
theorem measurable_physical_polar :
    Measurable (fun p : ℝ × PolarAngle => polarPoint p.1 (physicalRepresentative p.2)) :=
  continuous_real_polar.measurable.comp
    (measurable_fst.prodMk (measurable_physicalRepresentative.comp measurable_snd))

@[simp] theorem mem_physicalSection_iff_representative (G : Set CoordinatePlane)
    (r : ℝ) (q : PolarAngle) :
    q ∈ physicalSection G r ↔ polarPoint r (physicalRepresentative q) ∈ G := by
  have h := mem_physicalSection_coe G r (physicalRepresentative q)
  simpa only [physicalRepresentative_coe] using h

theorem measurableSet_joint_physicalSection {G : Set CoordinatePlane}
    (hG : MeasurableSet G) :
    MeasurableSet {p : ℝ × PolarAngle | p.2 ∈ physicalSection G p.1} := by
  simpa only [mem_physicalSection_iff_representative] using
    hG.preimage measurable_physical_polar

theorem measurableSet_physicalSection {G : Set CoordinatePlane}
    (hG : MeasurableSet G) (r : ℝ) : MeasurableSet (physicalSection G r) := by
  exact (measurableSet_joint_physicalSection hG).preimage
    (measurable_const.prodMk measurable_id)

theorem isOpen_joint_real_section {G : Set CoordinatePlane} (hG : IsOpen G) :
    IsOpen {p : ℝ × ℝ | polarPoint p.1 p.2 ∈ G} :=
  hG.preimage continuous_real_polar

/-- Open envelopes give open physical-circle sections, useful for the far
collar component argument; no measurability of an angular image is needed. -/
theorem isOpen_physicalSection {G : Set CoordinatePlane} (hG : IsOpen G) (r : ℝ) :
    IsOpen (physicalSection G r) := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (2*Real.pi))).isOpen_preimage.mp
  have he : (QuotientAddGroup.mk : ℝ → PolarAngle) ⁻¹' physicalSection G r =
      {θ : ℝ | polarPoint r θ ∈ G} := by
    ext θ
    exact mem_physicalSection_coe G r θ
  rw [he]
  exact hG.preimage (continuous_real_polar.comp (continuous_const.prodMk continuous_id))

/-- The exact physical Haar length, as an ENNReal to retain infinite-area cases. -/
def physicalLength (G : Set CoordinatePlane) (r : ℝ) : ℝ≥0∞ :=
  volume (physicalSection G r)

/-- The ordinary angular lower integral over one FULL turn equals physical
Haar length. Removing the one cut endpoint is a single null-set operation. -/
theorem physicalLength_eq_angular_lintegral {G : Set CoordinatePlane}
    (hG : MeasurableSet G) (r : ℝ) :
    physicalLength G r = ∫⁻ θ in Ioo (-Real.pi) Real.pi,
      G.indicator (1 : CoordinatePlane → ℝ≥0∞) (polarPoint r θ) := by
  classical
  rw [physicalLength, ← lintegral_indicator_one (measurableSet_physicalSection hG r),
    ← AddCircle.lintegral_preimage (2*Real.pi) (-Real.pi)]
  rw [show -Real.pi + 2*Real.pi = Real.pi by ring,
    ← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ)))]
  apply lintegral_congr
  intro θ
  change (if (θ : PolarAngle) ∈ physicalSection G r then (1 : ℝ≥0∞) else 0) =
    if polarPoint r θ ∈ G then 1 else 0
  rw [mem_physicalSection_coe]

/-- Direct compatibility with the pre-existing standard-cut polar API. -/
theorem physicalLength_eq_angleOuter {G : Set CoordinatePlane}
    (hG : MeasurableSet G) (r : ℝ) : physicalLength G r = angleOuter G r := by
  rw [physicalLength_eq_angular_lintegral hG]
  have hp : MeasurableSet ((fun θ : ℝ => polarPoint r θ) ⁻¹' G) :=
    hG.preimage (continuous_real_polar.comp (continuous_const.prodMk continuous_id)).measurable
  have hs : MeasurableSet (polarAngleSection G r) := measurableSet_Ioo.inter hp
  rw [angleOuter, Measure.toOuterMeasure_apply, ← lintegral_indicator_one hs,
    ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro θ
  by_cases hc : θ ∈ Ioo (-Real.pi) Real.pi <;>
    by_cases hg : polarPoint r θ ∈ G <;>
      simp only [Set.indicator, Pi.one_apply, polarAngleSection, mem_setOf_eq] <;>
      simp only [mem_Ioo] at hc <;>
      simp [hc, hg]

/-- No normalization is silently lost: the full physical circle has length 2π. -/
theorem physicalLength_le_full_turn (G : Set CoordinatePlane) (r : ℝ) :
    physicalLength G r ≤ ENNReal.ofReal (2*Real.pi) := by
  exact (measure_mono (subset_univ _)).trans_eq (AddCircle.measure_univ (2*Real.pi))

theorem measurable_physicalLength {G : Set CoordinatePlane} (hG : MeasurableSet G) :
    Measurable (physicalLength G) := by
  have hm : Measurable (fun p : ℝ × PolarAngle =>
      ({p : ℝ × PolarAngle | p.2 ∈ physicalSection G p.1}).indicator
        (1 : ℝ × PolarAngle → ℝ≥0∞) p) :=
    measurable_const.indicator (measurableSet_joint_physicalSection hG)
  have he : (fun r => ∫⁻ q : PolarAngle,
      ({p : ℝ × PolarAngle | p.2 ∈ physicalSection G p.1}).indicator
        (1 : ℝ × PolarAngle → ℝ≥0∞) (r,q)) = physicalLength G := by
    funext r
    exact lintegral_indicator_one (measurableSet_physicalSection hG r)
  rw [← he]
  exact hm.lintegral_prod_right

/-- Actual Lebesgue area, obtained from Mathlib's Jacobian theorem and Tonelli.
This is an equality, not an area hypothesis or an abstract numeric price. -/
theorem volume_eq_radial_physicalLength {G : Set CoordinatePlane}
    (hG : MeasurableSet G) :
    volume G = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * physicalLength G r := by
  have hp := lintegral_comp_polarCoord_symm (G.indicator (1 : CoordinatePlane → ℝ≥0∞))
  rw [lintegral_indicator_one hG] at hp
  rw [← hp]
  change (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 * G.indicator (1 : CoordinatePlane → ℝ≥0∞)
        (polarPoint p.1 p.2) ∂(volume.prod volume)) = _
  rw [setLIntegral_prod (s := Ioi (0 : ℝ)) (t := Ioo (-Real.pi) Real.pi)
    (fun p : ℝ × ℝ => ENNReal.ofReal p.1 *
      G.indicator (1 : CoordinatePlane → ℝ≥0∞) (polarPoint p.1 p.2))
    ((measurable_fst.ennreal_ofReal.mul
    ((measurable_const.indicator hG).comp continuous_real_polar.measurable)).aemeasurable)]
  apply lintegral_congr
  intro r
  have hm : Measurable (fun θ : ℝ =>
      G.indicator (1 : CoordinatePlane → ℝ≥0∞) (polarPoint r θ)) :=
    (measurable_const.indicator hG).comp
      (continuous_real_polar.comp (continuous_const.prodMk continuous_id)).measurable
  change (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal r *
    G.indicator (1 : CoordinatePlane → ℝ≥0∞) (polarPoint r θ)) = _
  rw [lintegral_const_mul (ENNReal.ofReal r) hm, physicalLength_eq_angular_lintegral hG]

/-- Radius-bank density with the capped Jacobian from the 1/10 argument. -/
def openBankDensity (G : Set CoordinatePlane) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (min r 1) * physicalLength G r

/-- One bank, paid only on positive radii. -/
def openBank (G : Set CoordinatePlane) : ℝ≥0∞ :=
  ∫⁻ r in Ioi (0 : ℝ), openBankDensity G r

theorem measurable_openBankDensity {G : Set CoordinatePlane} (hG : MeasurableSet G) :
    Measurable (openBankDensity G) :=
  (measurable_id.min measurable_const).ennreal_ofReal.mul (measurable_physicalLength hG)

/-- The capped physical polar bank is paid once by the ACTUAL area of G. -/
theorem openBank_le_volume {G : Set CoordinatePlane} (hG : MeasurableSet G) :
    openBank G ≤ volume G := by
  rw [volume_eq_radial_physicalLength hG]
  apply lintegral_mono
  intro r
  exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal (min_le_left r 1)) _

/-- Ordinary real angular integral, with the same unnormalized 2π Haar measure. -/
theorem physicalLength_toReal_eq_angular_integral {G : Set CoordinatePlane}
    (hG : MeasurableSet G) (r : ℝ) :
    (physicalLength G r).toReal = ∫ θ in Ioo (-Real.pi) Real.pi,
      G.indicator (1 : CoordinatePlane → ℝ) (polarPoint r θ) := by
  classical
  have hi : (∫ q : PolarAngle, (physicalSection G r).indicator (fun _ => (1 : ℝ)) q) =
      (physicalLength G r).toReal := by
    simpa [physicalLength, measureReal_def] using
      integral_indicator_const (μ := (volume : Measure PolarAngle)) (1 : ℝ)
        (measurableSet_physicalSection hG r)
  rw [← hi, ← AddCircle.integral_preimage (2*Real.pi) (-Real.pi)]
  rw [show -Real.pi + 2*Real.pi = Real.pi by ring,
    ← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ)))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ => by
    change (if (θ : PolarAngle) ∈ physicalSection G r then (1 : ℝ) else 0) =
      if polarPoint r θ ∈ G then 1 else 0
    rw [mem_physicalSection_coe]

/-- Finite angular sections make the real integral reversible, unlike an
unjustified `toReal` conversion of infinite planar area. -/
theorem physicalLength_eq_ofReal_angular_integral {G : Set CoordinatePlane}
    (hG : MeasurableSet G) (r : ℝ) :
    physicalLength G r = ENNReal.ofReal (∫ θ in Ioo (-Real.pi) Real.pi,
      G.indicator (1 : CoordinatePlane → ℝ) (polarPoint r θ)) := by
  rw [← physicalLength_toReal_eq_angular_integral hG,
    ENNReal.ofReal_toReal ((physicalLength_le_full_turn G r).trans_lt
      ENNReal.ofReal_lt_top).ne]

end
end StarKakeyaLower.OneTenth
