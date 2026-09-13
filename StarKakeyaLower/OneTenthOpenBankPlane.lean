import StarKakeyaLower.OneTenthOpenBankAssembly

/-!
# The bank in the actual Euclidean Plane of OneTenthRecovery

This adapter preserves actual area and arbitrary centers. The coordinate
bank is a preimage of the open envelope, not the image of a generated family.
-/

open Set MeasureTheory Real
open scoped ENNReal
namespace StarKakeyaLower.OneTenth
noncomputable section

/-- Public version of the actual volume-preserving Euclidean/product adapter. -/
def openBankCoordinates : Plane ≃ᵐ CoordinatePlane :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

theorem openBankCoordinates_measurePreserving :
    MeasurePreserving openBankCoordinates volume volume :=
  (MeasureTheory.volume_preserving_finTwoArrow ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

theorem continuous_openBankCoordinates_symm : Continuous openBankCoordinates.symm :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp (Homeomorph.finTwoArrow (X := ℝ)).symm.continuous

/-- The same open G, expressed in coordinates centered at o. -/
def centeredCoordinateEnvelope (o : Plane) (G : Set Plane) : Set CoordinatePlane :=
  (fun z => o + openBankCoordinates.symm z) ⁻¹' G

theorem centeredCoordinates_measurePreserving (o : Plane) :
    MeasurePreserving (fun z => o + openBankCoordinates.symm z) volume volume :=
  (measurePreserving_add_left volume o).comp openBankCoordinates_measurePreserving.symm

theorem isOpen_centeredCoordinateEnvelope (o : Plane) {G : Set Plane} (hG : IsOpen G) :
    IsOpen (centeredCoordinateEnvelope o G) :=
  hG.preimage (continuous_const.add continuous_openBankCoordinates_symm)

theorem measurableSet_centeredCoordinateEnvelope (o : Plane) {G : Set Plane}
    (hG : MeasurableSet G) : MeasurableSet (centeredCoordinateEnvelope o G) :=
  hG.preimage (centeredCoordinates_measurePreserving o).measurable

/-- No norm-convention factor: the planar measure is exactly preserved. -/
theorem volume_centeredCoordinateEnvelope (o : Plane) {G : Set Plane} (hG : MeasurableSet G) :
    volume (centeredCoordinateEnvelope o G) = volume G :=
  (centeredCoordinates_measurePreserving o).measure_preimage hG.nullMeasurableSet

theorem openBankCoordinates_symm_polarPoint (r θ : ℝ) :
    openBankCoordinates.symm (polarPoint r θ) = r • angleVector θ := by
  ext i
  fin_cases i <;> rfl

/-- Literal membership interface for triangles recovered about an arbitrary center. -/
@[simp] theorem polarPoint_mem_centeredCoordinateEnvelope (o : Plane) (G : Set Plane)
    (r θ : ℝ) :
    polarPoint r θ ∈ centeredCoordinateEnvelope o G ↔ o + r • angleVector θ ∈ G := by
  simp only [centeredCoordinateEnvelope, mem_preimage, openBankCoordinates_symm_polarPoint]

/-- Exact physical polar area formula in the original Euclidean Plane. -/
theorem volume_eq_centered_radial_physicalLength (o : Plane) {G : Set Plane}
    (hG : MeasurableSet G) :
    volume G = ∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal r * physicalLength (centeredCoordinateEnvelope o G) r := by
  rw [← volume_centeredCoordinateEnvelope o hG]
  exact volume_eq_radial_physicalLength (measurableSet_centeredCoordinateEnvelope o hG)

/-- The actual open-cover bank is paid by the actual original Plane area. -/
theorem centered_openBank_le_volume (o : Plane) {G : Set Plane} (hG : IsOpen G) :
    openBank (centeredCoordinateEnvelope o G) ≤ volume G := by
  rw [← volume_centeredCoordinateEnvelope o hG.measurableSet]
  exact openBank_le_volume (isOpen_centeredCoordinateEnvelope o hG).measurableSet

/-- Countable physical once-only radial assembly directly for OneTenthRecovery's G. -/
theorem centered_disjoint_radialBank_sum_le_volume {ι : Type*} [Countable ι]
    (o : Plane) {G : Set Plane} (hG : IsOpen G)
    (s : ι → Set ℝ) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) :
    (∑' i, radialBank (centeredCoordinateEnvelope o G) (s i)) ≤ volume G := by
  rw [← volume_centeredCoordinateEnvelope o hG.measurableSet]
  exact disjoint_radialBank_sum_le_volume
    (isOpen_centeredCoordinateEnvelope o hG).measurableSet s hs hd

end
end StarKakeyaLower.OneTenth
