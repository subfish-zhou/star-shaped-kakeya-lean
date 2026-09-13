import StarKakeyaLower.OneTenthFixedHigh
import StarKakeyaLower.OneTenthKernelIntegralsHigh

/-! Actual F and D0 radial prices. No section or bank bound is assumed.
Every receipt belongs to the same physical bank of the open envelope. -/
open Set MeasureTheory Real
open scoped ENNReal
namespace StarKakeyaLower.OneTenth.FixedHigh
noncomputable section
open Sources SectionBounds

/-- The three actual F subbanks, without any repeated volume(G) charge. -/
theorem F_radial_price_three (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hVF : V ⊆ F o c)
    (G : Set Plane) (hG : IsOpen G) (htri : ∀ q ∈ V, triangle o c q ⊆ G)
    (hh : ∀ q ∈ V, |farHeight o c q| ≤ 1/5) :
    ENNReal.ofReal ((446059/13962000)*(mass V).toReal) ≤
      radialBank (centeredCoordinateEnvelope o G) (Ico (1/2 : ℝ) (3/5)) +
      radialBank (centeredCoordinateEnvelope o G) (Ico (3/5 : ℝ) (7/10)) +
      radialBank (centeredCoordinateEnvelope o G) (Ico (7/10 : ℝ) (4/5)) := by
  apply KernelIntegrals.F_price_le_radialBanks
    (isOpen_centeredCoordinateEnvelope o hG).measurableSet (mass V).toReal
  · intro r hr
    exact F_section_real1 o hc hV hVF G htri hh ⟨hr.1.le,hr.2⟩
  · intro r hr
    exact F_section_real2 o hc hV hVF G htri hh ⟨hr.1.le,hr.2⟩
  · intro r hr
    exact F_section_real3 o hc hV hVF G htri hh ⟨hr.1.le,hr.2⟩

/-- Add adjacent half-open restrictions of the SAME physical bank. -/
theorem radialBank_Ico_add_Ico (W : Set CoordinatePlane) {a b d : ℝ}
    (hab : a ≤ b) (hbd : b ≤ d) :
    radialBank W (Ico a b) + radialBank W (Ico b d) = radialBank W (Ico a d) := by
  have hd : Disjoint (Ico a b) (Ico b d) := by
    apply Set.disjoint_left.mpr
    intro r hr hs
    exact not_lt_of_ge hs.1 hr.2
  rw [← radialBank_union W measurableSet_Ico hd, Ico_union_Ico_eq_Ico hab hbd]

theorem F_three_radialBanks_eq (W : Set CoordinatePlane) :
    radialBank W (Ico (1/2 : ℝ) (3/5)) +
      radialBank W (Ico (3/5 : ℝ) (7/10)) +
      radialBank W (Ico (7/10 : ℝ) (4/5)) =
    radialBank W (Ico (1/2 : ℝ) (4/5)) := by
  rw [radialBank_Ico_add_Ico W (by norm_num) (by norm_num),
    radialBank_Ico_add_Ico W (by norm_num) (by norm_num)]

/-- F's exact paper price on its enclosing half-open radial bank. -/
theorem F_radial_price (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hVF : V ⊆ F o c)
    (G : Set Plane) (hG : IsOpen G) (htri : ∀ q ∈ V, triangle o c q ⊆ G)
    (hh : ∀ q ∈ V, |farHeight o c q| ≤ 1/5) :
    ENNReal.ofReal ((446059/13962000)*(mass V).toReal) ≤
      radialBank (centeredCoordinateEnvelope o G) (Ico (1/2 : ℝ) (4/5)) := by
  rw [← F_three_radialBanks_eq]
  exact F_radial_price_three o hc hV hVF G hG htri hh

/-- D0 uses the capped Jacobian even beyond r=1. -/
theorem D0_radial_price (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hVD : V ⊆ D o c 0)
    (G : Set Plane) (hG : IsOpen G) (htri : ∀ q ∈ V, triangle o c q ⊆ G)
    (hh : ∀ q ∈ V, |farHeight o c q| ≤ 1/5) :
    ENNReal.ofReal ((19/400)*(mass V).toReal) ≤
      radialBank (centeredCoordinateEnvelope o G) (Ico (4/5 : ℝ) (6/5)) := by
  apply KernelIntegrals.D0_price_le_radialBank
    (isOpen_centeredCoordinateEnvelope o hG).measurableSet (mass V).toReal
  intro r hr
  exact D0_section_real o hc hV hVD G htri hh ⟨hr.1.le,hr.2⟩

/-- Full actual F cut: its Borelness is derived, not requested. -/
theorem actual_F_radial_price (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    (G : Set Plane) (hG : IsOpen G)
    (htri : ∀ q ∈ F o c, triangle o c q ⊆ G)
    (hh : ∀ q ∈ F o c, |farHeight o c q| ≤ 1/5) :
    ENNReal.ofReal ((446059/13962000)*(mass (F o c)).toReal) ≤
      radialBank (centeredCoordinateEnvelope o G) (Ico (1/2 : ℝ) (4/5)) :=
  F_radial_price o hc (measurableSet_F o hc) Subset.rfl G hG htri hh

/-- Full actual D0 cut, with no finite-area or star-shaped-envelope premise. -/
theorem actual_D0_radial_price (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    (G : Set Plane) (hG : IsOpen G)
    (htri : ∀ q ∈ D o c 0, triangle o c q ⊆ G)
    (hh : ∀ q ∈ D o c 0, |farHeight o c q| ≤ 1/5) :
    ENNReal.ofReal ((19/400)*(mass (D o c 0)).toReal) ≤
      radialBank (centeredCoordinateEnvelope o G) (Ico (4/5 : ℝ) (6/5)) :=
  D0_radial_price o hc (measurableSet_D o hc 0) Subset.rfl G hG htri hh

end
end StarKakeyaLower.OneTenth.FixedHigh
