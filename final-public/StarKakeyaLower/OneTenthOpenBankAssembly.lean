import StarKakeyaLower.OneTenthOpenBank

/-!
# Bounded receipts and disjoint assembly from one physical polar bank

The index below is a countable family of radial sets, NOT source labels.
Each integral measures the same physical section of `G`; overlapping angular
contributions are never summed. Zero is removed uniformly from every radial
set. Measurability and finite mass of bounded receipts are derived here.
-/

open Set MeasureTheory Real
open scoped ENNReal
namespace StarKakeyaLower.OneTenth
noncomputable section

/-- A restriction of the one global bank to a radial set. -/
def radialBank (G : Set CoordinatePlane) (s : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ r in s ∩ Ioi (0 : ℝ), openBankDensity G r

theorem radialBank_le_openBank (G : Set CoordinatePlane) (s : Set ℝ) :
    radialBank G s ≤ openBank G :=
  lintegral_mono_set inter_subset_right

theorem radialBank_le_volume {G : Set CoordinatePlane} (hG : MeasurableSet G) (s : Set ℝ) :
    radialBank G s ≤ volume G :=
  (radialBank_le_openBank G s).trans (openBank_le_volume hG)

theorem openBankDensity_le_full_turn (G : Set CoordinatePlane) (r : ℝ) :
    openBankDensity G r ≤ ENNReal.ofReal (2*Real.pi) := by
  calc
    openBankDensity G r ≤ 1 * ENNReal.ofReal (2*Real.pi) :=
      mul_le_mul' (by simpa using ENNReal.ofReal_le_ofReal (min_le_right r (1 : ℝ)))
        (physicalLength_le_full_turn G r)
    _ = _ := one_mul _

theorem openBankDensity_lt_top (G : Set CoordinatePlane) (r : ℝ) :
    openBankDensity G r < ∞ :=
  (openBankDensity_le_full_turn G r).trans_lt ENNReal.ofReal_lt_top

/-- All bounded radial restrictions are finite even when G has infinite area. -/
theorem radialBank_le_full_turn_mul_measure (G : Set CoordinatePlane) (s : Set ℝ) :
    radialBank G s ≤ ENNReal.ofReal (2*Real.pi) * volume (s ∩ Ioi (0 : ℝ)) := by
  calc
    radialBank G s ≤ ∫⁻ _r in s ∩ Ioi (0 : ℝ), ENNReal.ofReal (2*Real.pi) :=
      lintegral_mono (openBankDensity_le_full_turn G)
    _ = _ := by simp

theorem radialBank_lt_top_of_finite_measure (G : Set CoordinatePlane) {s : Set ℝ}
    (hs : volume s < ∞) : radialBank G s < ∞ :=
  (radialBank_le_full_turn_mul_measure G s).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((measure_mono inter_subset_left).trans_lt hs))

theorem radialBank_Icc_lt_top (G : Set CoordinatePlane) (a b : ℝ) :
    radialBank G (Icc a b) < ∞ :=
  radialBank_lt_top_of_finite_measure G (by simp)

/-- The real-valued capped density is genuinely integrable on every finite
radial restriction; it is not a totalized divergent Bochner integral. -/
theorem integrableOn_openBankDensity_toReal {G : Set CoordinatePlane}
    (hG : MeasurableSet G) {s : Set ℝ} (hs : volume s < ∞) :
    IntegrableOn (fun r => (openBankDensity G r).toReal) (s ∩ Ioi (0 : ℝ)) :=
  integrable_toReal_of_lintegral_ne_top (measurable_openBankDensity hG).aemeasurable
    (radialBank_lt_top_of_finite_measure G hs).ne

/-- Ordinary integral receipt, justified by measurable finite radial mass. -/
theorem radialBank_eq_ofReal_integral {G : Set CoordinatePlane}
    (hG : MeasurableSet G) {s : Set ℝ} (hs : volume s < ∞) :
    radialBank G s = ENNReal.ofReal
      (∫ r in s ∩ Ioi (0 : ℝ), (openBankDensity G r).toReal) := by
  rw [integral_toReal (measurable_openBankDensity hG).aemeasurable
    (Filter.Eventually.of_forall (openBankDensity_lt_top G))]
  exact (ENNReal.ofReal_toReal (radialBank_lt_top_of_finite_measure G hs).ne).symm

/-- Actual countable additivity on DISJOINT radial supports of the physical
bank. No planar inequality is an input. -/
theorem radialBank_iUnion {ι : Type*} [Countable ι] (G : Set CoordinatePlane)
    (s : ι → Set ℝ) (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (fun i j => Disjoint (s i) (s j))) :
    radialBank G (⋃ i, s i) = ∑' i, radialBank G (s i) := by
  unfold radialBank
  rw [iUnion_inter]
  exact lintegral_iUnion (fun i => (hs i).inter measurableSet_Ioi)
    (fun i j hij => (hd hij).mono inter_subset_left inter_subset_left) _

/-- The complete radial ledger is paid ONCE by area(G). This works for infinite
area without changing the original arbitrary set or adding boundedness. -/
theorem disjoint_radialBank_sum_le_volume {ι : Type*} [Countable ι]
    {G : Set CoordinatePlane} (hG : MeasurableSet G)
    (s : ι → Set ℝ) (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (fun i j => Disjoint (s i) (s j))) :
    (∑' i, radialBank G (s i)) ≤ volume G := by
  rw [← radialBank_iUnion G s hs hd]
  exact radialBank_le_volume hG _

/-- A lower section bound is integrated against the capped physical Jacobian
on its OWN radial support, ready for the disjoint assembly theorem. -/
theorem weighted_section_receipt {G : Set CoordinatePlane} {s : Set ℝ}
    (hs : MeasurableSet s) (f : ℝ → ℝ≥0∞)
    (hf : ∀ r ∈ s, 0 < r → f r ≤ physicalLength G r) :
    (∫⁻ r in s ∩ Ioi (0 : ℝ), ENNReal.ofReal (min r 1) * f r) ≤ radialBank G s := by
  apply setLIntegral_mono' (hs.inter measurableSet_Ioi)
  intro r hr
  exact mul_le_mul_left' (hf r hr.1 hr.2) _

/-- A direct countable geometric-minorant interface; the area bound is proved
from the actual bank, not passed as a premise. -/
theorem disjoint_weighted_section_receipts_le_volume {ι : Type*} [Countable ι]
    {G : Set CoordinatePlane} (hG : MeasurableSet G)
    (s : ι → Set ℝ) (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (f : ι → ℝ → ℝ≥0∞)
    (hf : ∀ i r, r ∈ s i → 0 < r → f i r ≤ physicalLength G r) :
    (∑' i, ∫⁻ r in s i ∩ Ioi (0 : ℝ), ENNReal.ofReal (min r 1) * f i r) ≤ volume G :=
  (ENNReal.tsum_le_tsum (fun i => weighted_section_receipt (hs i) (f i) (hf i))).trans
    (disjoint_radialBank_sum_le_volume hG s hs hd)

/-- On positive radii the real density is literally min(r,1) times ordinary
angular length; this is the interface for exact real kernel integration. -/
theorem openBankDensity_toReal {G : Set CoordinatePlane} {r : ℝ} (hr : 0 ≤ r) :
    (openBankDensity G r).toReal = min r 1 * (physicalLength G r).toReal := by
  rw [openBankDensity, ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_min hr zero_le_one)]

theorem radialBank_eq_ofReal_weighted_integral {G : Set CoordinatePlane}
    (hG : MeasurableSet G) {s : Set ℝ} (hsm : MeasurableSet s) (hs : volume s < ∞) :
    radialBank G s = ENNReal.ofReal
      (∫ r in s ∩ Ioi (0 : ℝ), min r 1 * (physicalLength G r).toReal) := by
  rw [radialBank_eq_ofReal_integral hG hs]
  congr 1
  apply setIntegral_congr_fun (hsm.inter measurableSet_Ioi)
  intro r hr
  exact openBankDensity_toReal hr.2.le

/-- A pair of disjoint radial restrictions really adds within the same bank. -/
theorem radialBank_union (G : Set CoordinatePlane) {s t : Set ℝ}
    (ht : MeasurableSet t) (hd : Disjoint s t) :
    radialBank G (s ∪ t) = radialBank G s + radialBank G t := by
  unfold radialBank
  rw [union_inter_distrib_right]
  exact lintegral_union (ht.inter measurableSet_Ioi)
    (hd.mono inter_subset_left inter_subset_left)

/-- The three low radius ranges are disjoint as physical radial banks. Their
joint payment is at most ONE area(G), not three copies of area(G). -/
theorem low_three_radialBanks_le_volume {G : Set CoordinatePlane} (hG : MeasurableSet G) :
    radialBank G (Ioo 0 (1/5 : ℝ)) +
      radialBank G (Ico (1/5 : ℝ) (7/20)) +
      radialBank G (Ico (7/20 : ℝ) (1/2)) ≤ volume G := by
  have h01 : Disjoint (Ioo (0 : ℝ) (1/5)) (Ico (1/5 : ℝ) (7/20)) := by
    apply Set.disjoint_left.mpr
    intro r h0 h1
    exact (not_lt_of_ge h1.1) h0.2
  have h012 : Disjoint ((Ioo (0 : ℝ) (1/5)) ∪ Ico (1/5 : ℝ) (7/20))
      (Ico (7/20 : ℝ) (1/2)) := by
    apply Set.disjoint_left.mpr
    intro r h01 h2
    rcases h01 with h0 | h1
    · linarith [h0.2, h2.1]
    · exact (not_lt_of_ge h2.1) h1.2
  rw [← radialBank_union G measurableSet_Ico h01,
    ← radialBank_union G measurableSet_Ico h012]
  exact radialBank_le_volume hG _

end
end StarKakeyaLower.OneTenth
