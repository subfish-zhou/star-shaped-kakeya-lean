import StarKakeyaLower.OneTenthKernelIntegralsAssembly

/-! Exact F and D0 radial prices. No high-radius geometric claim is assumed
except for the explicit same-section minorants in the receipt interfaces. -/
open Set MeasureTheory Real
open scoped ENNReal Interval
namespace StarKakeyaLower.OneTenth.KernelIntegrals
noncomputable section

theorem integrable_min_one (a b : ℝ) :
    IntervalIntegrable (fun r : ℝ => min r 1) volume a b :=
  (continuous_id.inf continuous_const).intervalIntegrable a b

/-- Actual integral across the cap kink r=1. -/
theorem integral_min_one {a b : ℝ} (ha : a ≤ 1) (hb : 1 ≤ b) :
    (∫ r in a..b, min r 1) = (1-a^2)/2+(b-1) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (1 : ℝ))
    (integrable_min_one a 1) (integrable_min_one 1 b)]
  have hl : (∫ r in a..1, min r 1) = (1-a^2)/2 := by
    calc
      _ = ∫ r in a..1, r := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le ha] at hr
        exact min_eq_left hr.2
      _ = _ := by rw [integral_id]; ring
  have hr : (∫ r in 1..b, min r 1) = b-1 := by
    calc
      _ = ∫ _r in (1 : ℝ)..b, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le hb] at hr
        exact min_eq_right hr.1
      _ = _ := by simp
  rw [hl, hr]

theorem integrable_D0 : IntervalIntegrable (fun r : ℝ => min r 1 * (1/8)) volume (4/5) (6/5) :=
  (integrable_min_one _ _).mul_const _

theorem integral_D0 : (∫ r in (4/5 : ℝ)..(6/5), min r 1 * (1/8)) = 19/400 := by
  rw [intervalIntegral.integral_mul_const, integral_min_one (by norm_num) (by norm_num)]
  norm_num

/-- A constant angular minorant below the cap is priced by the actual
ordinary integral of r, with finite-interval integrability. -/
theorem integral_radial_const (a b c : ℝ) :
    (∫ r in a..b, r*c) = (b^2-a^2)/2*c := by
  rw [intervalIntegral.integral_mul_const, integral_id]

theorem integrable_radial_const (a b c : ℝ) :
    IntervalIntegrable (fun r : ℝ => r*c) volume a b :=
  (continuous_id.mul continuous_const).intervalIntegrable a b

/-- The literal three F pieces, not merely their already evaluated scalars. -/
theorem integral_F :
    (∫ r in (1/2 : ℝ)..(3/5), r*(7/30)) +
    (∫ r in (3/5 : ℝ)..(7/10), r*(29/169)) +
    (∫ r in (7/10 : ℝ)..(4/5), r*(19/179)) = 446059/13962000 := by
  rw [integral_radial_const, integral_radial_const, integral_radial_const]
  norm_num

/-- A reusable actual bounded-bank receipt for a constant section minorant. -/
theorem constant_section_receipt {G : Set CoordinatePlane} (hG : MeasurableSet G)
    {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hs : ∀ r ∈ Ioo a b, c ≤ (physicalLength G r).toReal) :
    ENNReal.ofReal ((b^2-a^2)/2*c) ≤ radialBank G (Ioo a b) := by
  rw [← integral_radial_const]
  apply integral_le_radialBank hG ha hab (integrable_radial_const a b c)
  intro r hr
  rw [min_eq_left (le_trans hr.2.le hb)]
  exact mul_le_mul_of_nonneg_left (hs r hr) (by linarith [hr.1])

/-- The D0 support really crosses 1; replacing min(r,1) by r here is wrong. -/
theorem D0_price_le_radialBank {G : Set CoordinatePlane} (hG : MeasurableSet G)
    (v : ℝ)
    (hs : ∀ r ∈ Ioo (4/5 : ℝ) (6/5), (1/8)*v ≤ (physicalLength G r).toReal) :
    ENNReal.ofReal ((19/400)*v) ≤ radialBank G (Ico (4/5 : ℝ) (6/5)) := by
  rw [radialBank_Ico_eq_Ioo]
  have h := integral_le_radialBank hG (by norm_num : (0 : ℝ) ≤ 4/5)
    (by norm_num : (4/5 : ℝ) ≤ 6/5) (integrable_D0.mul_const v)
    (fun r hr => by
      calc
        min r 1*(1/8)*v = min r 1*((1/8)*v) := by ring
        _ ≤ min r 1*(physicalLength G r).toReal :=
          mul_le_mul_of_nonneg_left (hs r hr) (le_min (by linarith [hr.1]) zero_le_one))
  rw [intervalIntegral.integral_mul_const, integral_D0] at h
  exact h

/-- Three F receipts on their actual disjoint radial rows, ready for the
all-radius assembler; this does not add three separate planar areas. -/
theorem F_price_le_radialBanks {G : Set CoordinatePlane} (hG : MeasurableSet G)
    (v : ℝ)
    (h1 : ∀ r ∈ Ioo (1/2 : ℝ) (3/5), (7/30)*v ≤ (physicalLength G r).toReal)
    (h2 : ∀ r ∈ Ioo (3/5 : ℝ) (7/10), (29/169)*v ≤ (physicalLength G r).toReal)
    (h3 : ∀ r ∈ Ioo (7/10 : ℝ) (4/5), (19/179)*v ≤ (physicalLength G r).toReal) :
    ENNReal.ofReal ((446059/13962000)*v) ≤
      radialBank G (Ico (1/2 : ℝ) (3/5)) +
      radialBank G (Ico (3/5 : ℝ) (7/10)) +
      radialBank G (Ico (7/10 : ℝ) (4/5)) := by
  have p1 := constant_section_receipt hG (by norm_num) (by norm_num) (by norm_num) h1
  have p2 := constant_section_receipt hG (by norm_num) (by norm_num) (by norm_num) h2
  have p3 := constant_section_receipt hG (by norm_num) (by norm_num) (by norm_num) h3
  rw [radialBank_Ico_eq_Ioo, radialBank_Ico_eq_Ioo, radialBank_Ico_eq_Ioo]
  have he : ((3/5 : ℝ)^2-(1/2)^2)/2*((7/30)*v) +
      ((7/10)^2-(3/5)^2)/2*((29/169)*v) +
      ((4/5)^2-(7/10)^2)/2*((19/179)*v) = (446059/13962000)*v := by ring
  rw [← he]
  exact ENNReal.ofReal_add_le.trans
    (add_le_add (ENNReal.ofReal_add_le.trans (add_le_add p1 p2)) p3)

end
end StarKakeyaLower.OneTenth.KernelIntegrals
