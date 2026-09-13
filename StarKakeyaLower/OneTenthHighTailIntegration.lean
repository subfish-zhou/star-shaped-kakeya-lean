import StarKakeyaLower.OneTenthHighTail

/-! Ordinary real integrals and explicit interfaces to the single OpenBank. -/
open Set MeasureTheory Real
open scoped ENNReal
namespace StarKakeyaLower.OneTenth
noncomputable section

theorem highTail_constant_integral {m : ℝ} (hm : 16/5 ≤ m) (L : ℝ) :
    (∫ _r in highTailSupport m, L/(6*m)) = L/24 := by
  have hm0 : 0 < m := by linarith
  calc
    _ = (3*m/4-m/2) * (L/(6*m)) := by
      simp [highTailSupport, integral_const, Real.volume_Ico, ENNReal.toReal_ofReal,
        sub_nonneg.mpr (show m/2 ≤ 3*m/4 by linarith)]
    _ = L/24 := by field_simp; ring

theorem highTail_weighted_mass_integral {m : ℝ} (hm : 16/5 ≤ m) (L : ℝ) :
    (∫ r in highTailSupport m, min r 1 * (L/(6*m))) = L/24 := by
  calc
    _ = ∫ _r in highTailSupport m, L/(6*m) := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro r hr
      dsimp only
      rw [highTail_capped_weight hm hr, one_mul]
    _ = _ := highTail_constant_integral hm L

/-- Only the geometric pointwise section minorant is an input. The actual
ordinary integral is finite, computed and bounded by the actual radial bank. -/
theorem highTail_radialBank_receipt {G : Set CoordinatePlane} (hG : MeasurableSet G)
    {m L : ℝ} (hm : 16/5 ≤ m)
    (hsection : ∀ r ∈ highTailSupport m, L/(6*m) ≤ (physicalLength G r).toReal) :
    ENNReal.ofReal (L/24) ≤ radialBank G (highTailSupport m) := by
  have hfinite : volume (highTailSupport m) < ∞ := by simp [highTailSupport]
  have hi := integrableOn_openBankDensity_toReal hG hfinite
  rw [highTailSupport_positive hm] at hi
  rw [radialBank_eq_ofReal_integral hG hfinite, highTailSupport_positive hm]
  apply ENNReal.ofReal_le_ofReal
  rw [← highTail_constant_integral hm L]
  apply setIntegral_mono_on (integrableOn_const (by simp [highTailSupport])) hi
    measurableSet_Ico
  intro r hr
  dsimp only
  rw [openBankDensity_toReal (by have h := hr.1; change m/2 ≤ r at h; linarith),
    highTail_capped_weight hm hr, one_mul]
  exact hsection r hr

/-- ENNReal geometric interface, avoiding caller-side toReal manipulation. -/
theorem highTail_radialBank_receipt_ennreal {G : Set CoordinatePlane} (hG : MeasurableSet G)
    {m L : ℝ} (hm : 16/5 ≤ m) (hL : 0 ≤ L)
    (hsection : ∀ r ∈ highTailSupport m,
      ENNReal.ofReal (L/(6*m)) ≤ physicalLength G r) :
    ENNReal.ofReal (L/24) ≤ radialBank G (highTailSupport m) := by
  apply highTail_radialBank_receipt hG hm
  intro r hr
  have hf : physicalLength G r ≠ ∞ :=
    ne_of_lt ((physicalLength_le_full_turn G r).trans_lt ENNReal.ofReal_lt_top)
  have hh := ENNReal.toReal_mono hf (hsection r hr)
  rwa [ENNReal.toReal_ofReal (div_nonneg hL (by linarith))] at hh

/-- Feed a family minorant with the exact cone kernel directly into OpenBank. -/
theorem highTail_kernel_radialBank_receipt {G : Set CoordinatePlane} (hG : MeasurableSet G)
    {m L : ℝ} (hm : 16/5 ≤ m) (hL : 0 ≤ L)
    (hsection : ∀ r ∈ highTailSupport m,
      ENNReal.ofReal (L * highTailKernel m r) ≤ physicalLength G r) :
    ENNReal.ofReal (L/24) ≤ radialBank G (highTailSupport m) := by
  apply highTail_radialBank_receipt_ennreal hG hm hL
  intro r hr
  apply le_trans (ENNReal.ofReal_le_ofReal _) (hsection r hr)
  simpa only [div_eq_mul_inv, one_mul] using
    mul_le_mul_of_nonneg_left (highTail_kernel_lower hm hr.2.le) hL

/-- Direct CircleReceipt-shaped interface: the source length is bounded by
(1+2*rho) times the SAME physical section. This is not an area assumption. -/
theorem highTail_extension_radialBank_receipt {G : Set CoordinatePlane} (hG : MeasurableSet G)
    {m L : ℝ} (hm : 16/5 ≤ m) (hL : 0 ≤ L)
    (hsection : ∀ r ∈ highTailSupport m,
      ENNReal.ofReal L ≤ ENNReal.ofReal (1+2*highTailRho m r) * physicalLength G r) :
    ENNReal.ofReal (L/24) ≤ radialBank G (highTailSupport m) := by
  apply highTail_radialBank_receipt hG hm
  intro r hr
  have hden : 0 ≤ 1+2*highTailRho m r := by linarith [highTail_rho_nonneg m r]
  have hp : physicalLength G r < ∞ :=
    (physicalLength_le_full_turn G r).trans_lt ENNReal.ofReal_lt_top
  have hh := ENNReal.toReal_mono
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hp).ne (hsection r hr)
  rw [ENNReal.toReal_ofReal hL, ENNReal.toReal_mul, ENNReal.toReal_ofReal hden] at hh
  apply (div_le_iff₀ (by linarith : 0 < 6*m)).mpr
  have hd := mul_le_mul_of_nonneg_right (highTail_denominator_le hm hr.2.le)
    (ENNReal.toReal_nonneg : 0 ≤ (physicalLength G r).toReal)
  nlinarith

end
end StarKakeyaLower.OneTenth
