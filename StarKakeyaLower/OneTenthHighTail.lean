import StarKakeyaLower.OneTenthLobesCones
import StarKakeyaLower.OneTenthOpenBankAssembly
import StarKakeyaLower.OneTenthSourcesPartition

/-! Same-target bounded-height high tail. No source bins are changed. -/
open Set MeasureTheory Real
open scoped ENNReal
namespace StarKakeyaLower.OneTenth
noncomputable section

def highTailSupport (m : ℝ) : Set ℝ := Ico (m/2) (3*m/4)
def highTailConeBudget (m : ℝ) : ℝ := (2*m)^2 / Real.sqrt ((2*m)^2-(1/5 : ℝ)^2)
def highTailRho (m r : ℝ) : ℝ := max (highTailConeBudget m) (r/(m-r))
def highTailKernel (m r : ℝ) : ℝ := 1/(1+2*highTailRho m r)

theorem highTail_sqrt_lower {m : ℝ} (hm : 16/5 ≤ m) :
    3*m/2 ≤ Real.sqrt ((2*m)^2-(1/5 : ℝ)^2) := by
  have hrad : 0 ≤ (2*m)^2-(1/5 : ℝ)^2 := by nlinarith
  have hs := Real.sq_sqrt hrad
  have hn := Real.sqrt_nonneg ((2*m)^2-(1/5 : ℝ)^2)
  nlinarith

theorem highTail_coneBudget_le {m : ℝ} (hm : 16/5 ≤ m) :
    highTailConeBudget m ≤ 8*m/3 := by
  have hs := highTail_sqrt_lower hm
  have hp : 0 < Real.sqrt ((2*m)^2-(1/5 : ℝ)^2) := by linarith
  unfold highTailConeBudget
  apply (div_le_iff₀ hp).mpr
  nlinarith

theorem highTail_ratio_le {m r : ℝ} (hm : 16/5 ≤ m) (hr : r ≤ 3*m/4) :
    r/(m-r) ≤ 3 := by
  apply (div_le_iff₀ (by linarith : 0 < m-r)).mpr
  linarith

theorem highTail_denominator_le {m r : ℝ} (hm : 16/5 ≤ m) (hr : r ≤ 3*m/4) :
    1+2*highTailRho m r ≤ 6*m := by
  have hB := highTail_coneBudget_le hm
  have hr' := highTail_ratio_le hm hr
  unfold highTailRho
  rcases le_total (highTailConeBudget m) (r/(m-r)) with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

theorem highTail_rho_nonneg (m r : ℝ) : 0 ≤ highTailRho m r :=
  (div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)).trans (le_max_left _ _)

theorem highTail_kernel_lower {m r : ℝ} (hm : 16/5 ≤ m) (hr : r ≤ 3*m/4) :
    1/(6*m) ≤ highTailKernel m r := by
  unfold highTailKernel
  exact one_div_le_one_div_of_le (by linarith [highTail_rho_nonneg m r])
    (highTail_denominator_le hm hr)

/-- Literal lobe, including its physical inclusion. The cap branch is exactly
`general_far_cone_cap` through `bounded_far_cone_cap`; no area premise. -/
theorem highTail_far_lobe_receipt {α h p m r : ℝ}
    (hm : 16/5 ≤ m) (hh : 0 < h) (hhH : h ≤ 1/5) (hp : 1/2 ≤ p)
    (hMlo : m ≤ endpointRadius h p) (hMhi : endpointRadius h p ≤ 2*m)
    (hrlo : m/2 ≤ r) (hrhi : r ≤ 3*m/4) :
    (fun φ => polarPoint r (α+φ)) ''
      Icc (endpointAngle h p)
        (min (endpointAngle h (p-1)) (Real.arcsin (h/r))) ⊆
        supportNeedleTriangle α h (p-1/2) ∧
    0 < min (endpointAngle h (p-1)) (Real.arcsin (h/r))-endpointAngle h p ∧
    endpointAngle h p /
      (min (endpointAngle h (p-1)) (Real.arcsin (h/r))-endpointAngle h p) ≤
      highTailRho m r := by
  have hhr : h < r := by linarith
  have hrM : r < endpointRadius h p := by linarith
  have old := general_far_lobe_receipt (α := α) hh hp hhr hrM
  refine ⟨old.1, old.2.1, ?_⟩
  rcases le_total (endpointAngle h (p-1)) (Real.arcsin (h/r)) with H | H
  · rw [min_eq_left H]
    exact (bounded_far_cone_cap hh hhH (by norm_num) hp (by linarith) hMhi).trans
      (le_max_left _ _)
  · rw [min_eq_right H]
    apply (endpoint_lobe_gap hh (by linarith) hhr hrM).trans
    apply le_trans _ (le_max_right _ _)
    apply (div_le_div_iff₀ (by linarith : 0 < endpointRadius h p-r)
      (by linarith : 0 < m-r)).mpr
    nlinarith

theorem highTail_capped_weight {m r : ℝ} (hm : 16/5 ≤ m)
    (hr : r ∈ highTailSupport m) : min r 1 = 1 := by
  have hlo : m/2 ≤ r := hr.1
  exact min_eq_right (by linarith)

theorem highTailSupport_positive {m : ℝ} (hm : 16/5 ≤ m) :
    highTailSupport m ∩ Ioi 0 = highTailSupport m := by
  apply inter_eq_left.mpr
  intro r hr
  have hlo : m/2 ≤ r := hr.1
  change 0 < r
  linarith

theorem highTail_minorant_integral {m : ℝ} (hm : 16/5 ≤ m) :
    (∫ r in highTailSupport m, min r 1 * (1/(6*m))) = 1/24 := by
  have hm0 : 0 < m := by linarith
  calc
    _ = ∫ _r in Ico (m/2) (3*m/4), (1/(6*m) : ℝ) := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro r hr
      dsimp only
      rw [highTail_capped_weight hm hr, one_mul]
    _ = (3*m/4-m/2) * (1/(6*m)) := by
      simp [integral_const, Real.volume_Ico, ENNReal.toReal_ofReal, sub_nonneg.mpr
        (show m/2 ≤ 3*m/4 by linarith)]
    _ = 1/24 := by field_simp; ring

theorem highTail_price_strict : (1/(10*Real.pi) : ℝ) < 1/24 := by
  apply (div_lt_div_iff₀ (by positivity : 0 < 10*Real.pi) (by norm_num : (0 : ℝ) < 24)).mpr
  nlinarith [Real.pi_gt_three]

end
end StarKakeyaLower.OneTenth
