import StarKakeyaLower.CaseIAssemblyConditional
import StarKakeyaLower.SupportFirstArcSelector

/-!
# Case-I endpoint analytic closure on the stronger parameter interval

This file records the paper's literal three-branch function `g` on the stronger
parameter interval, proves that each branch is dominated by `g`, and supplies
the two analytic facts consumed downstream: the strict interior contact estimate
and the rotation-covariant selected first-arc selector.
-/

open Set MeasureTheory Real
open scoped ENNReal

namespace StarKakeyaLower

noncomputable section

/-- The frozen-radius endpoint ratio.  This is the only tuple-specific ratio;
`strongInteriorRatio` and `strongLargeAngleRatio` are parameter-free and live in
the CLEAN `Figure5EndpointDomain`. -/
def strongFrozenRatio : ℝ :=
  (1 + 2 * strongRLambda) / (1 - 2 * strongRLambda)

/-- The paper's literal maximum of the three endpoint ratios. -/
def strongPaperG (r : ℝ) : ℝ :=
  max (strongInteriorRatio r) (max strongFrozenRatio (strongLargeAngleRatio r))

theorem strongInteriorRatio_le_paperG (r : ℝ) :
    strongInteriorRatio r ≤ strongPaperG r := by
  exact le_max_left _ _

theorem strongFrozenRatio_le_paperG (r : ℝ) :
    strongFrozenRatio ≤ strongPaperG r := by
  exact le_trans (le_max_left _ _) (le_max_right _ _)

theorem strongLargeAngleRatio_le_paperG (r : ℝ) :
    strongLargeAngleRatio r ≤ strongPaperG r := by
  exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- On the radial domain used in Case I, the paper dilation factor is at least
one, as required by the quotient Haar-growth theorem. -/
theorem one_le_strongPaperG {r : ℝ} (hr0 : 0 ≤ r) (hrhalf : r < 1 / 2) :
    1 ≤ strongPaperG r := by
  apply le_trans _ (strongInteriorRatio_le_paperG r)
  rw [strongInteriorRatio]
  have hden : 0 < 1 - 2 * r := by linarith
  rw [le_div_iff₀ hden]
  linarith

/-- Strict version of the previous bound.  It is what turns the trivial
"far side of the target chart" endpoint estimate into a *strict* gap. -/
theorem one_lt_strongPaperG {r : ℝ} (hr0 : 0 < r) (hrhalf : r < 1 / 2) :
    1 < strongPaperG r := by
  apply lt_of_lt_of_le _ (strongInteriorRatio_le_paperG r)
  rw [strongInteriorRatio]
  have hden : 0 < 1 - 2 * r := by linarith
  rw [lt_div_iff₀ hden]
  linarith

/-- Below saturation the target span is automatically inside the frozen
base-ray chart.  This is the exact complement of the large-angle branch. -/
theorem strongEndpointTarget_lt_top_of_not_saturated {r t : ℝ}
    (hr0 : 0 < r) (hsat : ¬ Real.pi ≤ strongPaperG r * t) :
    t < Real.pi / 2 - Real.arctan (2 * r) := by
  have hden : 0 < Real.pi / 2 - Real.arctan (2 * r) := by
    linarith [Real.arctan_lt_pi_div_two (2 * r)]
  by_contra hge
  rw [not_lt] at hge
  apply hsat
  have hlarge : strongLargeAngleRatio r ≤ strongPaperG r :=
    strongLargeAngleRatio_le_paperG r
  have hpos : 0 < strongLargeAngleRatio r := by
    rw [strongLargeAngleRatio]
    exact div_pos Real.pi_pos hden
  calc
    Real.pi = strongLargeAngleRatio r * (Real.pi / 2 - Real.arctan (2 * r)) := by
      rw [strongLargeAngleRatio, div_mul_cancel₀]
      exact hden.ne'
    _ ≤ strongLargeAngleRatio r * t := by
      exact mul_le_mul_of_nonneg_left hge hpos.le
    _ ≤ strongPaperG r * t := by
      exact mul_le_mul_of_nonneg_right hlarge (hden.trans_le hge).le

end

end StarKakeyaLower
