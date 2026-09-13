import StarKakeyaLower.OneTenthSectionBoundsIntervals

/-! Uniform single-far witnesses. The near label is deliberately absent:
external-foot sources need not have an opposite physical ray. -/
open Set Real
namespace StarKakeyaLower.OneTenth.SectionBounds
noncomputable section

def coneBudget (R H : ℝ) : ℝ := R^2 / Real.sqrt (R^2-H^2)
def K (R H : ℝ) : ℝ := 1/(1+2*coneBudget R H)

theorem coneBudget_nonneg (R H : ℝ) : 0 ≤ coneBudget R H := by
  unfold coneBudget
  positivity

theorem bounded_positive_far {h p r m R H : ℝ}
    (hh : 0 < h) (hhH : h ≤ H) (hH : H ≤ 1/2) (hp : 1/2 ≤ p)
    (hRH : H < R) (hMR : endpointRadius h p ≤ R)
    (hr : 0 < r) (hrm : r < m) (hmM : m ≤ endpointRadius h p) :
    LocalInterval h p r 0 (max (coneBudget R H) (r/(m-r))) := by
  have hg : 0 < endpointAngle h (p-1)-endpointAngle h p :=
    sub_pos.mpr ((endpointAngle_strictAnti hh) (by linarith))
  have hcap := bounded_far_cone_cap hh hhH hH hp hRH hMR
  change endpointAngle h p / (endpointAngle h (p-1)-endpointAngle h p) ≤ coneBudget R H at hcap
  by_cases hhr : h < r
  · have hrM := hrm.trans_le hmM
    have hlen := far_lobe_length_pos hh (by linarith : 0 ≤ p) hhr hrM
    have hgap : endpointAngle h p /
        (min (endpointAngle h (p-1)) (Real.arcsin (h/r))-endpointAngle h p) ≤
        max (coneBudget R H) (r/(m-r)) := by
      rcases le_total (endpointAngle h (p-1)) (Real.arcsin (h/r)) with ht | ht
      · rw [min_eq_left ht]
        exact hcap.trans (le_max_left _ _)
      · rw [min_eq_right ht]
        apply (endpoint_lobe_gap hh (by linarith : 0 ≤ p) hhr hrM).trans
        apply le_trans _ (le_max_right _ _)
        exact (div_le_div_iff₀ (sub_pos.mpr hrM) (sub_pos.mpr hrm)).mpr (by nlinarith)
    have he := (div_le_iff₀ hlen).mp hgap
    have hb := endpointAngle_pos h p
    refine ⟨endpointAngle h p,min (endpointAngle h (p-1)) (Real.arcsin (h/r)),
      by linarith,by linarith,by nlinarith,?_⟩
    intro α φ hφ
    exact far_lobe_subset hh (by linarith : 0 ≤ p) hhr hrM ⟨φ,hφ,rfl⟩
  · exact (cone_far hh hr (le_of_not_gt hhr) (coneBudget_nonneg R H)
      ((div_le_iff₀ hg).mp hcap)).mono (le_max_left _ _)

/-- All signed heights, zero height, all foot positions, and r=|h|. -/
theorem bounded_far {h p r m R H : ℝ}
    (hhH : |h| ≤ H) (hH : H ≤ 1/2) (hp : 1/2 ≤ p)
    (hRH : H < R) (hMR : endpointRadius |h| p ≤ R)
    (hr : 0 < r) (hrm : r < m) (hmM : m ≤ endpointRadius |h| p) :
    LocalInterval h p r 0 (max (coneBudget R H) (r/(m-r))) := by
  apply signed_far
  rcases (abs_nonneg h).eq_or_lt with hz | hz
  · rw [← hz]
    apply zero_far hr
    rw [← hz,endpointRadius_zero (by linarith : 0 ≤ p)] at hmM
    linarith
  · exact bounded_positive_far hz hhH hH hp hRH hMR hr hrm hmM

end
end StarKakeyaLower.OneTenth.SectionBounds
