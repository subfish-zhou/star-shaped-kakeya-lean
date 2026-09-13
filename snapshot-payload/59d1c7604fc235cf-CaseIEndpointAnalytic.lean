import StarKakeyaLower.CaseIAssemblyConditional

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

/-- Interior endpoint ratio in Li's Case I. -/
def strongInteriorRatio (r : ℝ) : ℝ := (1 + 2 * r) / (1 - 2 * r)

/-- The frozen-radius endpoint ratio. -/
def strongFrozenRatio : ℝ :=
  (1 + 2 * strongRLambda) / (1 - 2 * strongRLambda)

/-- Large-angle endpoint ratio. -/
def strongLargeAngleRatio (r : ℝ) : ℝ :=
  Real.pi / (Real.pi / 2 - Real.arctan (2 * r))

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

theorem strongInteriorRatio_pos {r : ℝ} (hr0 : 0 ≤ r) (hrhalf : r < 1 / 2) :
    0 < strongInteriorRatio r := by
  rw [strongInteriorRatio]
  apply div_pos <;> linarith

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

/-! ## The selected support first arc

The endpoints are computed by the closed trace decomposition itself.  The nested
`if`s make all inadmissible (and empty-trace) cases literally `none`; in
particular no default arc is silently inserted. -/

/-- The selected first arc of the support triangle with parameter `p=(δ,c)`.
It is absent when the radius/height hypotheses fail or when the actual trace is
empty. -/
noncomputable def selectedSupportFirstArc? (r α : ℝ) (p : SupportParameter) :
    Option NormalizedPolarArc :=
  if hr : 0 < r then
    if hδ0 : 0 ≤ p.1 then
      if hδr : p.1 ≤ r then
        (supportTraceFirstArcData? (α := α) (c := p.2) hr hδ0 hδr).map
          FirstArcData.firstArc
      else none
    else none
  else none

/-- The optional selector itself is rotation covariant at positive height.  This
is the convenient graph-level form of the exact presentation theorem in
`LiGeometry`; in particular it does not assume that the selected component is
locally constant. -/
theorem selectedSupportFirstArc?_add_of_pos
    {r α δ c β : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hδr : δ ≤ r) :
    selectedSupportFirstArc? r (α + β) (δ, c) =
      (selectedSupportFirstArc? r α (δ, c)).map
        (NormalizedPolarArc.rotate β) := by
  rw [selectedSupportFirstArc?, selectedSupportFirstArc?, dif_pos hr,
    dif_pos hδ.le, dif_pos hδr, dif_pos hr, dif_pos hδ.le, dif_pos hδr]
  simpa only [Option.map_map, Function.comp_apply] using
    supportTraceFirstArcData?_firstArc_rotate β hr hδ hδr

/-! ## Scalar analytic helpers and the interior contact estimate -/

/-- Strict `arctan x < x` for positive `x`.  Shared by the endpoint estimates. -/
theorem arctan_lt_self_of_pos {x : ℝ} (hx : 0 < x) :
    Real.arctan x < x := by
  have hy0 : 0 < Real.arctan x := Real.arctan_pos.mpr hx
  have hyhalf : Real.arctan x < Real.pi / 2 := Real.arctan_lt_pi_div_two x
  have h := Real.lt_tan hy0 hyhalf
  rwa [Real.tan_arctan] at h

/-- Strict `x < arcsin x` on `(0,1)`. -/
theorem self_lt_arcsin_of_pos_of_lt_one {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) : x < Real.arcsin x := by
  apply (Real.lt_arcsin_iff_sin_lt' ?_).2
  · exact Real.sin_lt hx0
  · constructor <;> linarith [Real.pi_gt_d20]

/-- Positive isosceles contact gives the strict interior estimate. -/
theorem interior_contact_strict_gap
    {r δ t αmax : ℝ} (hr0 : 0 < r) (hrhalf : r < 1 / 2)
    (hδ0 : 0 < δ) (hδr : δ < r)
    (hu : αmax = Real.arcsin (δ / r))
    (ht : t = Real.arcsin (δ / r) - Real.arctan (2 * δ)) :
    2 * αmax - t < strongInteriorRatio r * t := by
  have hx0 : 0 < δ / r := div_pos hδ0 hr0
  have hx1 : δ / r < 1 := (div_lt_one hr0).2 hδr
  have ha : δ / r < Real.arcsin (δ / r) :=
    self_lt_arcsin_of_pos_of_lt_one hx0 hx1
  have hat : Real.arctan (2 * δ) < 2 * δ :=
    arctan_lt_self_of_pos (by positivity)
  have hB : Real.arctan (2 * δ) < 2 * r * Real.arcsin (δ / r) := by
    have hm := mul_lt_mul_of_pos_left ha (show 0 < 2 * r by positivity)
    have heq : 2 * r * (δ / r) = 2 * δ := by field_simp
    rw [heq] at hm
    linarith
  have hden : 0 < 1 - 2 * r := by linarith
  rw [strongInteriorRatio, div_mul_eq_mul_div, lt_div_iff₀ hden, hu, ht]
  nlinarith

end

end StarKakeyaLower
