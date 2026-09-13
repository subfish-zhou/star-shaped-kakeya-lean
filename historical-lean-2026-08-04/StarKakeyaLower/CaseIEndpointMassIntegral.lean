import StarKakeyaLower.CaseIEndpointAnalytic
import StarKakeyaLower.AnalyticBranches

/-!
# Case-I endpoint mass and radial integral

This file keeps the mass/averaging side separate from endpoint geometry.  In
particular none of the public assembly theorems accepts `JGammaMass` or a
radial-integral lower bound as a premise.
-/

open Set MeasureTheory Real Filter
open scoped ENNReal

namespace StarKakeyaLower

noncomputable section

/-- The pointwise minorant used by the strong Case-I certificate. `strongILower`
is a lower bound for the full integral `∫ r / strongPaperG r`; the arbitrary-
family quotient-circle dilation theorem incurs no Vitali/greedy factor `1/3`. -/
def strongCaseIQ (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.pi * strongP / strongPaperG r)

/-- Strong specialization of aggregate mass. -/
theorem strongCaseI_aggregateMass_of_directionOuterMass
    {r : ℝ} {A : Set ProjectiveDirection} (hr0 : 0 ≤ r) (hrhalf : r < 1 / 2)
    (hmass : ENNReal.ofReal (Real.pi * strongP) ≤ directionOuterMass A) :
    FirstArcAggregateMass A (strongPaperG r) (strongCaseIQ r) := by
  have hg1 := one_le_strongPaperG hr0 hrhalf
  rw [FirstArcAggregateMass, strongCaseIQ]
  have hg : 0 < strongPaperG r := lt_of_lt_of_le zero_lt_one hg1
  have hmul : ENNReal.ofReal (strongPaperG r) *
      ENNReal.ofReal (Real.pi * strongP / strongPaperG r) =
      ENNReal.ofReal (Real.pi * strongP) := by
    rw [← ENNReal.ofReal_mul hg.le]
    congr 1
    field_simp
  rw [hmul]
  exact hmass

/-- A real integral estimate for `r/g(r)` converts to the exact ENNReal radial
minorant used by the outer-measure slicing theorem.  This lemma is generic in
its analytic input and is used below only with the proved strong paper bound. -/
theorem strongCaseI_lintegral_ge_of_integral_ge
    (hI : strongILower ≤
      ∫ r in Icc strongA strongR₀, r / strongPaperG r) :
    ENNReal.ofReal (Real.pi * strongP * strongILower) ≤
      ∫⁻ r in Icc strongA strongR₀, ENNReal.ofReal r * strongCaseIQ r := by
  have hga : ∀ r ∈ Icc strongA strongR₀, 0 < strongPaperG r := by
    intro r hr
    exact lt_of_lt_of_le zero_lt_one
      (one_le_strongPaperG (by
        exact (by norm_num [strongA] : 0 ≤ strongA).trans hr.1)
        (hr.2.trans_lt (by norm_num [strongR₀] : strongR₀ < 1 / 2)))
  let f : ℝ → ℝ := fun r => r / strongPaperG r
  have hfcont : ContinuousOn f (Icc strongA strongR₀) := by
    have hinter : ContinuousOn strongInteriorRatio (Icc strongA strongR₀) := by
      change ContinuousOn (fun r : ℝ => (1 + 2 * r) / (1 - 2 * r)) _
      apply ContinuousOn.div
        (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
        (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
      intro r hr hzero
      have hrhalf := hr.2.trans_lt
        (by norm_num [strongR₀] : strongR₀ < 1 / 2)
      change 1 - 2 * r = 0 at hzero
      linarith
    have hfrozen : ContinuousOn (fun _ : ℝ => strongFrozenRatio)
        (Icc strongA strongR₀) := continuousOn_const
    have hlarge : ContinuousOn strongLargeAngleRatio
        (Icc strongA strongR₀) := by
      change ContinuousOn
        (fun r : ℝ => Real.pi / (Real.pi / 2 - Real.arctan (2 * r))) _
      apply ContinuousOn.div continuousOn_const
        ((continuousOn_const.div_const 2).sub
          (Real.continuous_arctan.comp_continuousOn
            (continuousOn_const.mul continuousOn_id)))
      intro r _ hzero
      change Real.pi / 2 - Real.arctan (2 * r) = 0 at hzero
      linarith [Real.arctan_lt_pi_div_two (2 * r)]
    have hmax (u v : ℝ → ℝ) (hu : ContinuousOn u (Icc strongA strongR₀))
        (hv : ContinuousOn v (Icc strongA strongR₀)) :
        ContinuousOn (fun r => max (u r) (v r)) (Icc strongA strongR₀) := by
      simpa only [Function.comp_apply] using
        continuous_max.comp_continuousOn (hu.prodMk hv)
    apply ContinuousOn.div continuousOn_id
      (hmax _ _ hinter (hmax _ _ hfrozen hlarge))
    intro r hr hzero
    exact (hga r hr).ne' hzero
  have hfint : IntegrableOn f (Icc strongA strongR₀) :=
    hfcont.integrableOn_Icc
  have hfmeas : Measurable f := by
    dsimp [f, strongPaperG, strongInteriorRatio, strongFrozenRatio,
      strongLargeAngleRatio]
    fun_prop
  have hfnn : ∀ r ∈ Icc strongA strongR₀, 0 ≤ f r := by
    intro r hr
    exact div_nonneg ((by norm_num [strongA] : 0 ≤ strongA).trans hr.1)
      (hga r hr).le
  have hconvert := ofReal_integral_eq_lintegral_ofReal hfint
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact hfnn r hr)
  have hc0 : 0 ≤ Real.pi * strongP :=
    mul_nonneg Real.pi_pos.le (by norm_num [strongP])
  calc
    ENNReal.ofReal (Real.pi * strongP * strongILower)
        ≤ ENNReal.ofReal (Real.pi * strongP *
            (∫ r in Icc strongA strongR₀, f r)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hI hc0)
    _ = ENNReal.ofReal (Real.pi * strongP) *
          (∫⁻ r in Icc strongA strongR₀, ENNReal.ofReal (f r)) := by
      rw [ENNReal.ofReal_mul hc0, hconvert]
    _ = ∫⁻ r in Icc strongA strongR₀,
          ENNReal.ofReal (Real.pi * strongP) * ENNReal.ofReal (f r) := by
      rw [MeasureTheory.lintegral_const_mul]
      exact hfmeas.ennreal_ofReal
    _ = ∫⁻ r in Icc strongA strongR₀,
          ENNReal.ofReal r * strongCaseIQ r := by
      apply MeasureTheory.lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      have hr0 : 0 ≤ r := (by norm_num [strongA] : 0 ≤ strongA).trans hr.1
      have hg := hga r hr
      rw [strongCaseIQ, ← ENNReal.ofReal_mul hr0]
      dsimp [f]
      rw [← ENNReal.ofReal_mul hc0]
      congr 1
      field_simp

end
end StarKakeyaLower
