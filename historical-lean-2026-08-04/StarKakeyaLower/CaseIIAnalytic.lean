import StarKakeyaLower.CaseIISelection
import StarKakeyaLower.StrongerKernel

open Set MeasureTheory

namespace StarKakeyaLower

noncomputable section

/-- A fixed rational loss small enough to retain the strict Case-II margin. -/
def strongCaseIIEps : ℝ := 1 / 10000000000

/-- The elementary cubic lower bound for sine. -/
theorem sub_cube_six_le_sin {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 ≤ Real.sin x := by
  let g : ℝ → ℝ := fun y => Real.sin y - y + y ^ 3 / 6
  let g' : ℝ → ℝ := fun y => Real.cos y - 1 + y ^ 2 / 2
  have hgderiv : ∀ y, HasDerivAt g (g' y) y := by
    intro y
    dsimp [g, g']
    convert ((Real.hasDerivAt_sin y).sub (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 3).div_const 6) using 1 <;> simp [id_eq] <;> ring
  have hgmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      ((Real.continuous_sin.sub continuous_id).add
        ((continuous_id.pow 3).div_const 6)).continuousOn
    · intro y _
      exact (hgderiv y).hasDerivWithinAt
    · intro y _
      dsimp [g']
      linarith [Real.one_sub_sq_div_two_le_cos (x := y)]
  have h := hgmono (show (0 : ℝ) ∈ Set.Ici 0 by simp) (show x ∈ Set.Ici 0 by simpa) hx
  have hzero : g 0 = 0 := by simp [g]
  rw [hzero] at h
  dsimp [g] at h
  nlinarith

/-- The stored rational/radical certificate really bounds the inverse sine at
our geometric radius; it is not left as a transcendental hypothesis. -/
theorem strong_arcsin_ratio_lt_upper :
    Real.arcsin (strongA / strongRho) < strongArcsinUpper := by
  have hrho0 : 0 < strongRho := by linarith [strongParameterDomain.rho_gt_half]
  have hdenLower : 0 < strongR₁Lower - 1 := by norm_num [strongR₁Lower]
  have hdenlt : strongR₁Lower - 1 < strongRho := by
    rw [strongRho]
    linarith [strongParameterDomain.r₁_gt_rational_lower]
  have hxlt : strongA / strongRho < strongCaseIIX := by
    rw [strongCaseIIX]
    exact (div_lt_div_iff_of_pos_left strongParameterDomain.a_pos hrho0 hdenLower).2 hdenlt
  have hy0 : 0 < strongArcsinUpper := by
    norm_num [strongArcsinUpper, strongCaseIIX, strongA, strongR₁Lower,
      strongSqrtLower]
  have hy1 : strongArcsinUpper < 1 := by
    norm_num [strongArcsinUpper, strongCaseIIX, strongA, strongR₁Lower,
      strongSqrtLower]
  have hcubic : strongCaseIIX <
      strongArcsinUpper - strongArcsinUpper ^ 3 / 6 := by
    norm_num [strongArcsinUpper, strongCaseIIX, strongA, strongR₁Lower,
      strongSqrtLower]
  have hsin : strongCaseIIX < Real.sin strongArcsinUpper := by
    exact hcubic.trans_le (sub_cube_six_le_sin hy0.le)
  apply (Real.arcsin_lt_iff_lt_sin' ?_).2 (hxlt.trans hsin)
  exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩

@[simp] theorem strongCaseIIEps_pos : 0 < strongCaseIIEps := by
  norm_num [strongCaseIIEps]

@[simp] theorem strongCaseIIEps_lt_one : strongCaseIIEps < 1 := by
  norm_num [strongCaseIIEps]

/-- A direct Taylor certificate at the fixed rational epsilon.  In particular,
no limiting argument in `eps` is used. -/
theorem strong_caseII_kappa_rational_lower :
    (99999 / 100000 : ℝ) < caseIIKappa strongCaseIIEps := by
  let d : ℝ := Real.pi / 200000
  let y : ℝ := (99999 / 100000 : ℝ) * (Real.pi / 2)
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hdlo : (3 / 200000 : ℝ) < d := by
    dsimp [d]
    nlinarith [Real.pi_gt_three]
  have hdhi : d < (1 / 50000 : ℝ) := by
    dsimp [d]
    nlinarith [Real.pi_lt_four]
  have hdabs : |d| ≤ 1 := by
    rw [abs_of_nonneg hd0]
    exact hdhi.le.trans (by norm_num)
  have hd4 : d ^ 4 ≤ (1 / 50000 : ℝ) ^ 4 := by
    exact pow_le_pow_left₀ hd0 hdhi.le 4
  have hcosbound := Real.cos_bound hdabs
  rw [abs_of_nonneg hd0] at hcosbound
  have hcos : Real.cos d < 1 - strongCaseIIEps := by
    have hu := (abs_le.mp hcosbound).2
    norm_num [strongCaseIIEps] at hdlo hd4 ⊢
    nlinarith [sq_nonneg d]
  have hyrewrite : y = Real.pi / 2 - d := by
    dsimp [y, d]
    ring
  have hsiny : Real.sin y < 1 - strongCaseIIEps := by
    rw [hyrewrite, Real.sin_pi_div_two_sub]
    exact hcos
  have hy0 : -(Real.pi / 2) ≤ y := by
    dsimp [y]
    nlinarith [Real.pi_pos]
  have hy1 : y ≤ Real.pi / 2 := by
    dsimp [y]
    nlinarith [Real.pi_pos]
  have hxmem : 1 - strongCaseIIEps ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> norm_num [strongCaseIIEps]
  have hasinmem : Real.arcsin (1 - strongCaseIIEps) ∈
      Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨Real.neg_pi_div_two_le_arcsin _, Real.arcsin_le_pi_div_two _⟩
  have hyasin : y < Real.arcsin (1 - strongCaseIIEps) := by
    by_contra h
    have hle := Real.strictMonoOn_sin.monotoneOn hasinmem
      (show y ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from ⟨hy0, hy1⟩)
      (le_of_not_gt h)
    rw [Real.sin_arcsin hxmem.1 hxmem.2] at hle
    exact (not_lt_of_ge hle) hsiny
  rw [caseIIKappa]
  apply (lt_div_iff₀ Real.pi_pos).2
  dsimp [y] at hyasin
  nlinarith [Real.pi_pos]

/-- The fixed epsilon still leaves every low-height needle in the scaled domain. -/
theorem strongA_lt_scaled_strongRho :
    strongA < (1 - strongCaseIIEps) * strongRho := by
  have hrho := strongParameterDomain.rho_gt_half
  norm_num [strongCaseIIEps, strongA] at hrho ⊢
  nlinarith

/-- The actual fixed-epsilon coefficient strictly exceeds the coefficient
needed after the `(1-p)π` Case-II directional-mass lower bound. -/
theorem strong_caseII_fixed_coefficient_strict :
    strongTarget / (1 - strongP) <
      caseIIC strongA strongRho * caseIIKappa strongCaseIIEps / 4 := by
  have ha := strongParameterDomain.a_pos
  have hrho : 0 < strongRho := by linarith [strongParameterDomain.rho_gt_half]
  have hasin0 : 0 < Real.arcsin (strongA / strongRho) :=
    Real.arcsin_pos.2 (div_pos ha hrho)
  have hu0 : 0 < strongArcsinUpper := by
    norm_num [strongArcsinUpper, strongCaseIIX, strongA, strongR₁Lower,
      strongSqrtLower]
  have hcLower : strongA / (2 * strongArcsinUpper) < caseIIC strongA strongRho := by
    rw [caseIIC]
    exact (div_lt_div_iff_of_pos_left ha (mul_pos (by norm_num) hu0)
      (mul_pos (by norm_num) hasin0)).2
      (mul_lt_mul_of_pos_left strong_arcsin_ratio_lt_upper (by norm_num))
  have hkLower := strong_caseII_kappa_rational_lower
  have hrational : strongTarget / (1 - strongP) <
      (strongA / (2 * strongArcsinUpper)) * (99999 / 100000 : ℝ) / 4 := by
    norm_num [strongTarget, strongP, strongA, strongArcsinUpper,
      strongCaseIIX, strongR₁Lower, strongSqrtLower]
  calc
    strongTarget / (1 - strongP) <
        (strongA / (2 * strongArcsinUpper)) * (99999 / 100000 : ℝ) / 4 := hrational
    _ < caseIIC strongA strongRho * caseIIKappa strongCaseIIEps / 4 := by
      have hq0 : (0 : ℝ) < 99999 / 100000 := by norm_num
      have hc0 := caseIIC_pos ha strongParameterDomain.rho_gt_a
      calc
        _ < caseIIC strongA strongRho * (99999 / 100000 : ℝ) / 4 := by
          nlinarith [mul_lt_mul_of_pos_right hcLower hq0]
        _ < _ := by
          nlinarith [mul_lt_mul_of_pos_left hkLower hc0]

/-- The same coefficient certificate in the normalization where the final
target and the Case-II angular mass both retain their factor of `π`. -/
theorem strong_caseII_fixed_coefficient_strict_pi_normalized :
    Real.pi * strongTarget / ((1 - strongP) * Real.pi) <
      caseIIC strongA strongRho * caseIIKappa strongCaseIIEps / 4 := by
  convert strong_caseII_fixed_coefficient_strict using 1
  field_simp

/-- The strong exterior radius lies in the range required by the fixed-ball
selection theorem. -/
theorem strongRho_le_one : strongRho ≤ 1 := by
  have hradle : Real.sqrt strongR₁Radicand ≤ strongRLambda := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num [strongRLambda]
    · rw [strongR₁Radicand]
      nlinarith [sq_nonneg strongD]
  have hdenLower : 1 - 2 * strongRLambda ≤ strongR₁Denominator := by
    rw [strongR₁Denominator]
    linarith
  have hright : 0 < 2 * (1 - 2 * strongRLambda) := by norm_num [strongRLambda]
  have hnum : Real.sqrt (1 + 4 * strongD ^ 2) <
      2 * (1 - 2 * strongRLambda) := by
    apply (Real.sqrt_lt' hright).2
    have hd := strongParameterDomain.d_lt_half_a
    have hd0 := strongParameterDomain.d_pos
    norm_num [strongA, strongRLambda] at hd ⊢
    nlinarith
  have hR : strongR₁ < 2 := by
    rw [strongR₁]
    apply (div_lt_iff₀ strongParameterDomain.r₁_denominator_pos).2
    exact hnum.trans_le (mul_le_mul_of_nonneg_left hdenLower (by norm_num))
  rw [strongRho]
  linarith

/-- Universal radius Case II.  The caller supplies only the no-high alternative
and the Haar outer mass of the paper's radius-complement class.  Haar length is
bridged to the metric Hausdorff normalization used by the fixed greedy theorem;
radius membership itself supplies the outside-ball geometry, and inverse-sine
concavity is discharged analytically. -/
theorem strongCaseII_radius_branch
    {E : Set Plane} (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    (hmass : ENNReal.ofReal ((1 - strongP) * Real.pi) ≤
      StarShapedKakeya.directionOuterMeasure (K.A_out_radius strongR₁)) :
    ENNReal.ofReal (Real.pi * strongTarget) < volume.toOuterMeasure E := by
  have hangle : ENNReal.ofReal ((1 - strongP) * Real.pi) ≤
      directionAngleOuter (K.A_out_radius strongR₁) :=
    hmass.trans (directionOuterMeasure_le_directionAngleOuter _)
  have hcase := caseII_A_out_fixed_greedy_lower_bound K
    strongCaseIIEps_pos strongCaseIIEps_lt_one strongParameterDomain.a_pos
    (by simpa [strongRho] using strongParameterDomain.rho_gt_a)
    (by simpa [strongRho] using strongA_lt_scaled_strongRho)
    (by simpa [strongRho] using strongParameterDomain.rho_gt_half)
    (by simpa [strongRho] using strongRho_le_one) hhigh
  let q : ℝ := caseIIC strongA strongRho * caseIIKappa strongCaseIIEps / 4
  have hq0 : 0 < q := by
    dsimp [q]
    exact div_pos (mul_pos (caseIIC_pos strongParameterDomain.a_pos
      strongParameterDomain.rho_gt_a)
      (caseIIKappa_pos strongCaseIIEps_pos strongCaseIIEps_lt_one)) (by norm_num)
  have hmass0 : 0 < (1 - strongP) * Real.pi :=
    mul_pos (sub_pos.2 strongParameterDomain.p_lt_one) Real.pi_pos
  have hreal : Real.pi * strongTarget < q * ((1 - strongP) * Real.pi) := by
    have hc := strong_caseII_fixed_coefficient_strict
    have hp0 : 0 < 1 - strongP := sub_pos.2 strongParameterDomain.p_lt_one
    rw [div_lt_iff₀ hp0] at hc
    dsimp [q]
    nlinarith [Real.pi_pos]
  have henn : ENNReal.ofReal (Real.pi * strongTarget) <
      ENNReal.ofReal q * ENNReal.ofReal ((1 - strongP) * Real.pi) := by
    rw [← ENNReal.ofReal_mul hq0.le]
    exact (ENNReal.ofReal_lt_ofReal_iff (mul_pos hq0 hmass0)).2 hreal
  exact henn.trans_le ((mul_le_mul_left' hangle (ENNReal.ofReal q)).trans (by
    simpa [q, strongRho] using hcase))

end
end StarKakeyaLower
