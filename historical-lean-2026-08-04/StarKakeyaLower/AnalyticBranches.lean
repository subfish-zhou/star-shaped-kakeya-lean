import StarKakeyaLower.AnalyticKernel

/-!
# Analytic branch bounds for the non-iterative Case I certificate

This file pays the alternating-series obligations used to enclose the two
transcendental branch crossings.  The results are unconditional Mathlib
theorems: no branch comparison is passed in as a hypothesis.
-/

open scoped BigOperators

namespace StarKakeyaLower

noncomputable section

/-- The nonnegative coefficient in the alternating power series for arctan. -/
def atanCoeff (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n + 1) / (2 * n + 1)

theorem atanCoeff_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (atanCoeff x) := by
  apply antitone_nat_of_succ_le
  intro n
  have hpow : x ^ (2 * (n + 1) + 1) ≤ x ^ (2 * n + 1) := by
    exact pow_le_pow_of_le_one hx0 hx1 (by omega)
  have hnum : 0 ≤ x ^ (2 * n + 1) := pow_nonneg hx0 _
  dsimp [atanCoeff]
  apply div_le_div₀ hnum hpow (by positivity)
  norm_num [Nat.cast_add]

theorem atan_even_partial_lower {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (k : ℕ) :
    (∑ i ∈ Finset.range (2 * k), (-1 : ℝ) ^ i * atanCoeff x i)
      ≤ Real.arctan x := by
  have hseries := Real.hasSum_arctan (x := x) (by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]
    exact hx1)
  have htend :
      Filter.Tendsto
        (fun n => ∑ i ∈ Finset.range n,
          (-1 : ℝ) ^ i * atanCoeff x i)
        Filter.atTop (nhds (Real.arctan x)) := by
    simpa [atanCoeff, mul_div_assoc] using hseries.tendsto_sum_nat
  exact (atanCoeff_antitone hx0 hx1.le).alternating_series_le_tendsto htend k

theorem arctan_le_odd_partial {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (k : ℕ) :
    Real.arctan x ≤
      ∑ i ∈ Finset.range (2 * k + 1), (-1 : ℝ) ^ i * atanCoeff x i := by
  have hseries := Real.hasSum_arctan (x := x) (by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]
    exact hx1)
  have htend :
      Filter.Tendsto
        (fun n => ∑ i ∈ Finset.range n,
          (-1 : ℝ) ^ i * atanCoeff x i)
        Filter.atTop (nhds (Real.arctan x)) := by
    simpa [atanCoeff, mul_div_assoc] using hseries.tendsto_sum_nat
  exact (atanCoeff_antitone hx0 hx1.le).tendsto_le_alternating_series htend k

/-- Fixed rational arguments used in the two branch-crossing certificates. -/
def altXLeft : ℝ := 2 * altSwitchLeft

def altXRight : ℝ := 2 * altSwitchRight

def altYLeft : ℝ := (1 - altXLeft) / (1 + altXLeft)

def altYRight : ℝ := (1 - altXRight) / (1 + altXRight)

def altAtanYLower6 (y : ℝ) : ℝ :=
  y - y ^ 3 / 3 + y ^ 5 / 5 - y ^ 7 / 7 + y ^ 9 / 9 - y ^ 11 / 11

theorem alt_atan_yLeft_lower :
    altAtanYLower6 altYLeft ≤ Real.arctan altYLeft := by
  have h := atan_even_partial_lower
    (x := altYLeft) (by norm_num [altYLeft, altXLeft, altSwitchLeft])
    (by norm_num [altYLeft, altXLeft, altSwitchLeft]) 3
  norm_num [atanCoeff, Finset.sum_range_succ] at h
  dsimp [altAtanYLower6]
  linarith

theorem alt_atan_yRight_lower :
    altAtanYLower6 altYRight ≤ Real.arctan altYRight := by
  have h := atan_even_partial_lower
    (x := altYRight) (by norm_num [altYRight, altXRight, altSwitchRight])
    (by norm_num [altYRight, altXRight, altSwitchRight]) 3
  norm_num [atanCoeff, Finset.sum_range_succ] at h
  dsimp [altAtanYLower6]
  linarith

theorem arctan_quarter_turn {x : ℝ} (hx0 : 0 ≤ x) (_hx1 : x < 1) :
    Real.arctan x + Real.arctan ((1 - x) / (1 + x)) = Real.pi / 4 := by
  have hden : 1 + x ≠ 0 := by linarith
  have hmul : x * ((1 - x) / (1 + x)) < 1 := by
    rw [← mul_div_assoc]
    rw [div_lt_one (by linarith)]
    nlinarith
  have hsquares : 1 + x ^ 2 ≠ 0 := by positivity
  have hfrac :
      (x + (1 - x) / (1 + x)) /
          (1 - x * ((1 - x) / (1 + x))) = 1 := by
    field_simp [hden, hsquares]
    rw [show x * (1 + x) + (1 - x) = 1 + x ^ 2 by ring]
    rw [show 1 + x - x * (1 - x) = 1 + x ^ 2 by ring]
    exact div_self hsquares
  rw [Real.arctan_add hmul, hfrac, Real.arctan_one]

theorem alt_atan_xLeft_upper :
    Real.arctan altXLeft ≤ Real.pi / 4 - altAtanYLower6 altYLeft := by
  have hturn := arctan_quarter_turn
    (x := altXLeft) (by norm_num [altXLeft, altSwitchLeft])
    (by norm_num [altXLeft, altSwitchLeft])
  have hlower := alt_atan_yLeft_lower
  change Real.arctan altXLeft + Real.arctan altYLeft = Real.pi / 4 at hturn
  change Real.arctan altXLeft ≤ Real.pi / 4 - altAtanYLower6 altYLeft
  linarith

theorem alt_atan_xRight_upper :
    Real.arctan altXRight ≤ Real.pi / 4 - altAtanYLower6 altYRight := by
  have hturn := arctan_quarter_turn
    (x := altXRight) (by norm_num [altXRight, altSwitchRight])
    (by norm_num [altXRight, altSwitchRight])
  have hlower := alt_atan_yRight_lower
  change Real.arctan altXRight + Real.arctan altYRight = Real.pi / 4 at hturn
  change Real.arctan altXRight ≤ Real.pi / 4 - altAtanYLower6 altYRight
  linarith

/-- The large-angle branch is below the constant branch at the left bracket. -/
theorem alt_largeAngle_le_const_at_left :
    Real.pi / (Real.pi / 2 - Real.arctan altXLeft) ≤ altGConst := by
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hden : 0 < Real.pi / 2 - Real.arctan altXLeft := by
    linarith [Real.arctan_lt_pi_div_two altXLeft]
  have hatan := alt_atan_xLeft_upper
  have hpilo : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hpihi : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  rw [div_le_iff₀ hden]
  norm_num [altGConst, altRLambda, altAtanYLower6,
    altYLeft, altXLeft, altSwitchLeft] at hatan ⊢
  linarith

/-- The rational branch is above the large-angle branch at the right bracket. -/
theorem alt_largeAngle_le_rational_at_right :
    Real.pi / (Real.pi / 2 - Real.arctan altXRight) ≤ altGRight := by
  have hden : 0 < Real.pi / 2 - Real.arctan altXRight := by
    linarith [Real.arctan_lt_pi_div_two altXRight]
  have hatan := alt_atan_xRight_upper
  have hpilo : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hpihi : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  rw [div_le_iff₀ hden]
  norm_num [altGRight, altAtanYLower6,
    altYRight, altXRight, altSwitchRight] at hatan ⊢
  linarith

/-! ## Calculus identity for the rational-branch interval -/

def altRightIntegrand (r : ℝ) : ℝ :=
  r * (1 - 2 * r) / (1 + 2 * r)

def altRightPrimitive (r : ℝ) : ℝ :=
  -r ^ 2 / 2 + r - Real.log (1 + 2 * r) / 2

theorem hasDerivAt_altRightPrimitive {r : ℝ} (hr : 1 + 2 * r ≠ 0) :
    HasDerivAt altRightPrimitive (altRightIntegrand r) r := by
  have hinner : HasDerivAt (fun x : ℝ => 1 + 2 * x) 2 r := by
    convert (hasDerivAt_const r 1).add
      ((hasDerivAt_const r 2).mul (hasDerivAt_id r)) using 1 <;>
        simp only [id_eq] <;> ring
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 + 2 * x))
      (2 * (1 + 2 * r)⁻¹) r := by
    convert (Real.hasDerivAt_log hr).comp r hinner using 1 <;> ring
  have hprimitive : HasDerivAt altRightPrimitive
      (-r + 1 - (1 + 2 * r)⁻¹) r := by
    dsimp [altRightPrimitive]
    have hpoly := (((hasDerivAt_id r).pow 2).neg.div_const 2).add
      (hasDerivAt_id r)
    convert hpoly.sub (hlog.div_const 2) using 1 <;>
      simp only [id_eq] <;> ring
  convert hprimitive using 1
  dsimp [altRightIntegrand]
  have hr' : 1 + r * 2 ≠ 0 := by simpa [mul_comm] using hr
  field_simp [hr, hr'] <;> ring

theorem alt_right_interval_integral_exact :
    (∫ r in altSwitchRight..altR₀, altRightIntegrand r) = altIRightExact := by
  have horder : altSwitchRight ≤ altR₀ := by
    norm_num [altSwitchRight, altR₀]
  have hderiv : ∀ r ∈ Set.uIcc altSwitchRight altR₀,
      HasDerivAt altRightPrimitive (altRightIntegrand r) r := by
    intro r hr
    have hrange : r ∈ Set.Icc altSwitchRight altR₀ := by
      simpa only [Set.uIcc_of_le horder] using hr
    have hrLower : altSwitchRight ≤ r := hrange.1
    apply hasDerivAt_altRightPrimitive
    apply ne_of_gt
    norm_num [altSwitchRight] at hrLower ⊢
    linarith
  have hcont : ContinuousOn altRightIntegrand
      (Set.uIcc altSwitchRight altR₀) := by
    rw [Set.uIcc_of_le horder]
    intro r hr
    have hrLower : altSwitchRight ≤ r := hr.1
    have hden : 1 + 2 * r ≠ 0 := by
      apply ne_of_gt
      norm_num [altSwitchRight] at hrLower ⊢
      linarith
    exact ((continuousAt_id.mul
      (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))).div
        (continuousAt_const.add (continuousAt_const.mul continuousAt_id)) hden).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcont.intervalIntegrable
  rw [hFTC]
  have hlogRatio :
      Real.log (1 + 2 * altR₀) - Real.log (1 + 2 * altSwitchRight) =
        Real.log (1 + altLogX) := by
    rw [← Real.log_div (by norm_num [altR₀])
      (by norm_num [altSwitchRight])]
    congr 1
    norm_num [altLogX, altR₀, altSwitchRight]
  dsimp [altRightPrimitive, altIRightExact]
  rw [← hlogRatio]
  ring

end

end StarKakeyaLower
