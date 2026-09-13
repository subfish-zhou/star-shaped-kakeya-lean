import StarKakeyaLower.EndpointCapacityLogBound

/-!
# One-tenth proof: exact scalar payments

These are unconditional scalar inequalities for the fixed constants of the
reviewed proof. They are NOT geometric area bounds. In particular no
physical-union receipt is assumed or promoted here.
-/

open Set Real

namespace StarKakeyaLower.OneTenth

noncomputable section

/-- Three odd terms, without the positive remainder. -/
def logRatioLower (z : ℝ) : ℝ := 2 * (z + z ^ 3 / 3 + z ^ 5 / 5)

private def lowerGap (z : ℝ) : ℝ :=
  Real.log ((1 + z) / (1 - z)) - logRatioLower z

private theorem lowerGap_hasDerivAt {x : ℝ} (hm : -1 < x) (hp : x < 1) :
    HasDerivAt lowerGap (2 * x ^ 6 / (1 - x ^ 2)) x := by
  have h1 : 1 - x ≠ 0 := by linarith
  have h2 : 1 + x ≠ 0 := by linarith
  have hx2 : 1 - x ^ 2 ≠ 0 := by nlinarith
  have hr := (((hasDerivAt_const x 1).add (hasDerivAt_id x)).div
    ((hasDerivAt_const x 1).sub (hasDerivAt_id x)) h1).log (div_ne_zero h2 h1)
  have hl := (((hasDerivAt_id x).add (((hasDerivAt_id x).pow 3).div_const 3)).add
    (((hasDerivAt_id x).pow 5).div_const 5)).const_mul 2
  convert hr.sub hl using 1 <;>
    dsimp [lowerGap, logRatioLower] <;>
    field_simp [h1, h2, hx2] <;> ring

/-- Rigorous lower partner to the existing upper-tail bound. -/
theorem logRatioLower_le {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    logRatioLower z ≤ Real.log ((1 + z) / (1 - z)) := by
  have hd : DifferentiableOn ℝ lowerGap (Icc 0 z) := by
    intro x hx
    exact (lowerGap_hasDerivAt (by linarith [hx.1])
      (by linarith [hx.2])).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn lowerGap (Icc 0 z) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 z) hd.continuousOn
      (hd.mono interior_subset)
    intro x hx
    rw [interior_Icc] at hx
    rw [(lowerGap_hasDerivAt (by linarith [hx.1]) (by linarith [hx.2])).deriv]
    apply div_nonneg (by positivity)
    nlinarith [hx.1, hx.2]
  have h := hmono (by simp [hz0]) (by simp [hz0]) hz0
  simpa [lowerGap, logRatioLower] using h

/-- The four exact integral values in the integrated-low source. -/
def C4 : ℝ := 61 / 750 - (8 / 25) * Real.log (5 / 4)
def C5 : ℝ := 87 / 800 - (1 / 2) * Real.log (17 / 14)
def C6 : ℝ := 93 / 800 - (18 / 25) * Real.log (22 / 19)
def D5 : ℝ := 69 / 800 - (1 / 2) * Real.log (20 / 17)
def price : ℝ := C4 / C6
def lowCoefficient : ℝ := 2 * C4 + C5 + (1 - price) * D5

theorem C4_bounds : (99273 / 10000000 : ℝ) < C4 ∧ C4 < 99275 / 10000000 := by
  have hl := logRatioLower_le (z := (1/9 : ℝ)) (by norm_num) (by norm_num)
  have hu := log_ratio_le_three_term_tail (z := (1/9 : ℝ)) (by norm_num) (by norm_num)
  norm_num [logRatioLower, logRatioThreeTermUpper] at hl hu
  constructor <;> unfold C4 <;> linarith

theorem C5_lower : (116719 / 10000000 : ℝ) < C5 := by
  have hu := log_ratio_le_three_term_tail (z := (3/31 : ℝ)) (by norm_num) (by norm_num)
  norm_num [logRatioThreeTermUpper] at hu
  unfold C5
  linarith

theorem C6_lower : (10694 / 1000000 : ℝ) < C6 := by
  have hu := log_ratio_le_three_term_tail (z := (3/41 : ℝ)) (by norm_num) (by norm_num)
  norm_num [logRatioThreeTermUpper] at hu
  unfold C6
  linarith

theorem D5_lower : (4990 / 1000000 : ℝ) < D5 := by
  have hu := log_ratio_le_three_term_tail (z := (3/37 : ℝ)) (by norm_num) (by norm_num)
  norm_num [logRatioThreeTermUpper] at hu
  unfold D5
  linarith

theorem C4_pos : 0 < C4 := by linarith [C4_bounds.1]
theorem C6_pos : 0 < C6 := by linarith [C6_lower]
theorem C4_lt_C6 : C4 < C6 := by linarith [C4_bounds.2, C6_lower]

theorem price_mem_Ioo : price ∈ Ioo (0 : ℝ) 1 := by
  exact ⟨div_pos C4_pos C6_pos, (div_lt_one C6_pos).mpr C4_lt_C6⟩

theorem price_mul_C6 : price * C6 = C4 :=
  div_mul_cancel₀ _ (ne_of_gt C6_pos)

/-- Exact cancellation; no area or angular statement is a hypothesis. -/
theorem low_payment_identity (b u : ℝ) :
    C4 * (2*b+u) + C5 * (b+u) + price*C6*u + (1-price)*D5*(b+u) =
      lowCoefficient * (b+u) := by
  rw [price_mul_C6]
  unfold lowCoefficient
  ring

/-- Complementary prices charge a subset of one physical source at most once.
No measurability is needed for this pointwise fact. -/
theorem complementary_indicator_le {α : Type*} (A B : Set α) (hAB : A ⊆ B) (x : α) :
    price * A.indicator (fun _ => (1 : ℝ)) x +
      (1-price) * B.indicator (fun _ => (1 : ℝ)) x ≤
        B.indicator (fun _ => (1 : ℝ)) x := by
  classical
  by_cases hx : x ∈ A
  · simp [hx, hAB hx]
  · by_cases hy : x ∈ B
    · simp [hx, hy, price_mem_Ioo.1.le]
    · simp [hx, hy]

theorem lowCoefficient_gt_floor : (637 / 20000 : ℝ) < lowCoefficient := by
  have hp : price < (929 / 1000 : ℝ) := by
    unfold price
    apply (div_lt_iff₀ C6_pos).mpr
    nlinarith [C4_bounds.2, C6_lower]
  have hD := D5_lower
  have hprod : (71/1000 : ℝ) * (4990/1000000) < (1-price)*D5 := by
    apply mul_lt_mul_of_pos_of_nonneg
    · linarith
    · exact hD
    · norm_num
    · linarith [price_mem_Ioo.2]
  unfold lowCoefficient
  nlinarith [C4_bounds.1, C5_lower]

/-- A kernel-checked pi comparison, not a decimal assumption. -/
theorem pi_gt_223_div_71 : (223 / 71 : ℝ) < Real.pi := by
  linarith [Real.pi_gt_d20]

theorem low_floor_gt_target : (1 / (10 * Real.pi) : ℝ) < 637 / 20000 := by
  apply (div_lt_iff₀ (by positivity : 0 < 10 * Real.pi)).mpr
  nlinarith [pi_gt_223_div_71]

theorem lowCoefficient_gt_target : (1 / (10 * Real.pi) : ℝ) < lowCoefficient :=
  low_floor_gt_target.trans lowCoefficient_gt_floor

/-- Three fixed finite-high rows, integrating the weight r. -/
theorem finite_high_payment :
    (7/30 : ℝ) * ((3/5)^2-(1/2)^2)/2 +
      (29/169) * ((7/10)^2-(3/5)^2)/2 +
      (19/179) * ((4/5)^2-(7/10)^2)/2 = 446059/13962000 := by norm_num

theorem finite_high_gt_target : (1 / (10 * Real.pi) : ℝ) < 446059 / 13962000 := by
  apply (div_lt_iff₀ (by positivity : 0 < 10 * Real.pi)).mpr
  nlinarith [pi_gt_223_div_71]

/-- The first-tail bank crosses r=1, so the radial weight is min(r,1). -/
theorem first_tail_payment :
    (1/8 : ℝ) * ((1^2-(4/5)^2)/2 + (6/5-1)) = 19/400 := by norm_num

theorem first_tail_gt_target : (1 / (10 * Real.pi) : ℝ) < 19 / 400 := by
  apply (div_lt_iff₀ (by positivity : 0 < 10 * Real.pi)).mpr
  nlinarith [Real.pi_gt_three]

/-- Every later scale, not a finite list of sampled scales. -/
theorem later_tail_lower {m : ℝ} (hm : 16/5 ≤ m) :
    (27/256 : ℝ) ≤ 1/8 - 1/(16*m) := by
  have hm0 : 0 < m := by linarith
  have hdiv : 1/(16*m) ≤ (5/256 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 16*m)).mpr
    nlinarith
  linarith

theorem later_tail_gt_target {m : ℝ} (hm : 16/5 ≤ m) :
    (1 / (10 * Real.pi) : ℝ) < (1/8 - 1/(16*m))/Real.pi := by
  rw [lt_div_iff₀ Real.pi_pos]
  have hpi : 1 / (10 * Real.pi) * Real.pi = (1/10 : ℝ) := by
    field_simp
  rw [hpi]
  linarith [later_tail_lower hm]

end
end StarKakeyaLower.OneTenth
