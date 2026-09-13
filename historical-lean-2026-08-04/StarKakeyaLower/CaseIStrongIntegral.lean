import StarKakeyaLower.AnalyticBranches
import StarKakeyaLower.CaseIEndpointAnalytic

/-!
# The numerical radial integral in the strong Case-I certificate

The maximum has the branch order frozen/large-angle/interior.  We use the
safe rational cuts `9/40 = .225` and `2353/10000 = .2353`; the numerical
crossings are approximately `.2250515730` and `.2352988169`.

The stored constant `strongILower` is already on the scale of the full radial
integral `∫ r / strongPaperG r` (it is about `0.021418807`), not one third of
that integral.  Thus the sound certificate below has no additional factor
three.  In particular, multiplying this particular constant by three would
state a false numerical inequality.
-/

open Set MeasureTheory Real
open scoped BigOperators

namespace StarKakeyaLower

noncomputable section

def strongSwitchLeft : ℝ := 9 / 40

def strongSwitchRight : ℝ := 2353 / 10000

def strongMiddleUpper : ℝ := strongInteriorRatio strongSwitchRight

def strongLogX : ℝ :=
  (1 + 2 * strongR₀) / (1 + 2 * strongSwitchRight) - 1

def strongLogZ : ℝ := strongLogX / (strongLogX + 2)

def strongLogGeomUpper : ℝ :=
  2 * strongLogZ + 2 * strongLogZ ^ 3 / 3 + 2 * strongLogZ ^ 5 / 5
    + 2 * strongLogZ ^ 7 / (1 - strongLogZ ^ 2)

def strongIntegralCertificate : ℝ :=
  (strongSwitchLeft ^ 2 - strongA ^ 2) / (2 * strongFrozenRatio)
    + (strongSwitchRight ^ 2 - strongSwitchLeft ^ 2) / (2 * strongMiddleUpper)
    + ((-strongR₀ ^ 2 / 2 + strongR₀)
      - (-strongSwitchRight ^ 2 / 2 + strongSwitchRight))
    - strongLogGeomUpper / 2

private theorem strong_atan_switchLeft_upper :
    Real.arctan (2 * strongSwitchLeft) ≤
      Real.pi / 4 - altAtanYLower6 ((1 - 2 * strongSwitchLeft) /
        (1 + 2 * strongSwitchLeft)) := by
  let x : ℝ := 2 * strongSwitchLeft
  let y : ℝ := (1 - x) / (1 + x)
  have hy0 : 0 ≤ y := by norm_num [y, x, strongSwitchLeft]
  have hy1 : y < 1 := by norm_num [y, x, strongSwitchLeft]
  have hl := atan_even_partial_lower hy0 hy1 3
  have hturn := arctan_quarter_turn (x := x)
    (by norm_num [x, strongSwitchLeft]) (by norm_num [x, strongSwitchLeft])
  norm_num [atanCoeff, Finset.sum_range_succ] at hl
  change Real.arctan x + Real.arctan y = Real.pi / 4 at hturn
  change Real.arctan x ≤ Real.pi / 4 - altAtanYLower6 y
  dsimp [altAtanYLower6]
  linarith

private theorem strong_large_le_frozen_at_left :
    strongLargeAngleRatio strongSwitchLeft ≤ strongFrozenRatio := by
  have hden : 0 < Real.pi / 2 - Real.arctan (2 * strongSwitchLeft) := by
    linarith [Real.arctan_lt_pi_div_two (2 * strongSwitchLeft)]
  have hatan := strong_atan_switchLeft_upper
  have hpilo := Real.pi_gt_d20
  have hpihi := Real.pi_lt_d20
  rw [strongLargeAngleRatio, div_le_iff₀ hden]
  norm_num [strongFrozenRatio, strongRLambda, altAtanYLower6,
    strongSwitchLeft] at hatan ⊢
  linarith

private theorem strong_atan_switchRight_upper :
    Real.arctan (2 * strongSwitchRight) ≤
      Real.pi / 4 - altAtanYLower6 ((1 - 2 * strongSwitchRight) /
        (1 + 2 * strongSwitchRight)) := by
  let x : ℝ := 2 * strongSwitchRight
  let y : ℝ := (1 - x) / (1 + x)
  have hy0 : 0 ≤ y := by norm_num [y, x, strongSwitchRight]
  have hy1 : y < 1 := by norm_num [y, x, strongSwitchRight]
  have hl := atan_even_partial_lower hy0 hy1 3
  have hturn := arctan_quarter_turn (x := x)
    (by norm_num [x, strongSwitchRight]) (by norm_num [x, strongSwitchRight])
  norm_num [atanCoeff, Finset.sum_range_succ] at hl
  change Real.arctan x + Real.arctan y = Real.pi / 4 at hturn
  change Real.arctan x ≤ Real.pi / 4 - altAtanYLower6 y
  dsimp [altAtanYLower6]
  linarith

private theorem strong_gap_nonneg_at_right :
    0 ≤ Real.pi * (6 * strongSwitchRight - 1) /
        (2 * (1 + 2 * strongSwitchRight)) -
      Real.arctan (2 * strongSwitchRight) := by
  have hatan := strong_atan_switchRight_upper
  have hpilo := Real.pi_gt_d20
  have hpihi := Real.pi_lt_d20
  norm_num [altAtanYLower6, strongSwitchRight] at hatan ⊢
  linarith

private theorem strong_large_le_interior
    {r : ℝ} (hr : strongSwitchRight ≤ r) (hrhalf : r < 1 / 2) :
    strongLargeAngleRatio r ≤ strongInteriorRatio r := by
  let H : ℝ → ℝ := fun x =>
    Real.pi * (6 * x - 1) / (2 * (1 + 2 * x)) - Real.arctan (2 * x)
  have hderiv (x : ℝ) (hx : 1 + 2 * x ≠ 0) : HasDerivAt H
      (4 * Real.pi / (1 + 2 * x) ^ 2 - 2 / (1 + 4 * x ^ 2)) x := by
    have hn := HasDerivAt.const_mul Real.pi
      (((hasDerivAt_id x).const_mul 6).sub_const 1)
    have hd := (((hasDerivAt_id x).const_mul 2).add_const 1).const_mul 2
    have ha := (Real.hasDerivAt_arctan (2 * x)).comp x
      ((hasDerivAt_id x).const_mul 2)
    have hdn : 2 * (2 * x + 1) ≠ 0 := by intro h; apply hx; nlinarith
    have hraw := (hn.div hd hdn).sub ha
    simp only [id_eq, Function.comp_apply, mul_one] at hraw
    have heq :
        ((Real.pi * 6 * (2 * (2 * x + 1)) -
            Real.pi * (6 * x - 1) * (2 * 2)) / (2 * (2 * x + 1)) ^ 2 -
          1 / (1 + (2 * x) ^ 2) * 2) =
        4 * Real.pi / (1 + 2 * x) ^ 2 - 2 / (1 + 4 * x ^ 2) := by
      have hq : 1 + 4 * x ^ 2 ≠ 0 := by positivity
      field_simp [hx, hq, hdn]
      have hlin : 2 * x + 1 ≠ 0 := by intro h; apply hx; nlinarith
      field_simp [hlin]
      ring
    rw [← heq]
    convert hraw using 1
    funext y
    dsimp only [H, Function.comp_apply]
    congr 2 <;> ring
  have hmono : MonotoneOn H (Ici strongSwitchRight) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici strongSwitchRight)
    · intro x hx
      have hx0 : 0 < 1 + 2 * x := by
        norm_num [strongSwitchRight] at hx ⊢
        linarith
      exact (hderiv x hx0.ne').continuousAt.continuousWithinAt
    · intro x hx
      have hxmem : strongSwitchRight < x := by simpa using hx
      have hx0 : 0 < 1 + 2 * x := by
        norm_num [strongSwitchRight] at hxmem ⊢
        linarith
      exact (hderiv x hx0.ne').differentiableAt.differentiableWithinAt
    · intro x hx
      have hxmem : strongSwitchRight < x := by simpa using hx
      have hx0 : 0 < 1 + 2 * x := by
        norm_num [strongSwitchRight] at hxmem ⊢
        linarith
      rw [(hderiv x hx0.ne').deriv]
      have hp : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have hsq1 : 0 < (1 + 2 * x) ^ 2 := sq_pos_of_pos hx0
      have hsq2 : 0 < 1 + 4 * x ^ 2 := by positivity
      rw [sub_nonneg, div_le_div_iff₀ hsq2 hsq1]
      nlinarith [sq_nonneg (2 * x - 1)]
  have hH : 0 ≤ H r := by
    have hm := hmono (show strongSwitchRight ∈ Ici strongSwitchRight by simp)
      (show r ∈ Ici strongSwitchRight by exact hr)
      hr
    dsimp [H] at hm ⊢
    linarith [strong_gap_nonneg_at_right]
  have hplus : 0 < 1 + 2 * r := by
    have : (0 : ℝ) < 1 + 2 * strongSwitchRight := by
      norm_num [strongSwitchRight]
    linarith
  have hatan : Real.arctan (2 * r) ≤
      Real.pi * (6 * r - 1) / (2 * (1 + 2 * r)) := by
    dsimp [H] at hH
    linarith
  have hcross : Real.pi * (1 - 2 * r) ≤
      (1 + 2 * r) * (Real.pi / 2 - Real.arctan (2 * r)) := by
    have h := (le_div_iff₀ (show 0 < 2 * (1 + 2 * r) by positivity)).mp hatan
    nlinarith
  have hangle : 0 < Real.pi / 2 - Real.arctan (2 * r) := by
    linarith [Real.arctan_lt_pi_div_two (2 * r)]
  have hminus : 0 < 1 - 2 * r := by linarith
  rw [strongLargeAngleRatio, strongInteriorRatio, div_le_iff₀ hangle]
  rw [div_mul_eq_mul_div, le_div_iff₀ hminus]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcross

private theorem strong_paperG_le_left {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ strongSwitchLeft) :
    strongPaperG r ≤ strongFrozenRatio := by
  have hhalf : r < 1 / 2 := by
    norm_num [strongSwitchLeft] at hr ⊢
    linarith
  have hinter : strongInteriorRatio r ≤ strongFrozenRatio := by
    rw [strongInteriorRatio, strongFrozenRatio]
    have hd1 : 0 < 1 - 2 * r := by linarith
    have hd2 : 0 < 1 - 2 * strongRLambda := by norm_num [strongRLambda]
    rw [div_le_div_iff₀ hd1 hd2]
    norm_num [strongSwitchLeft, strongRLambda] at hr ⊢
    nlinarith
  have hat : Real.arctan (2 * r) ≤ Real.arctan (2 * strongSwitchLeft) :=
    Real.arctan_mono (by linarith)
  have hlarge : strongLargeAngleRatio r ≤ strongFrozenRatio := by
    have hd : 0 < Real.pi / 2 - Real.arctan (2 * r) := by
      linarith [Real.arctan_lt_pi_div_two (2 * r)]
    rw [strongLargeAngleRatio, div_le_iff₀ hd]
    have hfix := strong_large_le_frozen_at_left
    rw [strongLargeAngleRatio] at hfix
    have hdf : 0 < Real.pi / 2 - Real.arctan (2 * strongSwitchLeft) := by
      linarith [Real.arctan_lt_pi_div_two (2 * strongSwitchLeft)]
    rw [div_le_iff₀ hdf] at hfix
    nlinarith [show 0 < strongFrozenRatio by norm_num [strongFrozenRatio, strongRLambda]]
  exact max_le hinter (max_le le_rfl hlarge)

private theorem strong_paperG_le_middle {r : ℝ}
    (hrL : strongSwitchLeft ≤ r) (hrR : r ≤ strongSwitchRight) :
    strongPaperG r ≤ strongMiddleUpper := by
  have hhalf : r < 1 / 2 := by
    norm_num [strongSwitchRight] at hrR ⊢
    linarith
  have hinter : strongInteriorRatio r ≤ strongMiddleUpper := by
    dsimp [strongMiddleUpper, strongInteriorRatio]
    have hd1 : 0 < 1 - 2 * r := by linarith
    have hd2 : 0 < 1 - 2 * strongSwitchRight := by
      norm_num [strongSwitchRight]
    rw [div_le_div_iff₀ hd1 hd2]
    nlinarith
  have hfrozen : strongFrozenRatio ≤ strongMiddleUpper := by
    norm_num [strongFrozenRatio, strongRLambda, strongMiddleUpper,
      strongInteriorRatio, strongSwitchRight]
  have hat : Real.arctan (2 * r) ≤ Real.arctan (2 * strongSwitchRight) :=
    Real.arctan_mono (by linarith)
  have hlargeR := strong_large_le_interior
    (r := strongSwitchRight) le_rfl (by norm_num [strongSwitchRight])
  have hlarge : strongLargeAngleRatio r ≤ strongMiddleUpper := by
    dsimp [strongMiddleUpper] at hlargeR ⊢
    rw [strongLargeAngleRatio] at hlargeR ⊢
    have hd : 0 < Real.pi / 2 - Real.arctan (2 * r) := by
      linarith [Real.arctan_lt_pi_div_two (2 * r)]
    have hdR : 0 < Real.pi / 2 - Real.arctan (2 * strongSwitchRight) := by
      linarith [Real.arctan_lt_pi_div_two (2 * strongSwitchRight)]
    rw [div_le_iff₀ hdR] at hlargeR
    rw [div_le_iff₀ hd]
    have hi0 : 0 < strongInteriorRatio strongSwitchRight := by
      norm_num [strongInteriorRatio, strongSwitchRight]
    nlinarith
  exact max_le hinter (max_le hfrozen hlarge)

private theorem strong_paperG_le_right {r : ℝ}
    (hr : strongSwitchRight ≤ r) (hrhalf : r < 1 / 2) :
    strongPaperG r ≤ strongInteriorRatio r := by
  have hfrozen : strongFrozenRatio ≤ strongInteriorRatio r := by
    rw [strongFrozenRatio, strongInteriorRatio]
    have hd1 : 0 < 1 - 2 * strongRLambda := by norm_num [strongRLambda]
    have hd2 : 0 < 1 - 2 * r := by linarith
    rw [div_le_div_iff₀ hd1 hd2]
    norm_num [strongRLambda, strongSwitchRight] at hr ⊢
    nlinarith
  exact max_le le_rfl (max_le hfrozen (strong_large_le_interior hr hrhalf))

private theorem strong_log_geom_upper :
    Real.log (1 + strongLogX) ≤ strongLogGeomUpper := by
  have hx : 0 ≤ strongLogX := by norm_num [strongLogX, strongR₀, strongSwitchRight]
  have hz : strongLogX / (strongLogX + 2) = strongLogZ := rfl
  have hsum := Real.hasSum_log_one_add hx
  rw [hz] at hsum
  let term : ℕ → ℝ := fun k =>
    2 * (1 / (2 * (k : ℝ) + 1)) * strongLogZ ^ (2 * k + 1)
  change HasSum term (Real.log (1 + strongLogX)) at hsum
  have hsplit := hsum.summable.sum_add_tsum_nat_add 3
  rw [hsum.tsum_eq] at hsplit
  have hz0 : 0 ≤ strongLogZ := by
    norm_num [strongLogZ, strongLogX, strongR₀, strongSwitchRight]
  have hz1 : strongLogZ < 1 := by
    norm_num [strongLogZ, strongLogX, strongR₀, strongSwitchRight]
  have hpoint : ∀ n : ℕ, term (n + 3) ≤
      2 * strongLogZ ^ 7 * (strongLogZ ^ 2) ^ n := by
    intro n
    have hd : (1 : ℝ) / (2 * ((n + 3 : ℕ) : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      norm_num [Nat.cast_add]
      positivity
    calc
      term (n + 3) ≤ 2 * strongLogZ ^ (2 * (n + 3) + 1) := by
        dsimp [term]
        apply mul_le_mul_of_nonneg_right
        · nlinarith
        · positivity
      _ = 2 * strongLogZ ^ 7 * (strongLogZ ^ 2) ^ n := by
        rw [show 2 * (n + 3) + 1 = 7 + 2 * n by omega]
        simp only [pow_add, pow_mul]
        ring
  have hterm : Summable (fun n : ℕ => term (n + 3)) := by
    simpa only [Function.comp_apply] using
      hsum.summable.comp_injective (i := fun n : ℕ => n + 3) (by
        intro m n h; exact Nat.add_right_cancel h)
  have hzsq : ‖strongLogZ ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg strongLogZ)]
    nlinarith [sq_nonneg (strongLogZ - 1)]
  have hgeom : Summable (fun n : ℕ =>
      2 * strongLogZ ^ 7 * (strongLogZ ^ 2) ^ n) :=
    (summable_geometric_of_norm_lt_one hzsq).mul_left _
  have htail : ∑' n : ℕ, term (n + 3) ≤
      2 * strongLogZ ^ 7 / (1 - strongLogZ ^ 2) := by
    calc
      ∑' n : ℕ, term (n + 3) ≤
          ∑' n : ℕ, 2 * strongLogZ ^ 7 * (strongLogZ ^ 2) ^ n :=
        hterm.tsum_le_tsum hpoint hgeom
      _ = 2 * strongLogZ ^ 7 / (1 - strongLogZ ^ 2) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg strongLogZ)]
        · rw [div_eq_mul_inv]
        · nlinarith [sq_nonneg (strongLogZ - 1)]
  rw [← hsplit]
  change (∑ i ∈ Finset.range 3, term i) + ∑' i : ℕ, term (i + 3) ≤ _
  calc
    _ ≤ (∑ i ∈ Finset.range 3, term i) +
        2 * strongLogZ ^ 7 / (1 - strongLogZ ^ 2) := add_le_add_right htail _
    _ = strongLogGeomUpper := by
      norm_num [term, strongLogGeomUpper, Finset.sum_range_succ]
      ring

private theorem integral_r_div_const (a b c : ℝ) (hc : c ≠ 0) :
    (∫ r in a..b, r / c) = (b ^ 2 - a ^ 2) / (2 * c) := by
  have hd : ∀ r ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ => x ^ 2 / (2 * c)) (r / c) r := by
    intro r _
    convert (((hasDerivAt_id r).pow 2).div_const (2 * c)) using 1 <;>
      simp only [id_eq] <;> field_simp <;> ring
  have hi : IntervalIntegrable (fun r : ℝ => r / c) volume a b := by
    exact (continuous_id.div_const c).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  field_simp

private theorem strong_right_integral_exact :
    (∫ r in strongSwitchRight..strongR₀, r / strongInteriorRatio r) =
      ((-strongR₀ ^ 2 / 2 + strongR₀)
        - (-strongSwitchRight ^ 2 / 2 + strongSwitchRight))
      - Real.log (1 + strongLogX) / 2 := by
  have h := alt_right_interval_integral_exact
  have hd : ∀ r ∈ Set.uIcc strongSwitchRight strongR₀,
      HasDerivAt altRightPrimitive (r / strongInteriorRatio r) r := by
    intro r hr
    have horder : strongSwitchRight ≤ strongR₀ := by
      norm_num [strongSwitchRight, strongR₀]
    have hrange : r ∈ Icc strongSwitchRight strongR₀ := by
      simpa [Set.uIcc_of_le horder] using hr
    have hn : 1 + 2 * r ≠ 0 := by
      apply ne_of_gt
      norm_num [strongSwitchRight] at hrange ⊢
      linarith
    convert hasDerivAt_altRightPrimitive hn using 1
    dsimp [altRightIntegrand, strongInteriorRatio]
    field_simp
  have hi : IntervalIntegrable (fun r => r / strongInteriorRatio r) volume
      strongSwitchRight strongR₀ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num [strongSwitchRight, strongR₀])]
    intro r hr
    apply ContinuousAt.continuousWithinAt
    dsimp [strongInteriorRatio]
    have hn : 1 - 2 * r ≠ 0 := by
      norm_num [strongSwitchRight, strongR₀] at hr ⊢
      linarith
    have hp : 1 + 2 * r ≠ 0 := by
      norm_num [strongSwitchRight] at hr ⊢
      linarith
    have hratio : (1 + 2 * r) / (1 - 2 * r) ≠ 0 := div_ne_zero hp hn
    exact continuousAt_id.div
      ((continuousAt_const.add (continuousAt_const.mul continuousAt_id)).div
        (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)) hn)
      hratio
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  have hratio : Real.log (1 + 2 * strongR₀) -
      Real.log (1 + 2 * strongSwitchRight) = Real.log (1 + strongLogX) := by
    rw [← Real.log_div (by norm_num [strongR₀])
      (by norm_num [strongSwitchRight])]
    congr 1
    norm_num [strongLogX, strongR₀, strongSwitchRight]
  dsimp [altRightPrimitive]
  rw [← hratio]
  ring

theorem strong_integral_certificate_ge :
    strongILower ≤ strongIntegralCertificate := by
  norm_num [strongILower, strongIntegralCertificate, strongLogGeomUpper,
    strongLogZ, strongLogX, strongA, strongR₀, strongSwitchLeft,
    strongSwitchRight, strongFrozenRatio, strongRLambda, strongMiddleUpper,
    strongInteriorRatio]

theorem strongILower_le_integral :
    strongILower ≤ ∫ r in Icc strongA strongR₀, r / strongPaperG r := by
  let f : ℝ → ℝ := fun r => r / strongPaperG r
  have hcont : ContinuousOn f (Icc strongA strongR₀) := by
    intro r hr
    apply ContinuousAt.continuousWithinAt
    have hhalf : r < 1 / 2 := hr.2.trans_lt (by norm_num [strongR₀])
    have hnrat : 1 - 2 * r ≠ 0 := by linarith
    have hnplus : 1 + 2 * r ≠ 0 := by
      have : 0 ≤ r := (by norm_num [strongA] : 0 ≤ strongA).trans hr.1
      linarith
    have hnang : Real.pi / 2 - Real.arctan (2 * r) ≠ 0 := by
      exact ne_of_gt (by linarith [Real.arctan_lt_pi_div_two (2 * r)])
    apply ContinuousAt.div
    · fun_prop
    · have hinter : ContinuousAt strongInteriorRatio r := by
        dsimp [strongInteriorRatio]
        exact (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).div
          (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)) hnrat
      have hlarge : ContinuousAt strongLargeAngleRatio r := by
        dsimp [strongLargeAngleRatio]
        exact continuousAt_const.div
          (continuousAt_const.sub (Real.continuous_arctan.continuousAt.comp
            (continuousAt_const.mul continuousAt_id))) hnang
      change ContinuousAt
        (fun x => max (strongInteriorRatio x)
          (max strongFrozenRatio (strongLargeAngleRatio x))) r
      fun_prop
    · intro hzero
      have hg := one_le_strongPaperG
        ((by norm_num [strongA] : 0 ≤ strongA).trans hr.1)
        hhalf
      exact (ne_of_gt (lt_of_lt_of_le zero_lt_one hg)) hzero
  have hf : IntervalIntegrable f volume strongA strongR₀ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num [strongA, strongR₀])]
    exact hcont
  have hAL : strongA ≤ strongSwitchLeft := by norm_num [strongA, strongSwitchLeft]
  have hLR : strongSwitchLeft ≤ strongSwitchRight := by
    norm_num [strongSwitchLeft, strongSwitchRight]
  have hRR : strongSwitchRight ≤ strongR₀ := by
    norm_num [strongSwitchRight, strongR₀]
  have hfL : IntervalIntegrable f volume strongA strongSwitchLeft := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hAL]
    exact hcont.mono (Icc_subset_Icc le_rfl (hLR.trans hRR))
  have hfM : IntervalIntegrable f volume strongSwitchLeft strongSwitchRight := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hLR]
    exact hcont.mono (Icc_subset_Icc hAL hRR)
  have hfR : IntervalIntegrable f volume strongSwitchRight strongR₀ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hRR]
    exact hcont.mono (Icc_subset_Icc (hAL.trans hLR) le_rfl)
  have hleft : (∫ r in strongA..strongSwitchLeft, r / strongFrozenRatio) ≤
      ∫ r in strongA..strongSwitchLeft, f r := by
    apply intervalIntegral.integral_mono_on hAL
      ((continuous_id.div_const strongFrozenRatio).intervalIntegrable _ _) hfL
    intro r hr
    apply div_le_div_of_nonneg_left
      ((by norm_num [strongA] : 0 ≤ strongA).trans hr.1)
      (lt_of_lt_of_le zero_lt_one (one_le_strongPaperG
        ((by norm_num [strongA] : 0 ≤ strongA).trans hr.1)
        (hr.2.trans_lt (by norm_num [strongSwitchLeft]))))
    exact strong_paperG_le_left
      ((by norm_num [strongA] : 0 ≤ strongA).trans hr.1) hr.2
  have hmiddle : (∫ r in strongSwitchLeft..strongSwitchRight,
      r / strongMiddleUpper) ≤ ∫ r in strongSwitchLeft..strongSwitchRight, f r := by
    apply intervalIntegral.integral_mono_on hLR
      ((continuous_id.div_const strongMiddleUpper).intervalIntegrable _ _) hfM
    intro r hr
    apply div_le_div_of_nonneg_left
      ((by norm_num [strongSwitchLeft] : 0 ≤ strongSwitchLeft).trans hr.1)
      (lt_of_lt_of_le zero_lt_one (one_le_strongPaperG
        ((by norm_num [strongSwitchLeft] : 0 ≤ strongSwitchLeft).trans hr.1)
        (hr.2.trans_lt (by norm_num [strongSwitchRight]))))
    exact strong_paperG_le_middle hr.1 hr.2
  have hright : (∫ r in strongSwitchRight..strongR₀,
      r / strongInteriorRatio r) ≤ ∫ r in strongSwitchRight..strongR₀, f r := by
    apply intervalIntegral.integral_mono_on hRR (by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hRR]
      intro r hr
      apply ContinuousAt.continuousWithinAt
      dsimp [strongInteriorRatio]
      have hn : 1 - 2 * r ≠ 0 := by
        norm_num [strongR₀] at hr ⊢
        linarith
      have hp : 1 + 2 * r ≠ 0 := by
        norm_num [strongSwitchRight] at hr ⊢
        linarith
      have hratio : (1 + 2 * r) / (1 - 2 * r) ≠ 0 := div_ne_zero hp hn
      exact continuousAt_id.div
        ((continuousAt_const.add (continuousAt_const.mul continuousAt_id)).div
          (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)) hn)
        hratio) hfR
    intro r hr
    apply div_le_div_of_nonneg_left
      ((by norm_num [strongSwitchRight] : 0 ≤ strongSwitchRight).trans hr.1)
      (lt_of_lt_of_le zero_lt_one (one_le_strongPaperG
        ((by norm_num [strongSwitchRight] : 0 ≤ strongSwitchRight).trans hr.1)
        (hr.2.trans_lt (by norm_num [strongR₀]))))
    exact strong_paperG_le_right hr.1 (hr.2.trans_lt (by norm_num [strongR₀]))
  have hsum : strongIntegralCertificate ≤ ∫ r in strongA..strongR₀, f r := by
    have hcert : strongIntegralCertificate ≤
        (∫ r in strongA..strongSwitchLeft, r / strongFrozenRatio) +
        (∫ r in strongSwitchLeft..strongSwitchRight, r / strongMiddleUpper) +
        (∫ r in strongSwitchRight..strongR₀, r / strongInteriorRatio r) := by
      rw [integral_r_div_const strongA strongSwitchLeft strongFrozenRatio
        (by norm_num [strongFrozenRatio, strongRLambda])]
      rw [integral_r_div_const strongSwitchLeft strongSwitchRight strongMiddleUpper
        (by norm_num [strongMiddleUpper, strongInteriorRatio, strongSwitchRight])]
      rw [strong_right_integral_exact]
      dsimp [strongIntegralCertificate]
      linarith [strong_log_geom_upper]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hfL.trans hfM) hfR]
    rw [← intervalIntegral.integral_add_adjacent_intervals hfL hfM]
    linarith [hcert, hleft, hmiddle, hright]
  calc
    strongILower ≤ strongIntegralCertificate := strong_integral_certificate_ge
    _ ≤ ∫ r in strongA..strongR₀, f r := hsum
    _ = ∫ r in Icc strongA strongR₀, r / strongPaperG r := by
      rw [intervalIntegral.integral_of_le (by norm_num [strongA, strongR₀]),
        MeasureTheory.integral_Icc_eq_integral_Ioc]

end
end StarKakeyaLower
