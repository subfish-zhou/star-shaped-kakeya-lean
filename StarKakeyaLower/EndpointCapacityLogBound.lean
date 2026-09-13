import Mathlib

/-!
# Exact logarithm bound for endpoint-capacity certificates

Three- and four-explicit-term atanh expansions give upper bounds with rigorous
rational tails. Both proofs differentiate the gap and prove its derivative
nonnegative on `[0,1)`; no external numerical certificate is assumed.
-/

open Set Real

namespace StarKakeyaLower

noncomputable section

/-- Three explicit odd terms plus a geometric tail for
`log ((1+z)/(1-z))`. -/
def logRatioThreeTermUpper (z : ℝ) : ℝ :=
  2 * (z + z ^ 3 / 3 + z ^ 5 / 5 + z ^ 7 / (7 * (1 - z ^ 2)))

private def logRatioThreeTermGap (z : ℝ) : ℝ :=
  logRatioThreeTermUpper z - Real.log ((1 + z) / (1 - z))

private theorem logRatioThreeTermGap_hasDerivAt
    {x : ℝ} (hm : -1 < x) (hp : x < 1) :
    HasDerivAt logRatioThreeTermGap
      (4 * x ^ 8 / (7 * (x - 1) ^ 2 * (x + 1) ^ 2)) x := by
  have h1 : (1 - x) ≠ 0 := by linarith
  have h2 : (1 + x) ≠ 0 := by linarith
  have hx2 : 1 - x ^ 2 ≠ 0 := by nlinarith
  have hpoly : 1 - x ^ 2 * 2 + x ^ 4 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hx2]
  have hs : 7 * (1 - x ^ 2) ≠ 0 :=
    mul_ne_zero (by norm_num) hx2
  have hu : HasDerivAt logRatioThreeTermUpper
      (2 * (1 + 3 * x ^ 2 / 3 + 5 * x ^ 4 / 5 +
        ((7 * x ^ 6) * (7 * (1 - x ^ 2)) -
          x ^ 7 * (7 * (-(2 * x)))) / (7 * (1 - x ^ 2)) ^ 2)) x := by
    unfold logRatioThreeTermUpper
    convert (((hasDerivAt_id x).add (((hasDerivAt_id x).pow 3).div_const 3)).add
      (((hasDerivAt_id x).pow 5).div_const 5)).add
      (((hasDerivAt_id x).pow 7).div
        ((hasDerivAt_const x 7).mul
          ((hasDerivAt_const x 1).sub ((hasDerivAt_id x).pow 2))) hs) |>.const_mul 2
        using 1 ;
      dsimp only [id_eq, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply] ;
      field_simp [hs, h1, h2, hx2, hpoly] ; ring_nf
  have hr : HasDerivAt (fun y : ℝ => (1 + y) / (1 - y))
      (((1 : ℝ) * (1 - x) - (1 + x) * (-1)) / (1 - x) ^ 2) x := by
    convert ((hasDerivAt_const x 1).add (hasDerivAt_id x)).div
      ((hasDerivAt_const x 1).sub (hasDerivAt_id x)) h1 using 1 ;
      dsimp only [id_eq, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply] ;
      field_simp [h1, h2] ; ring
  have hl := hr.log (div_ne_zero h2 h1)
  convert hu.sub hl using 1 ;
    dsimp only [id_eq, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply] ;
    field_simp [hs, h1, h2, hx2, hpoly] ; ring_nf ;
    rw [show 1 - x ^ 2 * 2 + x ^ 4 = (1 - x ^ 2) ^ 2 by ring] ;
    field_simp [hx2] ; ring

private theorem logRatioThreeTermGap_nonneg
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    0 ≤ logRatioThreeTermGap z := by
  obtain rfl | hzpos := hz0.eq_or_lt
  · simp [logRatioThreeTermGap, logRatioThreeTermUpper]
  have hd : DifferentiableOn ℝ logRatioThreeTermGap (Icc 0 z) := by
    intro x hx
    exact (logRatioThreeTermGap_hasDerivAt
      (by linarith [hx.1]) (by linarith [hx.2])).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn logRatioThreeTermGap (Icc 0 z) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 z) hd.continuousOn
      (hd.mono interior_subset)
    intro x hx
    rw [interior_Icc] at hx
    rw [(logRatioThreeTermGap_hasDerivAt
      (by linarith [hx.1]) (by linarith [hx.2])).deriv]
    positivity
  have h := hmono (by simp [hzpos.le]) (by simp [hzpos.le]) hzpos.le
  simpa [logRatioThreeTermGap, logRatioThreeTermUpper] using h

/-- Exact three-term atanh/log upper bound on `[0,1)`. -/
theorem log_ratio_le_three_term_tail
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Real.log ((1 + z) / (1 - z)) ≤ logRatioThreeTermUpper z :=
  sub_nonneg.mp (logRatioThreeTermGap_nonneg hz0 hz1)

/-- Four explicit odd terms plus a geometric tail for
`log ((1+z)/(1-z))`. -/
def logRatioFourTermUpper (z : ℝ) : ℝ :=
  2 * (z + z ^ 3 / 3 + z ^ 5 / 5 + z ^ 7 / 7 +
    z ^ 9 / (9 * (1 - z ^ 2)))

private def logRatioFourTermGap (z : ℝ) : ℝ :=
  logRatioFourTermUpper z - Real.log ((1 + z) / (1 - z))

private theorem logRatioFourTermGap_hasDerivAt
    {x : ℝ} (hm : -1 < x) (hp : x < 1) :
    HasDerivAt logRatioFourTermGap
      (4 * x ^ 10 / (9 * (x - 1) ^ 2 * (x + 1) ^ 2)) x := by
  have h1 : (1 - x) ≠ 0 := by linarith
  have h2 : (1 + x) ≠ 0 := by linarith
  have hx2 : 1 - x ^ 2 ≠ 0 := by nlinarith
  have hpoly : 1 - x ^ 2 * 2 + x ^ 4 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hx2]
  have hs : 9 * (1 - x ^ 2) ≠ 0 := mul_ne_zero (by norm_num) hx2
  have hu : HasDerivAt logRatioFourTermUpper
      (2 * (1 + 3 * x ^ 2 / 3 + 5 * x ^ 4 / 5 + 7 * x ^ 6 / 7 +
        ((9 * x ^ 8) * (9 * (1 - x ^ 2)) -
          x ^ 9 * (9 * (-(2 * x)))) / (9 * (1 - x ^ 2)) ^ 2)) x := by
    unfold logRatioFourTermUpper
    convert (((((hasDerivAt_id x).add (((hasDerivAt_id x).pow 3).div_const 3)).add
      (((hasDerivAt_id x).pow 5).div_const 5)).add
      (((hasDerivAt_id x).pow 7).div_const 7)).add
      (((hasDerivAt_id x).pow 9).div
        ((hasDerivAt_const x 9).mul
          ((hasDerivAt_const x 1).sub ((hasDerivAt_id x).pow 2))) hs)) |>.const_mul 2
        using 1 ;
      dsimp only [id_eq, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply] ;
      field_simp [hs, h1, h2, hx2, hpoly] ; ring_nf
  have hr : HasDerivAt (fun y : ℝ => (1 + y) / (1 - y))
      (((1 : ℝ) * (1 - x) - (1 + x) * (-1)) / (1 - x) ^ 2) x := by
    convert ((hasDerivAt_const x 1).add (hasDerivAt_id x)).div
      ((hasDerivAt_const x 1).sub (hasDerivAt_id x)) h1 using 1 <;>
      dsimp only [id_eq, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply] <;>
      field_simp [h1, h2] <;> ring
  have hl := hr.log (div_ne_zero h2 h1)
  convert hu.sub hl using 1 ;
    dsimp only [id_eq, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply] ;
    field_simp [hs, h1, h2, hx2, hpoly] ; ring_nf ;
    rw [show 1 - x ^ 2 * 2 + x ^ 4 = (1 - x ^ 2) ^ 2 by ring] ;
    field_simp [hx2] ; ring

private theorem logRatioFourTermGap_nonneg
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    0 ≤ logRatioFourTermGap z := by
  obtain rfl | hzpos := hz0.eq_or_lt
  · simp [logRatioFourTermGap, logRatioFourTermUpper]
  have hd : DifferentiableOn ℝ logRatioFourTermGap (Icc 0 z) := by
    intro x hx
    exact (logRatioFourTermGap_hasDerivAt
      (by linarith [hx.1]) (by linarith [hx.2])).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn logRatioFourTermGap (Icc 0 z) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 z) hd.continuousOn
      (hd.mono interior_subset)
    intro x hx
    rw [interior_Icc] at hx
    rw [(logRatioFourTermGap_hasDerivAt
      (by linarith [hx.1]) (by linarith [hx.2])).deriv]
    positivity
  have h := hmono (by simp [hzpos.le]) (by simp [hzpos.le]) hzpos.le
  simpa [logRatioFourTermGap, logRatioFourTermUpper] using h

/-- Exact four-term atanh/log upper bound on `[0,1)`. -/
theorem log_ratio_le_four_term_tail
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Real.log ((1 + z) / (1 - z)) ≤ logRatioFourTermUpper z :=
  sub_nonneg.mp (logRatioFourTermGap_nonneg hz0 hz1)

end

end StarKakeyaLower
