import StarKakeyaLower.EndpointCapacityLogBound

/-!
# Endpoint-capacity radial payment calculus

The fixed-window kernel and its exact logarithmic antiderivative.  This is the
analytic bridge between layer-cake integrals and the frozen rational/log
certificate.
-/

open Set Real MeasureTheory
open scoped Interval

namespace StarKakeyaLower

noncomputable section

/-- Fixed-window radial kernel. -/
def endpointWindowKernel (R u : ℝ) : ℝ :=
  u * (R - u) / (R + u)

private def endpointWindowAntiderivative (R u : ℝ) : ℝ :=
  -u ^ 2 / 2 + 2 * R * u - 2 * R ^ 2 * Real.log (R + u)

/-- Closed-form payment used by the exact certificate. -/
def endpointWindowPayment (R x y : ℝ) : ℝ :=
  -(y ^ 2 - x ^ 2) / 2 + 2 * R * (y - x) -
    2 * R ^ 2 * Real.log ((R + y) / (R + x))

/-- Rationalizable lower surrogate obtained by replacing the logarithm with the
shared three-term upper bound. -/
def endpointWindowPaymentLower (R x y : ℝ) : ℝ :=
  let z := (y - x) / (2 * R + x + y);
  -(y ^ 2 - x ^ 2) / 2 + 2 * R * (y - x) -
    2 * R ^ 2 * logRatioThreeTermUpper z

/-- Every nonnegative radial interval below a positive outer radius admits the
shared rational payment lower bound. -/
theorem endpointWindowPaymentLower_le
    {R x y : ℝ} (hR : 0 < R) (hx : 0 ≤ x) (hxy : x ≤ y) :
    endpointWindowPaymentLower R x y ≤ endpointWindowPayment R x y := by
  let z : ℝ := (y - x) / (2 * R + x + y)
  have hden : 0 < 2 * R + x + y := by nlinarith
  have hz0 : 0 ≤ z := by
    exact div_nonneg (sub_nonneg.mpr hxy) hden.le
  have hz1 : z < 1 := by
    rw [div_lt_one hden]
    nlinarith
  have hRx : 0 < R + x := by nlinarith
  have hone : 1 - z ≠ 0 := ne_of_gt (sub_pos.mpr hz1)
  have hratio : (R + y) / (R + x) = (1 + z) / (1 - z) := by
    apply (div_eq_div_iff (ne_of_gt hRx) hone).2
    have hzD : z * (2 * R + x + y) = y - x := by
      dsimp [z]
      field_simp [ne_of_gt hden]
    nlinarith [hzD]
  have hlog := log_ratio_le_three_term_tail hz0 hz1
  rw [← hratio] at hlog
  dsimp [endpointWindowPaymentLower, z, endpointWindowPayment]
  nlinarith [sq_nonneg R]

/-- N=64 rational lower surrogate using the frozen four-term logarithm bound. -/
def endpointWindowPaymentLowerFour (R x y : ℝ) : ℝ :=
  let z := (y - x) / (2 * R + x + y);
  -(y ^ 2 - x ^ 2) / 2 + 2 * R * (y - x) -
    2 * R ^ 2 * logRatioFourTermUpper z

/-- The four-term rational surrogate underestimates the exact payment. -/
theorem endpointWindowPaymentLowerFour_le
    {R x y : ℝ} (hR : 0 < R) (hx : 0 ≤ x) (hxy : x ≤ y) :
    endpointWindowPaymentLowerFour R x y ≤ endpointWindowPayment R x y := by
  let z : ℝ := (y - x) / (2 * R + x + y)
  have hden : 0 < 2 * R + x + y := by nlinarith
  have hz0 : 0 ≤ z := div_nonneg (sub_nonneg.mpr hxy) hden.le
  have hz1 : z < 1 := by rw [div_lt_one hden]; nlinarith
  have hRx : 0 < R + x := by nlinarith
  have hone : 1 - z ≠ 0 := ne_of_gt (sub_pos.mpr hz1)
  have hratio : (R + y) / (R + x) = (1 + z) / (1 - z) := by
    apply (div_eq_div_iff (ne_of_gt hRx) hone).2
    have hzD : z * (2 * R + x + y) = y - x := by
      dsimp [z]
      field_simp [ne_of_gt hden]
    nlinarith [hzD]
  have hlog := log_ratio_le_four_term_tail hz0 hz1
  rw [← hratio] at hlog
  dsimp [endpointWindowPaymentLowerFour, z, endpointWindowPayment]
  nlinarith [sq_nonneg R]

private theorem endpointWindowAntiderivative_hasDerivAt
    {R u : ℝ} (h : R + u ≠ 0) :
    HasDerivAt (endpointWindowAntiderivative R) (endpointWindowKernel R u) u := by
  unfold endpointWindowAntiderivative endpointWindowKernel
  convert (((((hasDerivAt_id u).pow 2).neg.div_const 2).add
    ((hasDerivAt_const u (2 * R)).mul (hasDerivAt_id u))).sub
    ((hasDerivAt_const u (2 * R ^ 2)).mul
      (((hasDerivAt_const u R).add (hasDerivAt_id u)).log
        (by simpa using h)))) using 1 ;
    dsimp ; field_simp [h] ; ring

private theorem endpointWindowKernel_continuousOn
    {R x y : ℝ} (hR : 0 < R) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ContinuousOn (endpointWindowKernel R) (uIcc x y) := by
  intro u hu
  have hu0 : 0 ≤ u := by
    rcases Set.mem_uIcc.mp hu with hu | hu <;> nlinarith
  apply ContinuousAt.continuousWithinAt
  unfold endpointWindowKernel
  fun_prop (disch := positivity)

private theorem endpointWindowPayment_eq_antiderivative_sub
    {R x y : ℝ} (hR : 0 < R) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    endpointWindowPayment R x y =
      endpointWindowAntiderivative R y - endpointWindowAntiderivative R x := by
  have hx0 : R + x ≠ 0 := by positivity
  have hy0 : R + y ≠ 0 := by positivity
  unfold endpointWindowPayment endpointWindowAntiderivative
  rw [Real.log_div hy0 hx0]
  ring

/-- Exact FTC identity for the endpoint-capacity kernel. -/
theorem intervalIntegral_endpointWindowKernel
    {R x y : ℝ} (hR : 0 < R) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∫ u in x..y, endpointWindowKernel R u = endpointWindowPayment R x y := by
  rw [endpointWindowPayment_eq_antiderivative_sub hR hx hy]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    have hu0 : 0 ≤ u := by
      rcases Set.mem_uIcc.mp hu with hu | hu <;> nlinarith
    exact endpointWindowAntiderivative_hasDerivAt (by positivity)
  · exact (endpointWindowKernel_continuousOn hR hx hy).intervalIntegrable

end

end StarKakeyaLower
