import Mathlib

/-!
# Parametric analytic and algebraic kernel for Case II

This file formalizes the parameter inequalities and the coefficient elimination
used in the parametric extension of Li's Theorem 3.5.  It does **not** assert
the geometric selection theorem, pairwise disjointness of selected triangles,
or the outer-measure radial-fan formula.

The definitions retain all parameters explicitly.  In particular, the final
elimination theorem starts from the two lower bounds produced by the geometric
and measure-theoretic layers; it does not assume the desired conclusion.
-/

namespace StarKakeyaLower

noncomputable section

/-- The parametric Case-II weight attached to height cap `a` and exterior
radius `rho`. -/
def caseIIC (a rho : ℝ) : ℝ :=
  a / (2 * Real.arcsin (a / rho))

/-- The loss in the epsilon-greedy selection. -/
def caseIIKappa (eps : ℝ) : ℝ :=
  2 * Real.arcsin (1 - eps) / Real.pi

/-- The weight used in the paper's epsilon-greedy deletion.  Notice the
essential factor `1 - eps` in the denominator. -/
def caseIIPaperWeight (eps rho height : ℝ) : ℝ :=
  Real.arcsin (height / ((1 - eps) * rho))

/-- The coefficient of the selected-triangle area in the radial-fan lower
bound after substituting the covering estimate. -/
def caseIILambda (c kappa rho : ℝ) : ℝ :=
  1 - 2 * rho ^ 2 / (c * kappa)

theorem lt_arcsin_of_pos_of_lt_one {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    x < Real.arcsin x := by
  have hasin : 0 < Real.arcsin x := Real.arcsin_pos.2 hx0
  have hsin := Real.sin_lt hasin
  rw [Real.sin_arcsin (by linarith) hx1.le] at hsin
  exact hsin

theorem caseIIC_pos {a rho : ℝ}
    (ha : 0 < a) (harho : a < rho) :
    0 < caseIIC a rho := by
  have hrho : 0 < rho := ha.trans harho
  have harg : 0 < a / rho := div_pos ha hrho
  have hasin : 0 < Real.arcsin (a / rho) := Real.arcsin_pos.2 harg
  exact div_pos ha (mul_pos zero_lt_two hasin)

/-- The strict coefficient inequality needed to make the elimination
coefficient negative. -/
theorem caseIIC_lt_half_rho {a rho : ℝ}
    (ha : 0 < a) (harho : a < rho) :
    caseIIC a rho < rho / 2 := by
  have hrho : 0 < rho := ha.trans harho
  have harg0 : 0 < a / rho := div_pos ha hrho
  have harg1 : a / rho < 1 := (div_lt_one hrho).2 harho
  have hasin : 0 < Real.arcsin (a / rho) := Real.arcsin_pos.2 harg0
  have hstrict : a / rho < Real.arcsin (a / rho) :=
    lt_arcsin_of_pos_of_lt_one harg0 harg1
  have hcross : a < rho * Real.arcsin (a / rho) := by
    have := (div_lt_iff₀ hrho).1 hstrict
    simpa [mul_comm] using this
  rw [caseIIC, div_lt_iff₀ (mul_pos zero_lt_two hasin)]
  nlinarith

/-- Monotonicity of `arcsin x / x`, written in exactly the form needed for a
single triangle.  The proof uses strict concavity of sine, not differentiation
of a quotient. -/
theorem caseII_single_triangle_weight {a rho delta : ℝ}
    (ha : 0 < a) (harho : a < rho)
    (hdelta0 : 0 ≤ delta) (hdeltaa : delta ≤ a) :
    caseIIC a rho * Real.arcsin (delta / rho) ≤ delta / 2 := by
  have hrho : 0 < rho := ha.trans harho
  rcases hdelta0.eq_or_lt with rfl | hdelta
  · simp [caseIIC]
  let u : ℝ := Real.arcsin (delta / rho)
  let v : ℝ := Real.arcsin (a / rho)
  have hdu0 : 0 < delta / rho := div_pos hdelta hrho
  have hav0 : 0 < a / rho := div_pos ha hrho
  have hdu1 : delta / rho ≤ 1 := by
    rw [div_le_one hrho]
    exact hdeltaa.trans harho.le
  have hav1 : a / rho < 1 := (div_lt_one hrho).2 harho
  have hu0 : 0 < u := Real.arcsin_pos.2 hdu0
  have hv0 : 0 < v := Real.arcsin_pos.2 hav0
  have huv : u ≤ v := by
    dsimp [u, v]
    exact Real.arcsin_le_arcsin (div_le_div_of_nonneg_right hdeltaa hrho.le)
  have hu_mem : u ∈ Set.Icc (0 : ℝ) Real.pi := by
    refine ⟨hu0.le, (Real.arcsin_le_pi_div_two _).trans ?_⟩
    linarith [Real.pi_pos]
  have hv_mem : v ∈ Set.Icc (0 : ℝ) Real.pi := by
    refine ⟨hv0.le, (Real.arcsin_le_pi_div_two _).trans ?_⟩
    linarith [Real.pi_pos]
  have hsin_u : Real.sin u = delta / rho := by
    dsimp [u]
    exact Real.sin_arcsin (by linarith) hdu1
  have hsin_v : Real.sin v = a / rho := by
    dsimp [v]
    exact Real.sin_arcsin (by linarith) hav1.le
  have hcross : a * u ≤ delta * v := by
    rcases huv.eq_or_lt with huv_eq | huv_lt
    · have hratio : delta / rho = a / rho := by
        rw [← hsin_u, ← hsin_v, huv_eq]
      have hda : delta = a := (div_left_inj' hrho.ne').1 hratio
      rw [hda, huv_eq]
    · have hsec :=
        StrictConcaveOn.secant_strict_mono
          (𝕜 := ℝ) (f := Real.sin) strictConcaveOn_sin_Icc
          (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by exact ⟨le_rfl, Real.pi_pos.le⟩)
          hu_mem hv_mem hu0.ne' hv0.ne' huv_lt
      rw [Real.sin_zero, hsin_u, hsin_v, sub_zero, sub_zero] at hsec
      have hsec' : (a / rho) / v < (delta / rho) / u := by
        simpa using hsec
      have hdivcross : (a / rho) * u < (delta / rho) * v :=
        (div_lt_div_iff₀ hv0 hu0).1 hsec'
      have hrhocross := mul_lt_mul_of_pos_left hdivcross hrho
      have hleft : rho * ((a / rho) * u) = a * u := by
        field_simp
      have hright : rho * ((delta / rho) * v) = delta * v := by
        field_simp
      rw [hleft, hright] at hrhocross
      exact hrhocross.le
  have hvden : 0 < 2 * v := mul_pos zero_lt_two hv0
  rw [caseIIC, div_mul_eq_mul_div, div_le_iff₀ hvden]
  nlinarith

theorem caseIIKappa_pos {eps : ℝ}
    (_heps0 : 0 < eps) (heps1 : eps < 1) :
    0 < caseIIKappa eps := by
  have hm : 0 < 1 - eps := sub_pos.2 heps1
  have hasin : 0 < Real.arcsin (1 - eps) := Real.arcsin_pos.2 hm
  exact div_pos (mul_pos zero_lt_two hasin) Real.pi_pos

theorem caseIIKappa_lt_one {eps : ℝ}
    (heps0 : 0 < eps) :
    caseIIKappa eps < 1 := by
  have hm : 1 - eps < 1 := by linarith
  have hasin : Real.arcsin (1 - eps) < Real.pi / 2 :=
    Real.arcsin_lt_pi_div_two.2 hm
  rw [caseIIKappa, div_lt_one Real.pi_pos]
  linarith

theorem caseIIKappa_nonneg {eps : ℝ}
    (heps1 : eps ≤ 1) :
    0 ≤ caseIIKappa eps := by
  have hm : 0 ≤ 1 - eps := sub_nonneg.2 heps1
  have hasin : 0 ≤ Real.arcsin (1 - eps) := Real.arcsin_nonneg.2 hm
  exact div_nonneg (mul_nonneg zero_le_two hasin) Real.pi_pos.le

/-- The inverse-sine chord used by Case II is genuinely concave.  The second
 derivative is `m (m² - 1) sin u / (sqrt (1 - m² sin² u))³`, hence is
 nonpositive on the left half-period when `0 < m < 1`. -/
theorem concaveOn_arcsin_mul_sin {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) (Real.pi / 2))
      (fun u : ℝ => Real.arcsin (m * Real.sin u)) := by
  let f : ℝ → ℝ := fun u => Real.arcsin (m * Real.sin u)
  let f' : ℝ → ℝ := fun u =>
    m * Real.cos u / Real.sqrt (1 - (m * Real.sin u) ^ 2)
  let f'' : ℝ → ℝ := fun u =>
    m * (m ^ 2 - 1) * Real.sin u /
      (Real.sqrt (1 - (m * Real.sin u) ^ 2)) ^ 3
  have hbase : ∀ u, 0 < 1 - (m * Real.sin u) ^ 2 := by
    intro u
    have hs : |Real.sin u| ≤ 1 := Real.abs_sin_le_one u
    have hmabs : |m| < 1 := by simpa [abs_of_pos hm0] using hm1
    have hprod : |m * Real.sin u| < 1 := by
      rw [abs_mul]
      calc
        |m| * |Real.sin u| ≤ |m| * 1 :=
          mul_le_mul_of_nonneg_left hs (abs_nonneg m)
        _ < 1 := by simpa using hmabs
    have hsq : (m * Real.sin u) ^ 2 < 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (m * Real.sin u)]
    linarith
  have hf' : ∀ u, HasDerivAt f (f' u) u := by
    intro u
    have hargneg : m * Real.sin u ≠ -1 := by
      have := hbase u
      nlinarith
    have hargpos : m * Real.sin u ≠ 1 := by
      have := hbase u
      nlinarith
    dsimp [f, f']
    convert (Real.hasDerivAt_arcsin hargneg hargpos).comp u
      ((Real.hasDerivAt_sin u).const_mul m) using 1 <;> ring
  have hf'' : ∀ u, HasDerivAt f' (f'' u) u := by
    intro u
    have hb := hbase u
    have hbase_deriv : HasDerivAt (fun x : ℝ => 1 - (m * Real.sin x) ^ 2)
        (-2 * m ^ 2 * Real.sin u * Real.cos u) u := by
      convert (((Real.hasDerivAt_sin u).const_mul m).pow 2).const_sub 1 using 1 <;> ring
    have hsqrt : HasDerivAt (fun x : ℝ =>
        Real.sqrt (1 - (m * Real.sin x) ^ 2))
        ((-2 * m ^ 2 * Real.sin u * Real.cos u) /
          (2 * Real.sqrt (1 - (m * Real.sin u) ^ 2))) u :=
      hbase_deriv.sqrt hb.ne'
    have hnum : HasDerivAt (fun x : ℝ => m * Real.cos x)
        (-m * Real.sin u) u := by
      convert (Real.hasDerivAt_cos u).const_mul m using 1 <;> ring
    dsimp [f', f'']
    convert hnum.div hsqrt (Real.sqrt_ne_zero'.2 hb) using 1
    field_simp [Real.sqrt_ne_zero'.2 hb]
    have hb' : 0 ≤ 1 - m ^ 2 * Real.sin u ^ 2 := by
      simpa [mul_pow] using hb.le
    have hsquare :
        Real.sqrt (1 - m ^ 2 * Real.sin u ^ 2) ^ 2 =
          1 - m ^ 2 * Real.sin u ^ 2 := Real.sq_sqrt hb'
    have hid :
        (m ^ 2 - 1) * Real.sin u = Real.sin u *
          (-Real.sqrt (1 - m ^ 2 * Real.sin u ^ 2) ^ 2 +
            m ^ 2 * Real.cos u ^ 2) := by
      calc
        (m ^ 2 - 1) * Real.sin u =
            Real.sin u * (m ^ 2 * (Real.sin u ^ 2 + Real.cos u ^ 2) - 1) := by
          rw [Real.sin_sq_add_cos_sq]
          ring
        _ = _ := by rw [hsquare]; ring
    rw [hid]
    ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 (Real.pi / 2))
  · exact (Real.continuous_arcsin.comp
      (continuous_const.mul Real.continuous_sin)).continuousOn
  · intro u _
    exact (hf' u).hasDerivWithinAt
  · intro u _
    exact (hf'' u).hasDerivWithinAt
  · intro u hu
    dsimp [f'']
    have hu' : u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      simpa [interior_Icc, Real.pi_pos.ne'] using hu
    have hsin : 0 ≤ Real.sin u := Real.sin_nonneg_of_nonneg_of_le_pi hu'.1.le
      (hu'.2.le.trans (by linarith [Real.pi_pos]))
    have hsqrt : 0 < Real.sqrt (1 - (m * Real.sin u) ^ 2) :=
      Real.sqrt_pos.2 (hbase u)
    have hmcoef : m * (m ^ 2 - 1) ≤ 0 := by nlinarith
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hmcoef hsin) (by positivity)

/-- The exact specialization required by the epsilon-greedy construction. -/
theorem caseII_arcsin_concave {eps : ℝ} (heps0 : 0 < eps) (heps1 : eps < 1) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) (Real.pi / 2))
      (fun u : ℝ => Real.arcsin ((1 - eps) * Real.sin u)) :=
  concaveOn_arcsin_mul_sin (by linarith) (by linarith)

/-- If the chord concavity of `u ↦ arcsin (m * sin u)` is supplied, this
lemma extracts the precise epsilon weight used by the greedy proof.  The
assumption is a genuine analytic interface (`ConcaveOn` on an interval), not
the target pointwise inequality. -/
theorem caseII_asin_weight_of_concave {m H : ℝ}
    (_hm0 : 0 ≤ m) (_hm1 : m ≤ 1)
    (hH : H ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (hconcave :
      ConcaveOn ℝ (Set.Icc (0 : ℝ) (Real.pi / 2))
        (fun u : ℝ => Real.arcsin (m * Real.sin u))) :
    2 * Real.arcsin m / Real.pi * H ≤
      Real.arcsin (m * Real.sin H) := by
  have hpi2 : 0 < Real.pi / 2 := by positivity
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨le_rfl, hpi2.le⟩
  have hhalf : Real.pi / 2 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨hpi2.le, le_rfl⟩
  have hweight0 : 0 ≤ H / (Real.pi / 2) := div_nonneg hH.1 hpi2.le
  have hweight1 : H / (Real.pi / 2) ≤ 1 :=
    (div_le_one hpi2).2 hH.2
  have hweight_compl : 0 ≤ 1 - H / (Real.pi / 2) := sub_nonneg.2 hweight1
  have hweight_sum :
      (1 - H / (Real.pi / 2)) + H / (Real.pi / 2) = 1 := by
    ring
  have hchord := hconcave.2 hzero hhalf hweight_compl hweight0 hweight_sum
  have hsin_half : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
  have hasin_zero : Real.arcsin (m * Real.sin 0) = 0 := by simp
  have hpoint :
      (1 - H / (Real.pi / 2)) * 0
          + (H / (Real.pi / 2)) * Real.arcsin m
        ≤ Real.arcsin
          (m * Real.sin
            ((1 - H / (Real.pi / 2)) * 0
              + (H / (Real.pi / 2)) * (Real.pi / 2))) := by
    simpa [hasin_zero, hsin_half] using hchord
  have harg :
      (1 - H / (Real.pi / 2)) * 0
          + (H / (Real.pi / 2)) * (Real.pi / 2) = H := by
    field_simp <;> ring
  rw [harg] at hpoint
  have hcoef :
      2 * Real.arcsin m / Real.pi * H =
        (H / (Real.pi / 2)) * Real.arcsin m := by
    field_simp
  rw [hcoef]
  simpa using hpoint

/-- A selected paper-weight is paid for by half the corresponding triangle
height.  This is the precise combination of inverse-sine concavity and the
single-triangle estimate. -/
theorem caseII_paperWeight_paid_by_height
    {eps a rho height : ℝ}
    (heps0 : 0 < eps) (heps1 : eps < 1)
    (ha : 0 < a) (harho : a < rho)
    (hh0 : 0 ≤ height) (hha : height ≤ a)
    (hscaled : height ≤ (1 - eps) * rho) :
    caseIIC a rho * caseIIKappa eps * caseIIPaperWeight eps rho height ≤
      height / 2 := by
  have hm0 : 0 ≤ 1 - eps := by linarith
  have hm1 : 1 - eps ≤ 1 := by linarith
  have hrho : 0 < rho := ha.trans harho
  have hden : 0 < (1 - eps) * rho := mul_pos (sub_pos.2 heps1) hrho
  have harg0 : 0 ≤ height / ((1 - eps) * rho) := div_nonneg hh0 hden.le
  have harg1 : height / ((1 - eps) * rho) ≤ 1 := (div_le_one hden).2 hscaled
  let H := caseIIPaperWeight eps rho height
  have hH0 : 0 ≤ H := Real.arcsin_nonneg.2 harg0
  have hHpi : H ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hsinH : Real.sin H = height / ((1 - eps) * rho) := by
    exact Real.sin_arcsin (by linarith) harg1
  have hconc := caseII_asin_weight_of_concave hm0 hm1 ⟨hH0, hHpi⟩
    (caseII_arcsin_concave heps0 heps1)
  have hrewrite : Real.arcsin ((1 - eps) * Real.sin H) =
      Real.arcsin (height / rho) := by
    rw [hsinH]
    congr 1
    have hmne : 1 - eps ≠ 0 := ne_of_gt (sub_pos.2 heps1)
    field_simp [hmne, hrho.ne']
  rw [hrewrite] at hconc
  have hsingle := caseII_single_triangle_weight ha harho hh0 hha
  change caseIIC a rho * caseIIKappa eps * H ≤ height / 2
  have hk : caseIIKappa eps = 2 * Real.arcsin (1 - eps) / Real.pi := rfl
  rw [← hk] at hconc
  simpa [mul_assoc] using
    (mul_le_mul_of_nonneg_left hconc (caseIIC_pos ha harho).le).trans hsingle

/-- Negativity of the selected-area coefficient in the range needed by the
parametric theorem. -/
theorem caseIILambda_neg {c kappa rho : ℝ}
    (hc0 : 0 < c) (hcrho : c < rho / 2)
    (hk0 : 0 < kappa) (hk1 : kappa ≤ 1)
    (hrho : 1 / 2 < rho) :
    caseIILambda c kappa rho < 0 := by
  have hrho0 : 0 < rho := by linarith
  have hck0 : 0 < c * kappa := mul_pos hc0 hk0
  have hck : c * kappa < rho / 2 := by
    calc
      c * kappa ≤ c * 1 := mul_le_mul_of_nonneg_left hk1 hc0.le
      _ < rho / 2 := by simpa using hcrho
  have hhalf_num : rho / 2 < 2 * rho ^ 2 := by
    nlinarith
  have hratio : 1 < 2 * rho ^ 2 / (c * kappa) := by
    rw [lt_div_iff₀ hck0]
    simpa using hck.trans hhalf_num
  dsimp [caseIILambda]
  linarith

/-- Exact coefficient elimination from the two lower bounds produced by the
selected-triangle and radial-fan constructions. -/
theorem caseII_coefficient_elimination
    {c kappa rho L M b : ℝ}
    (hc0 : 0 < c) (hk0 : 0 < kappa) (hrho0 : 0 < rho)
    (hlambda : caseIILambda c kappa rho < 0)
    (hselected : b ≤ M)
    (hfan : rho ^ 2 / 2 * L + caseIILambda c kappa rho * b ≤ M) :
    c * kappa / 4 * L ≤ M := by
  let lambda := caseIILambda c kappa rho
  have hlambda' : lambda < 0 := by simpa [lambda] using hlambda
  have hmul : lambda * M ≤ lambda * b :=
    mul_le_mul_of_nonpos_left hselected hlambda'.le
  have hcombined : rho ^ 2 / 2 * L + lambda * M ≤ M := by
    have hfan' : rho ^ 2 / 2 * L + lambda * b ≤ M := by
      simpa [lambda] using hfan
    linarith only [hmul, hfan']
  have hcore : rho ^ 2 / 2 * L ≤ (1 - lambda) * M := by
    linarith
  have hlambda_id :
      1 - lambda = 2 * rho ^ 2 / (c * kappa) := by
    simp [lambda, caseIILambda]
  rw [hlambda_id] at hcore
  let scale : ℝ := c * kappa / (2 * rho ^ 2)
  have hscale0 : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hcore hscale0
  have hleft :
      scale * (rho ^ 2 / 2 * L) = c * kappa / 4 * L := by
    dsimp [scale]
    field_simp
    ring
  have hright :
      scale * (2 * rho ^ 2 / (c * kappa) * M) = M := by
    dsimp [scale]
    field_simp
  simpa [hleft, hright] using hscaled

/-- The complete algebraic minimax step, with the sign discharged from the
natural parameter inequalities. -/
theorem caseII_minimax
    {c kappa rho L M b : ℝ}
    (hc0 : 0 < c) (hcrho : c < rho / 2)
    (hk0 : 0 < kappa) (hk1 : kappa ≤ 1)
    (hrho : 1 / 2 < rho)
    (hselected : b ≤ M)
    (hfan : rho ^ 2 / 2 * L + caseIILambda c kappa rho * b ≤ M) :
    c * kappa / 4 * L ≤ M := by
  exact caseII_coefficient_elimination hc0 hk0 (by linarith)
    (caseIILambda_neg hc0 hcrho hk0 hk1 hrho) hselected hfan

/-- Genuine minimax bridge with `L` equal to the initial angular mass.  The
covering premise accounts for both the residual and all deleted shadows, while
the payment premise charges the selected weights to selected triangle area. -/
theorem caseII_minimax_of_initial_cover
    {c kappa rho L R W M b : ℝ}
    (hc0 : 0 < c) (hcrho : c < rho / 2)
    (hk0 : 0 < kappa) (hk1 : kappa ≤ 1)
    (hrho : 1 / 2 < rho)
    (hW0 : 0 ≤ W)
    (hcover : L ≤ R + 2 * W)
    (hpayment : c * kappa * W ≤ b)
    (hselected : b ≤ M)
    (hgeometric : rho ^ 2 / 2 * R + b ≤ M) :
    c * kappa / 4 * L ≤ M := by
  have hck : 0 < c * kappa := mul_pos hc0 hk0
  have hWb : W ≤ b / (c * kappa) := by
    rw [le_div_iff₀ hck]
    nlinarith [hpayment]
  have hLR : L ≤ R + 2 * (b / (c * kappa)) :=
    hcover.trans (add_le_add_right (mul_le_mul_of_nonneg_left hWb zero_le_two) R)
  have hcoef0 : 0 ≤ rho ^ 2 / 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hLR hcoef0
  have hfan : rho ^ 2 / 2 * L + caseIILambda c kappa rho * b ≤ M := by
    have hb0 : 0 ≤ b := (mul_nonneg (mul_pos hc0 hk0).le hW0).trans hpayment
    have hid : rho ^ 2 / 2 * (R + 2 * (b / (c * kappa))) +
        caseIILambda c kappa rho * b =
          rho ^ 2 / 2 * R + b - rho ^ 2 / (c * kappa) * b := by
      dsimp [caseIILambda]
      field_simp
      ring
    calc
      rho ^ 2 / 2 * L + caseIILambda c kappa rho * b ≤
          rho ^ 2 / 2 * (R + 2 * (b / (c * kappa))) +
            caseIILambda c kappa rho * b := add_le_add hscaled le_rfl
      _ = rho ^ 2 / 2 * R + b - rho ^ 2 / (c * kappa) * b := hid
      _ ≤ rho ^ 2 / 2 * R + b := sub_le_self _ (mul_nonneg (by positivity) hb0)
      _ ≤ M := hgeometric
  exact caseII_minimax hc0 hcrho hk0 hk1 hrho hselected hfan

end

end StarKakeyaLower
