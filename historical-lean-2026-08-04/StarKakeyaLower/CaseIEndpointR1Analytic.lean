import StarKakeyaLower.CaseIEndpointAnalytic

/-!
# The analytic `R₁` endpoint envelope

This file isolates the scalar part of Li's Lemma 3.2.  Its input is the raw
first-contact formula `t = asin (δ₀/r) - atan (2δ₀)` together with one of the
two geometric `R₁ sin t` comparisons (or saturation of the projective circle).
In particular, no final endpoint-gap estimate is assumed.
-/

namespace StarKakeyaLower

noncomputable section

-- The rational polynomial certificates below require more normalization than
-- Lean's default heartbeat budget permits.
set_option maxHeartbeats 800000

/-- On the whole Figure-5 height box the first-contact function is strictly
increasing.  This is the comparison which turns a selected mixed-component
span bound into a height cutoff; it is intentionally stated independently of
any endpoint source sum. -/
theorem strongEndpointPhi_strictMonoOn {r : ℝ}
    (hr : r ∈ Set.Icc strongA strongR₀) :
    StrictMonoOn (strongEndpointPhi r) (Set.Icc 0 strongA) := by
  have hr0 : 0 < r := strongParameterDomain.a_pos.trans_le hr.1
  have hrhalf : r < 1 / 2 := hr.2.trans_lt
    strongParameterDomain.r₀_lt_half
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 strongA)
      ((Real.continuous_arcsin.comp (continuous_id.div_const r)).sub
        (Real.continuous_arctan.comp (continuous_const.mul continuous_id))).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hxr : x / r ∈ Set.Ioo (-1 : ℝ) 1 := by
      constructor
      · have : 0 < x / r := div_pos hx.1 hr0
        linarith
      · exact (div_lt_one hr0).2 (hx.2.trans_le hr.1)
    have ha := (Real.hasDerivAt_arcsin (ne_of_gt hxr.1) (ne_of_lt hxr.2)).comp x
      (hasDerivAt_id x |>.div_const r)
    have ht := (hasDerivAt_id x).const_mul (2 : ℝ) |>.arctan
    convert (ha.sub ht).hasDerivWithinAt using 1
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 < x := hx.1
    have hxrlt : x / r < 1 := (div_lt_one hr0).2 (hx.2.trans_le hr.1)
    have hxr0 : 0 ≤ x / r := div_nonneg hx0.le hr0.le
    have hrad0 : 0 < 1 - (x / r) ^ 2 := by nlinarith
    have hsqrt0 : 0 < Real.sqrt (1 - (x / r) ^ 2) := Real.sqrt_pos.2 hrad0
    have hsqrt_le : Real.sqrt (1 - (x / r) ^ 2) ≤ 1 := by
      rw [Real.sqrt_le_one]
      nlinarith [sq_nonneg (x / r)]
    have hden : r * Real.sqrt (1 - (x / r) ^ 2) < 1 / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hsqrt_le hr0.le]
    have hfirst : 2 < 1 / Real.sqrt (1 - (x / r) ^ 2) * (1 / r) := by
      calc
        2 < 1 / (r * Real.sqrt (1 - (x / r) ^ 2)) :=
          (lt_div_iff₀ (mul_pos hr0 hsqrt0)).2 (by nlinarith)
        _ = 1 / Real.sqrt (1 - (x / r) ^ 2) * (1 / r) := by field_simp
    have hsecond : 1 / (1 + (2 * x) ^ 2) * 2 ≤ 2 := by
      have hd : 1 ≤ 1 + (2 * x) ^ 2 := by nlinarith [sq_nonneg (2 * x)]
      have hp : 0 < 1 + (2 * x) ^ 2 := by nlinarith [sq_nonneg (2 * x)]
      have := (div_le_one hp).2 hd
      nlinarith
    simp only [id_eq, mul_one]
    change 0 < 1 / √(1 - (x / r) ^ 2) * (1 / r) -
      1 / (1 + (2 * x) ^ 2) * 2
    linarith

private theorem strongR1_pos : 0 < strongR₁ := by
  rw [strongR₁]
  exact div_pos (Real.sqrt_pos.2 (by positivity)) strong_r₁_denominator_pos

/-- A rational upper enclosure for the radical constant used by the base-ray
estimate.  This is deliberately proved from the definitions (and the certified
enclosure for `strongD`), rather than supplied as numerical input. -/
theorem strongR₁_lt_1859 : strongR₁ < 1859 / 1000 := by
  let dl : ℝ := 302738 / 10000000
  let du : ℝ := 302739 / 10000000
  let s : ℝ := 11521 / 50000
  let n : ℝ := 125229 / 125000
  obtain ⟨hdl, hdu⟩ := strong_d_rational_bounds
  have hd0 := strong_d_domain.1
  have hrad0 := strong_r₁_radicand_nonneg
  have hrad_lt : strongR₁Radicand < s ^ 2 := by
    rw [strongR₁Radicand]
    dsimp [dl, s] at hdl ⊢
    norm_num [strongRLambda] at hdl ⊢
    nlinarith
  have hs0 : 0 ≤ s := by norm_num [s]
  have hsqrt : Real.sqrt strongR₁Radicand < s :=
    (Real.sqrt_lt hrad0 hs0).2 hrad_lt
  have hnum_sq : 1 + 4 * strongD ^ 2 < n ^ 2 := by
    dsimp [du, n] at hdu ⊢
    nlinarith
  have hn0 : 0 < n := by norm_num [n]
  have hnum : Real.sqrt (1 + 4 * strongD ^ 2) < n := by
    rw [Real.sqrt_lt' hn0]
    exact hnum_sq
  have hden_lower : (26958 / 50000 : ℝ) < strongR₁Denominator := by
    rw [strongR₁Denominator]
    dsimp [s] at hsqrt
    linarith
  rw [strongR₁]
  apply (div_lt_iff₀ strong_r₁_denominator_pos).2
  have harith : n < (1859 / 1000 : ℝ) * (26958 / 50000) := by
    norm_num [n]
  exact hnum.trans (harith.trans (mul_lt_mul_of_pos_left hden_lower (by norm_num)))

private theorem sin_taylor_lower {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x - x ^ 3 / 6 - x ^ 4 * (5 / 96) ≤ Real.sin x := by
  have habs : |x| ≤ 1 := by simpa [abs_of_nonneg hx0] using hx1
  have h := neg_le_of_abs_le (Real.sin_bound habs)
  rw [abs_of_nonneg hx0] at h
  linarith

/-- Continuous-domain base-ray estimate for the frozen endpoint branch.

The proof splits at `t = 7/100`.  Below the cut, the `R₁` constraint and two
Taylor bootstraps force `α < (1250/669)t`.  Above it, the height-product
constraint is incompatible with `α ≥ (1250/669)t`; three rational subintervals
certify the only tight range.  No endpoint-gap estimate is an input. -/
theorem base_ray_frozen_analytic
    {r t α : ℝ}
    (hr : r ∈ Set.Icc strongA strongR₀)
    (ht0 : 0 < t)
    (htop : t < Real.pi / 2 - Real.arctan (2 * r))
    (hhalf : t / 2 ≤ α) (hαtop : α ≤ Real.pi / 2)
    (hsint : 0 ≤ Real.sin t)
    (hR1 : Real.sin α ≤ strongR₁ * Real.sin t)
    (hheight : Real.sin α * Real.sin (α - t) ≤ strongA * Real.sin t) :
    2 * α - t < strongFrozenRatio * t := by
  -- These hypotheses are part of the geometric interface; the scalar
  -- contradiction below only needs their indicated consequences.
  have _ := hr
  have _ := htop
  have _ := hsint
  have hα0 : 0 ≤ α := by linarith
  have hk0 : (0 : ℝ) < 1250 / 669 := by norm_num
  have hl0 : (0 : ℝ) < 581 / 669 := by norm_num
  suffices hα : α < (1250 / 669 : ℝ) * t by
    norm_num [strongFrozenRatio, strongRLambda] at hα ⊢
    linarith
  by_contra hnot
  have hkt : (1250 / 669 : ℝ) * t ≤ α := le_of_not_gt hnot
  rcases le_or_gt t (7 / 100 : ℝ) with hsmall | hlarge
  · have hsint_lt : Real.sin t < t := Real.sin_lt ht0
    have hsinα_lt : Real.sin α < (1859 / 1000 : ℝ) * t := by
      calc
        Real.sin α ≤ strongR₁ * Real.sin t := hR1
        _ < (1859 / 1000 : ℝ) * t := by
          have hRu := strongR₁_lt_1859
          have hsin_nonneg : 0 ≤ Real.sin t :=
            Real.sin_nonneg_of_nonneg_of_le_pi ht0.le (by
              linarith [htop, Real.arctan_lt_pi_div_two (2 * r)])
          nlinarith
    have hαpi0 : 0 ≤ Real.pi / 2 := Real.pi_div_two_pos.le
    have hjordan := Real.mul_le_sin hα0 hαtop
    have hα_pre : α < 41 / 200 := by
      have hsinα0 : 0 < Real.sin α := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · exact lt_of_lt_of_le (mul_pos hk0 ht0) hkt
        · linarith [Real.pi_pos]
      have hchord : α ≤ Real.pi / 2 * Real.sin α := by
        calc
          α = Real.pi / 2 * (2 / Real.pi * α) := by field_simp
          _ ≤ Real.pi / 2 * Real.sin α :=
            mul_le_mul_of_nonneg_left hjordan hαpi0
      have hpiRat : Real.pi / 2 < (1571 / 1000 : ℝ) := by
        linarith [Real.pi_lt_d20]
      have hchain : α < (1571 / 1000 : ℝ) * ((1859 / 1000 : ℝ) * t) :=
        hchord.trans_lt ((mul_lt_mul_of_pos_right hpiRat hsinα0).trans
          (mul_lt_mul_of_pos_left hsinα_lt (by norm_num)))
      nlinarith
    have htaylor1 := sin_taylor_lower hα0 (by linarith : α ≤ 1)
    have hα_mid : α < 33 / 250 := by
      have hαsq : α ^ 2 < (41 / 200 : ℝ) ^ 2 := by nlinarith
      have hαcube : α ^ 3 ≤ (41 / 200 : ℝ) ^ 2 * α := by
        nlinarith [mul_nonneg hα0 (sub_nonneg.mpr hαsq.le)]
      have hαfour : α ^ 4 ≤ (41 / 200 : ℝ) ^ 3 * α := by
        nlinarith [mul_nonneg (sq_nonneg α) (sub_nonneg.mpr hαsq.le)]
      nlinarith
    have htaylor2 := sin_taylor_lower hα0 (by linarith : α ≤ 1)
    have hαsq : α ^ 2 < (33 / 250 : ℝ) ^ 2 := by nlinarith
    have hαcube : α ^ 3 ≤ (33 / 250 : ℝ) ^ 2 * α := by
      nlinarith [mul_nonneg hα0 (sub_nonneg.mpr hαsq.le)]
    have hαfour : α ^ 4 ≤ (33 / 250 : ℝ) ^ 3 * α := by
      nlinarith [mul_nonneg (sq_nonneg α) (sub_nonneg.mpr hαsq.le)]
    nlinarith
  · have ht07 : (7 / 100 : ℝ) < t := hlarge
    have hdiff : (581 / 669 : ℝ) * t ≤ α - t := by
      nlinarith
    have hdiff0 : 0 ≤ α - t := le_trans (mul_nonneg hl0.le ht0.le) hdiff
    have hdiff_top : α - t ≤ Real.pi / 2 := by linarith
    by_cases htHalf : t ≤ 1 / 2
    · have hkt1 : (1250 / 669 : ℝ) * t ≤ 1 := by nlinarith
      have hlt1 : (581 / 669 : ℝ) * t ≤ 1 := by nlinarith
      have hsin_k := Real.sin_gt_sub_cube (mul_pos hk0 ht0) hkt1
      have hsin_l := Real.sin_gt_sub_cube (mul_pos hl0 ht0) hlt1
      have hsinα : Real.sin ((1250 / 669 : ℝ) * t) ≤ Real.sin α := by
        apply Real.strictMonoOn_sin.monotoneOn
        · constructor <;> linarith [Real.pi_pos]
        · exact ⟨by linarith [Real.pi_pos], hαtop⟩
        · exact hkt
      have hsindiff : Real.sin ((581 / 669 : ℝ) * t) ≤ Real.sin (α - t) := by
        apply Real.strictMonoOn_sin.monotoneOn
        · constructor <;> linarith [Real.pi_pos]
        · exact ⟨by linarith [Real.pi_pos], hdiff_top⟩
        · exact hdiff
      have hsinα0 : 0 ≤ Real.sin α :=
        Real.sin_nonneg_of_nonneg_of_le_pi hα0 (by linarith [Real.pi_pos, hαtop])
      have hsindiff0 : 0 ≤ Real.sin (α - t) :=
        Real.sin_nonneg_of_nonneg_of_le_pi hdiff0 (by linarith [Real.pi_pos, hdiff_top])
      have hprod :
          ((1250 / 669 : ℝ) * t - ((1250 / 669 : ℝ) * t) ^ 3 / 4) *
              ((581 / 669 : ℝ) * t - ((581 / 669 : ℝ) * t) ^ 3 / 4) <
            Real.sin α * Real.sin (α - t) := by
        have hp0 : 0 < (1250 / 669 : ℝ) * t - ((1250 / 669 : ℝ) * t) ^ 3 / 4 := by
          have hx0 := mul_pos hk0 ht0
          have hx2 : ((1250 / 669 : ℝ) * t) ^ 2 ≤ 1 := by nlinarith
          nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hx2)]
        have hq0 : 0 < (581 / 669 : ℝ) * t - ((581 / 669 : ℝ) * t) ^ 3 / 4 := by
          have hx0 := mul_pos hl0 ht0
          have hx2 : ((581 / 669 : ℝ) * t) ^ 2 ≤ 1 := by nlinarith
          nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hx2)]
        have hpSin :
            (1250 / 669 : ℝ) * t - ((1250 / 669 : ℝ) * t) ^ 3 / 4 <
              Real.sin α := hsin_k.trans_le hsinα
        have hqSin :
            (581 / 669 : ℝ) * t - ((581 / 669 : ℝ) * t) ^ 3 / 4 <
              Real.sin (α - t) := hsin_l.trans_le hsindiff
        exact (mul_lt_mul_of_pos_right hpSin hq0).trans
          (mul_lt_mul_of_pos_left hqSin (hp0.trans hpSin))
      have hpoly :
          strongA * t <
            ((1250 / 669 : ℝ) * t - ((1250 / 669 : ℝ) * t) ^ 3 / 4) *
              ((581 / 669 : ℝ) * t - ((581 / 669 : ℝ) * t) ^ 3 / 4) := by
        rcases le_or_gt t (1 / 10 : ℝ) with h1 | h1
        · have ht2 : t ^ 2 ≤ (1 / 10 : ℝ) ^ 2 := by nlinarith
          have hp : (1250 / 669 : ℝ) * t *
              (1 - (1250 / 669 : ℝ) ^ 2 * (1 / 10 : ℝ) ^ 2 / 4) ≤
              (1250 / 669 : ℝ) * t - ((1250 / 669 : ℝ) * t) ^ 3 / 4 := by
            nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr ht2)]
          have hq : (581 / 669 : ℝ) * t *
              (1 - (581 / 669 : ℝ) ^ 2 * (1 / 10 : ℝ) ^ 2 / 4) ≤
              (581 / 669 : ℝ) * t - ((581 / 669 : ℝ) * t) ^ 3 / 4 := by
            nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr ht2)]
          have hp0 : 0 ≤ (1250 / 669 : ℝ) * t *
              (1 - (1250 / 669 : ℝ) ^ 2 * (1 / 10 : ℝ) ^ 2 / 4) := by positivity
          have hq0 : 0 ≤ (581 / 669 : ℝ) * t *
              (1 - (581 / 669 : ℝ) ^ 2 * (1 / 10 : ℝ) ^ 2 / 4) := by positivity
          have hpq := mul_le_mul hp hq hq0 (hp0.trans hp)
          norm_num [strongA] at hpq ⊢
          nlinarith
        · rcases le_or_gt t (1 / 5 : ℝ) with h2 | h2
          · have ht2 : t ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := by nlinarith
            have hp : (1250 / 669 : ℝ) * t *
                (1 - (1250 / 669 : ℝ) ^ 2 * (1 / 5 : ℝ) ^ 2 / 4) ≤
                (1250 / 669 : ℝ) * t - ((1250 / 669 : ℝ) * t) ^ 3 / 4 := by
              nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr ht2)]
            have hq : (581 / 669 : ℝ) * t *
                (1 - (581 / 669 : ℝ) ^ 2 * (1 / 5 : ℝ) ^ 2 / 4) ≤
                (581 / 669 : ℝ) * t - ((581 / 669 : ℝ) * t) ^ 3 / 4 := by
              nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr ht2)]
            have hp0 : 0 ≤ (1250 / 669 : ℝ) * t *
                (1 - (1250 / 669 : ℝ) ^ 2 * (1 / 5 : ℝ) ^ 2 / 4) := by positivity
            have hq0 : 0 ≤ (581 / 669 : ℝ) * t *
                (1 - (581 / 669 : ℝ) ^ 2 * (1 / 5 : ℝ) ^ 2 / 4) := by positivity
            have hpq := mul_le_mul hp hq hq0 (hp0.trans hp)
            norm_num [strongA] at hpq ⊢
            nlinarith
          · have ht2 : t ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
            have hp : (1250 / 669 : ℝ) * t *
                (1 - (1250 / 669 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ 2 / 4) ≤
                (1250 / 669 : ℝ) * t - ((1250 / 669 : ℝ) * t) ^ 3 / 4 := by
              nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr ht2)]
            have hq : (581 / 669 : ℝ) * t *
                (1 - (581 / 669 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ 2 / 4) ≤
                (581 / 669 : ℝ) * t - ((581 / 669 : ℝ) * t) ^ 3 / 4 := by
              nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr ht2)]
            have hp0 : 0 ≤ (1250 / 669 : ℝ) * t *
                (1 - (1250 / 669 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ 2 / 4) := by positivity
            have hq0 : 0 ≤ (581 / 669 : ℝ) * t *
                (1 - (581 / 669 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ 2 / 4) := by positivity
            have hpq := mul_le_mul hp hq hq0 (hp0.trans hp)
            norm_num [strongA] at hpq ⊢
            nlinarith
      have hsint_le : Real.sin t ≤ t := Real.sin_le ht0.le
      rw [strongA] at hpoly
      norm_num [strongA] at hheight
      linarith
    · have htHalf' : (1 / 2 : ℝ) < t := lt_of_not_ge htHalf
      have hjα := Real.mul_le_sin hα0 hαtop
      have hjd := Real.mul_le_sin hdiff0 hdiff_top
      have hhalfα : α / 2 < Real.sin α := by
        have hp := Real.pi_lt_four
        have hp0 := Real.pi_pos
        have hαpos : 0 < α := lt_of_lt_of_le (mul_pos hk0 ht0) hkt
        have : α / 2 < 2 / Real.pi * α := by
          convert mul_lt_mul_of_pos_right (show (1 / 2 : ℝ) < 2 / Real.pi by
            rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hp0]
            linarith) hαpos using 1 <;> ring
        exact this.trans_le hjα
      have hhalfd : (α - t) / 2 < Real.sin (α - t) := by
        have hp := Real.pi_lt_four
        have hp0 := Real.pi_pos
        have hdpos : 0 < α - t := lt_of_lt_of_le (mul_pos hl0 ht0) hdiff
        have : (α - t) / 2 < 2 / Real.pi * (α - t) := by
          convert mul_lt_mul_of_pos_right (show (1 / 2 : ℝ) < 2 / Real.pi by
            rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hp0]
            linarith) hdpos using 1 <;> ring
        exact this.trans_le hjd
      have hsinα0 : 0 ≤ Real.sin α :=
        Real.sin_nonneg_of_nonneg_of_le_pi hα0 (by linarith [Real.pi_pos, hαtop])
      have hsind0 : 0 ≤ Real.sin (α - t) :=
        Real.sin_nonneg_of_nonneg_of_le_pi hdiff0 (by linarith [Real.pi_pos, hdiff_top])
      have hprod : α / 2 * ((α - t) / 2) <
          Real.sin α * Real.sin (α - t) := by nlinarith
      have hlow : strongA * t < α / 2 * ((α - t) / 2) := by
        norm_num [strongA]
        nlinarith [mul_nonneg (sub_nonneg.mpr hkt) (sub_nonneg.mpr hdiff)]
      have hsint_le := Real.sin_le ht0.le
      norm_num [strongA] at hheight
      nlinarith

private theorem sin_arcsin_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.sin (Real.arcsin x) ≤ x := by
  by_cases hx1 : x ≤ 1
  · exact (Real.sin_arcsin (by linarith) hx1).le
  · rw [(Real.arcsin_eq_pi_div_two.2 (le_of_not_ge hx1)), Real.sin_pi_div_two]
    exact le_of_not_ge hx1

private theorem endpoint_self_lt_arcsin {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    x < Real.arcsin x := by
  apply (Real.lt_arcsin_iff_sin_lt' ?_).2
  · exact Real.sin_lt hx0
  · constructor <;> linarith [Real.pi_gt_d20]

private theorem strongEndpointPhi_pos
    {r δ₀ : ℝ} (hr0 : 0 < r) (hrhalf : r < 1 / 2)
    (hδ0 : 0 < δ₀) (hδr : δ₀ < r) :
    0 < strongEndpointPhi r δ₀ := by
  have hx0 : 0 < δ₀ / r := div_pos hδ0 hr0
  have hx1 : δ₀ / r < 1 := (div_lt_one hr0).2 hδr
  have hasin : δ₀ / r < Real.arcsin (δ₀ / r) :=
    endpoint_self_lt_arcsin hx0 hx1
  have hatan : Real.arctan (2 * δ₀) < 2 * δ₀ :=
    arctan_lt_self_of_pos (by positivity)
  have hscale : 2 * δ₀ < δ₀ / r := by
    rw [lt_div_iff₀ hr0]
    nlinarith
  rw [strongEndpointPhi]
  linarith

private theorem arcsin_div_mono_radius
    {δ₀ r R : ℝ} (hδ0 : 0 ≤ δ₀) (hr : 0 < r) (hrR : r ≤ R) :
    Real.arcsin (δ₀ / R) ≤ Real.arcsin (δ₀ / r) := by
  apply Real.arcsin_le_arcsin
  apply (div_le_div_iff₀ (hr.trans_le hrR) hr).2
  nlinarith

/-- The complete scalar `R₁` envelope.  Besides the final strict estimate, the
conjunction exposes the unclamped sine inequality, principal-argument bounds,
the interior contact estimate, both radius-split comparisons, and the large
angle saturation estimate.  The final disjunction contains only raw geometric
comparisons (or circle saturation), never the desired gap itself. -/
theorem strongR1_endpoint_envelope_analytic
    {r δ₀ t s S : ℝ}
    (hr : r ∈ Set.Icc strongA strongR₀)
    (hδ0 : 0 < δ₀) (hδr : δ₀ < r)
    (ht : t = strongEndpointPhi r δ₀)
    (hs : s = Real.arcsin (δ₀ / r))
    (hS : S = Real.arcsin (strongR₁ * Real.sin t))
    (hdispatch :
      Real.pi ≤ strongPaperG r * t ∨
      (strongRLambda ≤ r ∧ strongR₁ * Real.sin t ≤ δ₀ / r) ∨
      (r ≤ strongRLambda ∧ strongR₁ * Real.sin t ≤ δ₀ / strongRLambda)) :
    0 < t ∧
    0 ≤ strongR₁ * Real.sin t ∧
    Real.sin S ≤ strongR₁ * Real.sin t ∧
    0 ≤ S ∧ S ≤ Real.pi / 2 ∧
    2 * s - t < strongInteriorRatio r * t ∧
    (strongRLambda ≤ r → strongR₁ * Real.sin t ≤ δ₀ / r → S ≤ s) ∧
    (r ≤ strongRLambda → strongR₁ * Real.sin t ≤ δ₀ / strongRLambda →
      2 * S - t < strongFrozenRatio * t) ∧
    (Real.pi ≤ strongPaperG r * t →
      2 * max s S - t < strongPaperG r * t) ∧
    2 * max s S - t < strongPaperG r * t := by
  have hr0 : 0 < r := strongParameterDomain.a_pos.trans_le hr.1
  have hrhalf : r < 1 / 2 :=
    hr.2.trans_lt strongParameterDomain.r₀_lt_half
  have ht0 : 0 < t := by
    rw [ht]
    exact strongEndpointPhi_pos hr0 hrhalf hδ0 hδr
  have htUpper : t < Real.pi / 2 := by
    rw [ht, strongEndpointPhi]
    have hatan0 : 0 < Real.arctan (2 * δ₀) := Real.arctan_pos.mpr (by positivity)
    linarith [Real.arcsin_le_pi_div_two (δ₀ / r)]
  have hsin0 : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0.le (by linarith [Real.pi_pos])
  have harg0 : 0 ≤ strongR₁ * Real.sin t :=
    mul_nonneg strongR1_pos.le hsin0
  have hsinS : Real.sin S ≤ strongR₁ * Real.sin t := by
    rw [hS]
    exact sin_arcsin_le_self_of_nonneg harg0
  have hS0 : 0 ≤ S := by
    rw [hS, Real.arcsin_nonneg]
    exact harg0
  have hSpi : S ≤ Real.pi / 2 := by
    rw [hS]
    exact Real.arcsin_le_pi_div_two _
  have hs0 : 0 ≤ s := by
    rw [hs, Real.arcsin_nonneg]
    exact (div_pos hδ0 hr0).le
  have hspi : s ≤ Real.pi / 2 := by
    rw [hs]
    exact Real.arcsin_le_pi_div_two _
  have hinterior : 2 * s - t < strongInteriorRatio r * t := by
    apply interior_contact_strict_gap hr0 hrhalf hδ0 hδr hs
    simpa only [strongEndpointPhi] using ht
  have hupperComparison :
      strongRLambda ≤ r → strongR₁ * Real.sin t ≤ δ₀ / r → S ≤ s := by
    intro _ hgeom
    rw [hS, hs]
    exact Real.arcsin_le_arcsin hgeom
  have hfrozenComparison :
      r ≤ strongRLambda → strongR₁ * Real.sin t ≤ δ₀ / strongRLambda →
        2 * S - t < strongFrozenRatio * t := by
    intro hrrl hgeom
    have hrl0 : 0 < strongRLambda :=
      strongParameterDomain.a_pos.trans strongParameterDomain.a_lt_rLambda
    have hδrl : δ₀ < strongRLambda := hδr.trans_le hrrl
    have hx0 : 0 < δ₀ / strongRLambda := div_pos hδ0 hrl0
    have hx1 : δ₀ / strongRLambda < 1 := (div_lt_one hrl0).2 hδrl
    let u := Real.arcsin (δ₀ / strongRLambda)
    have huLower : δ₀ / strongRLambda < u := by
      dsimp [u]
      exact endpoint_self_lt_arcsin hx0 hx1
    have hSu : S ≤ u := by
      rw [hS]
      exact Real.arcsin_le_arcsin hgeom
    have hus : u ≤ s := by
      dsimp [u]
      rw [hs]
      exact arcsin_div_mono_radius hδ0.le hr0 hrrl
    have hatan : Real.arctan (2 * δ₀) < 2 * δ₀ :=
      arctan_lt_self_of_pos (by positivity)
    have hatan_u : Real.arctan (2 * δ₀) < 2 * strongRLambda * u := by
      have := mul_lt_mul_of_pos_left huLower (show 0 < 2 * strongRLambda by positivity)
      have heq : 2 * strongRLambda * (δ₀ / strongRLambda) = 2 * δ₀ := by
        field_simp
      rw [heq] at this
      linarith
    have hcore : (1 - 2 * strongRLambda) * S < t := by
      have hcoef : 0 < 1 - 2 * strongRLambda := by
        norm_num [strongRLambda]
      rw [ht, strongEndpointPhi, hs] at *
      nlinarith
    have hden : 0 < 1 - 2 * strongRLambda := by
      norm_num [strongRLambda]
    rw [strongFrozenRatio, div_mul_eq_mul_div, lt_div_iff₀ hden]
    nlinarith
  have hlargeRaw : 2 * max s S - t < Real.pi := by
    have hmaxpi : max s S ≤ Real.pi / 2 := max_le hspi hSpi
    linarith
  have hsaturation : Real.pi ≤ strongPaperG r * t →
      2 * max s S - t < strongPaperG r * t :=
    fun hsat => hlargeRaw.trans_le hsat
  have hfinal : 2 * max s S - t < strongPaperG r * t := by
    rcases hdispatch with hlarge | hupper | hfrozen
    · exact hsaturation hlarge
    · have hSs := hupperComparison hupper.1 hupper.2
      rw [max_eq_left hSs]
      exact hinterior.trans_le (mul_le_mul_of_nonneg_right
        (strongInteriorRatio_le_paperG r) ht0.le)
    · have hSf := hfrozenComparison hfrozen.1 hfrozen.2
      have hsPaper := hinterior.trans_le (mul_le_mul_of_nonneg_right
        (strongInteriorRatio_le_paperG r) ht0.le)
      have hSPaper := hSf.trans_le (mul_le_mul_of_nonneg_right
        (strongFrozenRatio_le_paperG r) ht0.le)
      rcases le_total s S with hsS | hSs
      · rw [max_eq_right hsS]
        exact hSPaper
      · rw [max_eq_left hSs]
        exact hsPaper
  exact ⟨ht0, harg0, hsinS, hS0, hSpi, hinterior,
    hupperComparison, hfrozenComparison, hsaturation, hfinal⟩

end

end StarKakeyaLower
