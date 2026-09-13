import StarKakeyaLower.OneTenthLobesGap

/-! # The full-cone banks, including far-only low labels -/
open Set Real
namespace StarKakeyaLower.OneTenth
noncomputable section

theorem endpointAngle_le_ratio {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    endpointAngle h x ≤ h/x := by
  rw [endpointAngle_eq_arctan hh hx]
  have ht := Real.le_tan (Real.arctan_nonneg.mpr (div_nonneg hh.le hx.le))
    (Real.arctan_lt_pi_div_two (h/x))
  simpa only [Real.tan_arctan] using ht

/-- Uniform far-only cone cap, with no assumption on the near endpoint radius.
The coarse split at p=4/5 is sufficient for the required 1/4 extension ratio. -/
theorem low_far_cone_cap {h p m : ℝ} (hh : 0 < h) (hhmax : h ≤ 1/5)
    (hp : 1/2 ≤ p) (hm : 0 ≤ m) (hunit : p+m=1) :
    endpointAngle h p ≤ (Real.pi-endpointAngle h m-endpointAngle h p)/4 := by
  have hp0 : 0 < p := by linarith
  have hb := endpointAngle_le_ratio hh hp0
  have hc := endpointAngle_le_half hh hm
  have hpi := Real.pi_gt_three
  by_cases hps : p ≤ 4/5
  · have hm0 : 0 < m := by linarith
    have hhm : h/m ≤ 1 := (div_le_one hm0).mpr (by linarith)
    have hcm : endpointAngle h m ≤ Real.pi/4 := by
      rw [endpointAngle_eq_arctan hh hm0,← Real.arctan_one]
      exact Real.arctan_le_arctan hhm
    have hbp : h/p ≤ 2/5 := (div_le_iff₀ hp0).mpr (by nlinarith)
    linarith
  · have hbp : h/p ≤ 1/4 := (div_le_iff₀ hp0).mpr (by nlinarith)
    linarith

/-- An eligible endpoint has offset at most π/6. -/
theorem eligible_endpoint_angle_le {h x : ℝ} (hh : 0 < h) (hhmax : h ≤ 1/5)
    (hx : 0 ≤ x) (hR : 2/5 ≤ endpointRadius h x) :
    endpointAngle h x ≤ Real.pi/6 := by
  rw [endpointAngle_eq_arcsin hh hx]
  have hratio : h/endpointRadius h x ≤ 1/2 :=
    (div_le_iff₀ (endpointRadius_pos hh)).mpr (by nlinarith)
  have hhalf : Real.arcsin (1/2 : ℝ) = Real.pi/6 := by
    rw [← Real.sin_pi_div_six]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  exact (Real.arcsin_le_arcsin hratio).trans_eq hhalf

/-- The near cap uses eligibility of both endpoints, unlike the far-only cap. -/
theorem eligible_near_cone_cap {h p m : ℝ} (hh : 0 < h) (hhmax : h ≤ 1/5)
    (hp : 0 ≤ p) (hm : 0 ≤ m)
    (hM : 2/5 ≤ endpointRadius h p) (hN : 2/5 ≤ endpointRadius h m) :
    endpointAngle h m ≤ (Real.pi-endpointAngle h m-endpointAngle h p)/4 := by
  have hb := eligible_endpoint_angle_le hh hhmax hp hM
  have hc := eligible_endpoint_angle_le hh hhmax hm hN
  linarith

/-- Whole cone and far extension budget on the low inner bank. -/
theorem low_far_full_cone_receipt {α h p m r : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 1/5) (hp : 1/2 ≤ p) (hm : 0 ≤ m)
    (hunit : p+m=1) (hr : 0 < r) (hrh : r ≤ h) :
    (fun φ => polarPoint r (α+φ)) ''
      Icc (endpointAngle h p) (Real.pi-endpointAngle h m) ⊆
      supportNeedleTriangle α h (p-1/2) ∧
    endpointAngle h p ≤ (Real.pi-endpointAngle h m-endpointAngle h p)/4 := by
  refine ⟨?_,low_far_cone_cap hh hhmax hp hm hunit⟩
  rintro _ ⟨φ,hφ,rfl⟩
  apply (full_cone_iff hh hr hrh
    ⟨(endpointAngle_pos h p).le.trans hφ.1,
      by linarith [hφ.2,endpointAngle_pos h m]⟩).mpr
  rw [show p-1 = -m by linarith,endpointAngle_neg]
  exact hφ

/-- Near full-cone receipt is the same physical set, not a second copy. -/
theorem eligible_near_full_cone_receipt {α h p m r : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 1/5) (hp : 1/2 ≤ p) (hm : 0 ≤ m)
    (hunit : p+m=1) (hr : 0 < r) (hrh : r ≤ h)
    (hM : 2/5 ≤ endpointRadius h p) (hN : 2/5 ≤ endpointRadius h m) :
    (fun φ => polarPoint r (α+φ)) ''
      Icc (endpointAngle h p) (Real.pi-endpointAngle h m) ⊆
      supportNeedleTriangle α h (p-1/2) ∧
    endpointAngle h m ≤ (Real.pi-endpointAngle h m-endpointAngle h p)/4 := by
  exact ⟨(low_far_full_cone_receipt hh hhmax hp hm hunit hr hrh).1,
    eligible_near_cone_cap hh hhmax (by linarith) hm hM hN⟩

/-- Cosine of the genuine endpoint argument, including external-foot signs. -/
theorem endpointAngle_cos {h x : ℝ} (hh : 0 < h) :
    Real.cos (endpointAngle h x) = x/endpointRadius h x := by
  have hchart := And.intro (endpointAngle_pos h x) (endpointAngle_lt_pi h x)
  have h1 := (endpointAngle_le_iff hh hchart).mp le_rfl
  have h2 := (le_endpointAngle_iff hh hchart).mp le_rfl
  rw [endpointAngle_sin hh] at h1 h2
  have heq : h*Real.cos (endpointAngle h x) = x*(h/endpointRadius h x) := le_antisymm h1 h2
  have hR := endpointRadius_pos (x := x) hh
  apply (eq_div_iff hR.ne').mpr
  field_simp [hR.ne'] at heq
  nlinarith

/-- The unit base gives sin(gamma)=h/(MN) exactly, for both foot cases. -/
theorem unit_cone_sine {h p : ℝ} (hh : 0 < h) :
    Real.sin (endpointAngle h (p-1)-endpointAngle h p) =
      h/(endpointRadius h (p-1)*endpointRadius h p) := by
  rw [Real.sin_sub,endpointAngle_sin hh,endpointAngle_sin hh,
    endpointAngle_cos hh,endpointAngle_cos hh]
  field_simp
  <;> ring

/-- Paper G08 without an integral: sin(gamma) <= gamma and N <= M give
h <= M² gamma. This uses the actual unit endpoints, also when p>1. -/
theorem general_far_cone_cap {h p : ℝ} (hh : 0 < h) (hp : 1/2 ≤ p) :
    endpointAngle h p / (endpointAngle h (p-1)-endpointAngle h p) ≤
      (endpointRadius h p)^2/p := by
  have hp0 : 0 < p := by linarith
  have hM := endpointRadius_pos (x := p) hh
  have hN := endpointRadius_pos (x := p-1) hh
  have hNM : endpointRadius h (p-1) ≤ endpointRadius h p := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hg : 0 < endpointAngle h (p-1)-endpointAngle h p :=
    sub_pos.mpr ((endpointAngle_strictAnti hh) (by linarith))
  have hs := Real.sin_le hg.le
  rw [unit_cone_sine hh] at hs
  have hhg := (div_le_iff₀ (mul_pos hN hM)).mp hs
  have hprod := mul_le_mul_of_nonneg_left hNM (mul_nonneg hg.le hM.le)
  have hb := (le_div_iff₀ hp0).mp (endpointAngle_le_ratio hh hp0)
  apply (div_le_div_iff₀ hg hp0).mpr
  nlinarith

/-- All foot positions: the real capped far lobe is nonempty, is physically
inside the triangle, and has the maximum of the cone and lobe budgets. -/
theorem general_far_lobe_receipt {α h p r : ℝ} (hh : 0 < h) (hp : 1/2 ≤ p)
    (hhr : h < r) (hrM : r < endpointRadius h p) :
    (fun φ => polarPoint r (α+φ)) ''
      Icc (endpointAngle h p)
        (min (endpointAngle h (p-1)) (Real.arcsin (h/r))) ⊆
        supportNeedleTriangle α h (p-1/2) ∧
    0 < min (endpointAngle h (p-1)) (Real.arcsin (h/r))-endpointAngle h p ∧
    endpointAngle h p /
        (min (endpointAngle h (p-1)) (Real.arcsin (h/r))-endpointAngle h p) ≤
      max ((endpointRadius h p)^2/p) (r/(endpointRadius h p-r)) := by
  have hp0 : 0 ≤ p := by linarith
  refine ⟨far_lobe_subset hh hp0 hhr hrM,
    far_lobe_length_pos hh hp0 hhr hrM,?_⟩
  rcases le_total (endpointAngle h (p-1)) (Real.arcsin (h/r)) with H | H
  · rw [min_eq_left H]
    exact (general_far_cone_cap hh hp).trans (le_max_left _ _)
  · rw [min_eq_right H]
    exact (endpoint_lobe_gap hh hp0 hhr hrM).trans (le_max_right _ _)

/-- The radius/height-uniform G08 bound. The strict R>H hypothesis merely
states positivity of its displayed denominator. -/
theorem bounded_far_cone_cap {h H p R : ℝ} (hh : 0 < h) (hhH : h ≤ H)
    (hHhalf : H ≤ 1/2) (hp : 1/2 ≤ p) (hRH : H < R)
    (hM : endpointRadius h p ≤ R) :
    endpointAngle h p / (endpointAngle h (p-1)-endpointAngle h p) ≤
      R^2 / Real.sqrt (R^2-H^2) := by
  have hp0 : 0 < p := by linarith
  have hR0 : 0 < R := by linarith
  have hMsq : (endpointRadius h p)^2 = p^2+h^2 := Real.sq_sqrt (by positivity)
  have hM0 := endpointRadius_pos (x := p) hh
  have hsq : p^2+h^2 ≤ R^2 := by nlinarith
  let q := Real.sqrt (R^2-h^2)
  have hrad : 0 ≤ R^2-h^2 := by nlinarith
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q^2 = R^2-h^2 := Real.sq_sqrt hrad
  have hpq : p ≤ q := by nlinarith
  have hqpos : 0 < q := hp0.trans_le hpq
  have hqp : h^2 ≤ p*q := by nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr hqp)
  have hfrac : (endpointRadius h p)^2/p ≤ R^2/q := by
    apply (div_le_div_iff₀ hp0 hqpos).mpr
    nlinarith [congrArg (fun t : ℝ => t*q) hMsq,
      congrArg (fun t : ℝ => t*p) hq2]
  have hQpos : 0 < Real.sqrt (R^2-H^2) := Real.sqrt_pos.mpr (by nlinarith)
  have hQq : Real.sqrt (R^2-H^2) ≤ q := by
    apply Real.sqrt_le_sqrt
    nlinarith
  exact (general_far_cone_cap hh hp).trans (hfrac.trans
    ((div_le_div_iff₀ hqpos hQpos).mpr (mul_le_mul_of_nonneg_left hQq (sq_nonneg R))))

#print axioms bounded_far_cone_cap
#print axioms general_far_lobe_receipt
#print axioms general_far_cone_cap
#print axioms low_far_full_cone_receipt
#print axioms eligible_near_full_cone_receipt
end
end StarKakeyaLower.OneTenth
