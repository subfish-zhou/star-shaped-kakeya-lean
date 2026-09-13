import StarKakeyaLower.OneTenthCaps

/-!
# Quarter caps for the literal positive-height endpoint formula

`OneTenthLobesGeometry.endpointAngle h x` is definitionally
`pi/2 - arctan (x/h)`, and `OneTenthLobes.endpointRadius h x` is
`sqrt (x^2+h^2)`. Keeping these formulas literal gives the analytic estimates
a small import closure independent of the physical-inclusion proofs. There is
no substitute angle, assumed sine identity, or assumed cap. Consumers unfold
the two definitions to apply these theorems to the actual geometry.

Strictly positive height is essential: at zero height the totalized formula is
NOT a physical argument. Use the Lobes zero-height section theorem instead.
-/

namespace StarKakeyaLower.OneTenth.Caps
noncomputable section

/-- The exact positive-coordinate relation between the actual upper-half-plane
argument and its slope angle. Both denominators are strictly positive. -/
theorem upper_angle_eq_arctan {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    Real.pi/2-Real.arctan (x/h) = Real.arctan (h/x) := by
  simpa only [inv_div] using (Real.arctan_inv_of_pos (div_pos hx hh)).symm

/-- Exact sine/radius relation for the actual upper-half-plane argument.
This holds for negative, zero, and positive longitudinal coordinate. -/
theorem upper_angle_sine_eq {h x : ℝ} (hh : 0 < h) :
    Real.sin (Real.pi/2-Real.arctan (x/h)) = h/Real.sqrt (x^2+h^2) := by
  have hR : 0 < Real.sqrt (x^2+h^2) := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg x])
  have hRsq : (Real.sqrt (x^2+h^2))^2 = x^2+h^2 := Real.sq_sqrt (by positivity)
  have hS : Real.sqrt (1+(x/h)^2) = Real.sqrt (x^2+h^2)/h := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (div_nonneg hR.le hh.le)).mp
    rw [Real.sq_sqrt (by positivity)]
    simp only [div_pow, hRsq]
    field_simp [hh.ne']
    ring
  rw [Real.sin_pi_div_two_sub, Real.cos_arctan, hS]
  field_simp

/-- Strict far estimate for the literal endpoint formulas, including the
endpoint foot `m=0`, treated separately without dividing by `m`. -/
theorem far_endpoint_sum_lt_pi {h p m : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 1/5) (hp : 1/2 ≤ p)
    (hm : 0 ≤ m) (hunit : p+m=1) :
    5*(Real.pi/2-Real.arctan (p/h)) + (Real.pi/2-Real.arctan (m/h)) < Real.pi := by
  have hp0 : 0 < p := by linarith
  rcases hm.eq_or_lt with hmz | hmpos
  · have hm0 : m=0 := hmz.symm
    have hp1 : p=1 := by linarith
    subst m
    subst p
    rw [upper_angle_eq_arctan hh (by norm_num : (0:ℝ)<1)]
    simp only [div_one, zero_div, Real.arctan_zero, sub_zero]
    have hb := arctan_le_ratio hh.le
    linarith [Real.pi_gt_three]
  · have hp1 : p < 1 := by linarith
    have hmEq : m=1-p := by linarith
    rw [upper_angle_eq_arctan hh hp0, upper_angle_eq_arctan hh hmpos, hmEq]
    exact far_arctan_sum_lt_pi hp hp1 hh hhmax

/-- Actual endpoint-formula far cap, including the endpoint-foot boundary. -/
theorem far_endpoint_quarter_cap {h p m : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 1/5) (hp : 1/2 ≤ p)
    (hm : 0 ≤ m) (hunit : p+m=1) :
    4*(Real.pi/2-Real.arctan (p/h)) ≤
      Real.pi-(Real.pi/2-Real.arctan (p/h))-(Real.pi/2-Real.arctan (m/h)) := by
  linarith [far_endpoint_sum_lt_pi hh hhmax hp hm hunit]

/-- Actual endpoint radius eligibility proves the sine bound. -/
theorem endpoint_sine_le_half {h x : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 1/5) (hR : 2/5 ≤ Real.sqrt (x^2+h^2)) :
    Real.sin (Real.pi/2-Real.arctan (x/h)) ≤ 1/2 := by
  rw [upper_angle_sine_eq hh]
  have hR0 : 0 < Real.sqrt (x^2+h^2) := by linarith
  exact (div_le_iff₀ hR0).mpr (by nlinarith)

/-- Nonnegative longitudinal coordinate places the actual positive-height
endpoint angle in the correct sine-monotonicity interval. -/
theorem upper_angle_mem_first_quadrant {h x : ℝ} (hh : 0 < h) (hx : 0 ≤ x) :
    Real.pi/2-Real.arctan (x/h) ∈ Set.Icc 0 (Real.pi/2) := by
  have hlow := Real.arctan_lt_pi_div_two (x/h)
  have hupp := Real.arctan_nonneg.mpr (div_nonneg hx hh.le)
  constructor <;> linarith

/-- Actual endpoint pi/6 estimate, with eligibility and coordinates as inputs. -/
theorem eligible_endpoint_le_pi_div_six {h x : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 1/5) (hx : 0 ≤ x)
    (hR : 2/5 ≤ Real.sqrt (x^2+h^2)) :
    Real.pi/2-Real.arctan (x/h) ≤ Real.pi/6 := by
  exact angle_le_pi_div_six_of_sin_le_half (upper_angle_mem_first_quadrant hh hx)
    (endpoint_sine_le_half hh hhmax hR)

/-- Both actual quarter caps from two eligible endpoint radii. Neither cap nor
any area estimate is assumed. The shared height is strictly positive. -/
theorem eligible_endpoint_quarter_caps {h p m : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 1/5) (hp : 0 ≤ p) (hm : 0 ≤ m)
    (hM : 2/5 ≤ Real.sqrt (p^2+h^2)) (hN : 2/5 ≤ Real.sqrt (m^2+h^2)) :
    (Real.pi/2-Real.arctan (p/h)) ≤ Real.pi/6 ∧
    (Real.pi/2-Real.arctan (m/h)) ≤ Real.pi/6 ∧
    4*(Real.pi/2-Real.arctan (p/h)) ≤
      Real.pi-(Real.pi/2-Real.arctan (p/h))-(Real.pi/2-Real.arctan (m/h)) ∧
    4*(Real.pi/2-Real.arctan (m/h)) ≤
      Real.pi-(Real.pi/2-Real.arctan (p/h))-(Real.pi/2-Real.arctan (m/h)) := by
  exact both_quarter_caps_of_sine_bounds
    (upper_angle_mem_first_quadrant hh hp) (upper_angle_mem_first_quadrant hh hm)
    (endpoint_sine_le_half hh hhmax hM) (endpoint_sine_le_half hh hhmax hN)

end
end StarKakeyaLower.OneTenth.Caps
