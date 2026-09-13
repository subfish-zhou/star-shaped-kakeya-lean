import Mathlib

/-!
# One-tenth low-height quarter-cone caps

Pure angle estimates, independent of any area receipt or physical inclusion.
The far cap is the same-claim split at `x = 4/5`, not a stationary-point search.
The coordinate corollaries require strictly positive denominators. Zero height
is explicitly separate; these arctangent slope formulas are not a replacement
for the physical zero-height singleton-ray section.
-/

open Set
namespace StarKakeyaLower.OneTenth.Caps
noncomputable section

/-- The elementary arctangent bound, obtained without differentiation. -/
theorem arctan_le_ratio {t : ℝ} (ht : 0 ≤ t) : Real.arctan t ≤ t := by
  have H := Real.le_tan (Real.arctan_nonneg.mpr ht) (Real.arctan_lt_pi_div_two t)
  simpa only [Real.tan_arctan] using H

/-- Strict far-cap inequality on the low, internal-foot geometry.
No eligibility/radius assumption on the near endpoint is needed. -/
theorem far_arctan_sum_lt_pi {x z : ℝ}
    (hx : 1/2 ≤ x) (hx1 : x < 1) (hz : 0 < z) (hzmax : z ≤ 1/5) :
    5 * Real.arctan (z/x) + Real.arctan (z/(1-x)) < Real.pi := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < 1-x := by linarith
  have hb := arctan_le_ratio (div_nonneg hz.le hx0.le)
  have hpi := Real.pi_gt_three
  by_cases hsplit : x ≤ 4/5
  · have ht : z/(1-x) ≤ 1 := (div_le_one hy0).mpr (by linarith)
    have hc : Real.arctan (z/(1-x)) ≤ Real.pi/4 := by
      rw [← Real.arctan_one]
      exact Real.arctan_mono ht
    have hq : z/x ≤ 2/5 := (div_le_iff₀ hx0).mpr (by nlinarith)
    linarith
  · have hq : z/x ≤ 1/4 := (div_le_iff₀ hx0).mpr (by nlinarith)
    have hc := Real.arctan_lt_pi_div_two (z/(1-x))
    linarith

/-- Reusable far quarter cap, stated as `4 b ≤ gamma`. -/
theorem far_quarter_cap {x z : ℝ}
    (hx : 1/2 ≤ x) (hx1 : x < 1) (hz : 0 < z) (hzmax : z ≤ 1/5) :
    4 * Real.arctan (z/x) ≤ Real.pi - Real.arctan (z/x) -
      Real.arctan (z/(1-x)) := by
  linarith [far_arctan_sum_lt_pi hx hx1 hz hzmax]

/-- Named-angle adapter: angle and cone-width equations are definitions,
not assumptions of the desired cap. -/
theorem far_quarter_cap_of_angles {x z b c gamma : ℝ}
    (hx : 1/2 ≤ x) (hx1 : x < 1) (hz : 0 < z) (hzmax : z ≤ 1/5)
    (hb : b = Real.arctan (z/x)) (hc : c = Real.arctan (z/(1-x)))
    (hg : gamma = Real.pi-b-c) : 4*b ≤ gamma := by
  subst b; subst c; subst gamma
  exact far_quarter_cap hx hx1 hz hzmax

/-- On the genuine first-quadrant range, sine at most one half forces an
angle at most pi/6. The range is essential, not an angular receipt. -/
theorem angle_le_pi_div_six_of_sin_le_half {b : ℝ}
    (hb : b ∈ Icc 0 (Real.pi/2)) (hs : Real.sin b ≤ 1/2) :
    b ≤ Real.pi/6 := by
  by_contra H
  have hlt : Real.pi/6 < b := lt_of_not_ge H
  have hsin := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (show -(Real.pi/2) ≤ Real.pi/6 by linarith [Real.pi_pos]) hb.2 hlt
  rw [Real.sin_pi_div_six] at hsin
  linarith

/-- Eligible-near angles give both caps on the very same cone width. -/
theorem both_quarter_caps_of_sine_bounds {b c : ℝ}
    (hb : b ∈ Icc 0 (Real.pi/2)) (hc : c ∈ Icc 0 (Real.pi/2))
    (hsb : Real.sin b ≤ 1/2) (hsc : Real.sin c ≤ 1/2) :
    b ≤ Real.pi/6 ∧ c ≤ Real.pi/6 ∧
    4*b ≤ Real.pi-b-c ∧ 4*c ≤ Real.pi-b-c := by
  have B := angle_le_pi_div_six_of_sin_le_half hb hsb
  have C := angle_le_pi_div_six_of_sin_le_half hc hsc
  exact ⟨B, C, by linarith, by linarith⟩

/-- Exact Euclidean endpoint sine identity for the positive-coordinate
arctangent chart. The denominator `x` is never zero. -/
theorem sin_arctan_ratio_eq {x z : ℝ} (hx : 0 < x) :
    Real.sin (Real.arctan (z/x)) = z / Real.sqrt (x^2+z^2) := by
  have hi : 1 + (z/x)^2 = (x^2+z^2)/x^2 := by
    field_simp
  rw [Real.sin_arctan, hi, Real.sqrt_div (by positivity), Real.sqrt_sq hx.le]
  field_simp

/-- Sine eligibility is derived from actual height and Euclidean radius,
not posited as a cap or area hypothesis. -/
theorem sine_le_half_of_coordinates {x z : ℝ} (hx : 0 < x)
    (hzmax : z ≤ 1/5) (hR : 2/5 ≤ Real.sqrt (x^2+z^2)) :
    Real.sin (Real.arctan (z/x)) ≤ 1/2 := by
  rw [sin_arctan_ratio_eq hx]
  have hR0 : 0 < Real.sqrt (x^2+z^2) := by linarith
  exact (div_le_iff₀ hR0).mpr (by nlinarith)

/-- Both quarter caps from two positive coordinate endpoints with the same
height. The unit-base equation is not needed for this stronger local fact. -/
theorem both_quarter_caps_of_coordinates {x y z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hzmax : z ≤ 1/5)
    (hRx : 2/5 ≤ Real.sqrt (x^2+z^2))
    (hRy : 2/5 ≤ Real.sqrt (y^2+z^2)) :
    Real.arctan (z/x) ≤ Real.pi/6 ∧ Real.arctan (z/y) ≤ Real.pi/6 ∧
    4*Real.arctan (z/x) ≤ Real.pi-Real.arctan (z/x)-Real.arctan (z/y) ∧
    4*Real.arctan (z/y) ≤ Real.pi-Real.arctan (z/x)-Real.arctan (z/y) := by
  apply both_quarter_caps_of_sine_bounds
  · exact ⟨Real.arctan_nonneg.mpr (div_nonneg hz.le hx.le),
      (Real.arctan_lt_pi_div_two _).le⟩
  · exact ⟨Real.arctan_nonneg.mpr (div_nonneg hz.le hy.le),
      (Real.arctan_lt_pi_div_two _).le⟩
  · exact sine_le_half_of_coordinates hx hzmax hRx
  · exact sine_le_half_of_coordinates hy hzmax hRy

/-- Separate zero-height slope identity, only with positive longitudinal
coordinates. This does NOT assert that the physical section is a full cone. -/
theorem zero_height_slopes {x y : ℝ} (_hx : 0 < x) (_hy : 0 < y) :
    Real.arctan ((0 : ℝ)/x) = 0 ∧ Real.arctan ((0 : ℝ)/y) = 0 := by
  simp

end
end StarKakeyaLower.OneTenth.Caps
