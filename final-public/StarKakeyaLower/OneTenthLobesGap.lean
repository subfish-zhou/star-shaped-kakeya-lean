import StarKakeyaLower.OneTenthLobes

/-! # Quantified gaps for the actual lobes

The inverse-sine convexity argument is proved locally in this small import
closure, using the sign of the second derivative on the stated interval.
The final receipts pair the numerical gap with the already proved physical
set inclusion, rather than leaving the geometry as a premise.
-/
open Set Real
namespace StarKakeyaLower.OneTenth
noncomputable section

private theorem convexOn_arcsin_local {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ConvexOn ℝ (Icc 0 c) Real.arcsin := by
  apply convexOn_of_deriv2_nonneg (convex_Icc 0 c) Real.continuous_arcsin.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact (Real.hasDerivAt_arcsin (by linarith [hx.1])
      (by linarith [hx.2])).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [Real.deriv_arcsin,interior_Icc] at *
    have hp : 0 < 1-x^2 := by nlinarith [hx.1,hx.2]
    have hs : DifferentiableAt ℝ (fun y : ℝ => √(1-y^2)) x :=
      ((Real.hasDerivAt_sqrt hp.ne').comp x
        ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2))).differentiableAt
    simpa [one_div] using (hs.inv (by positivity)).differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hp : 0 < 1-x^2 := by nlinarith [hx.1,hx.2]
    have hs : HasDerivAt (fun y : ℝ => √(1-y^2))
        ((1/(2*√(1-x^2)))*(-(2*x))) x := by
      convert (Real.hasDerivAt_sqrt hp.ne').comp x
        ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)) using 1
      all_goals simp [mul_comm]
    have hi : HasDerivAt (fun y : ℝ => 1/√(1-y^2))
        (-((1/(2*√(1-x^2)))*(-(2*x)))/(√(1-x^2))^2) x := by
      simpa [one_div] using hs.inv (by positivity)
    rw [show deriv^[2] Real.arcsin x = deriv (deriv Real.arcsin) x by rfl,
      Real.deriv_arcsin,hi.deriv]
    have hr : 0 < √(1-x^2) := Real.sqrt_pos.mpr hp
    field_simp
    simpa using hx.1.le

/-- Radius scaling, including zero height. -/
theorem lobe_radius_mul_arcsin_le {h r R : ℝ} (hh : 0 ≤ h)
    (hhr : h < r) (hrR : r < R) :
    R * Real.arcsin (h/R) ≤ r * Real.arcsin (h/r) := by
  rcases hh.eq_or_lt with rfl | hh
  · simp
  have hr := hh.trans hhr
  have hR := hr.trans hrR
  have hx : 0 < h/R := div_pos hh hR
  have hxy : h/R ≤ h/r := (div_le_div_iff₀ hR hr).mpr (by nlinarith)
  have hy : h/r < 1 := (div_lt_one hr).mpr hhr
  have hy0 : 0 ≤ h/r := (div_pos hh hr).le
  have hc := convexOn_arcsin_local hy0 hy
  have hs := hc.secant_mono (a := 0) (x := h/R) (y := h/r)
    ⟨le_rfl,hy0⟩ ⟨hx.le,hxy⟩ ⟨hy0,le_rfl⟩ hx.ne'
    (div_pos hh hr).ne' hxy
  simp only [Real.arcsin_zero,sub_zero] at hs
  field_simp [hh.ne',hr.ne',hR.ne'] at hs
  nlinarith

theorem endpoint_lobe_gap {h x r : ℝ} (hh : 0 < h) (hx : 0 ≤ x)
    (hhr : h < r) (hrR : r < endpointRadius h x) :
    endpointAngle h x / (Real.arcsin (h/r)-endpointAngle h x) ≤
      r / (endpointRadius h x-r) := by
  have hp := endpointAngle_lt_arcsin hh hx hhr hrR
  apply (div_le_div_iff₀ (sub_pos.mpr hp) (sub_pos.mpr hrR)).mpr
  have hs := lobe_radius_mul_arcsin_le hh.le hhr hrR
  rw [← endpointAngle_eq_arcsin hh hx] at hs
  nlinarith

/-- The arctangent version in the positive-longitudinal chart. -/
theorem atan_arcsin_lobe_gap {h x r : ℝ} (hh : 0 < h) (hx : 0 < x)
    (hhr : h < r) (hrR : r < endpointRadius h x) :
    Real.arctan (h/x) / (Real.arcsin (h/r)-Real.arctan (h/x)) ≤
      r / (endpointRadius h x-r) := by
  rw [← endpointAngle_eq_arctan hh hx]
  exact endpoint_lobe_gap hh hx.le hhr hrR

/-- Complete far physical lobe, positive length, and its common-bank gap in
one theorem. Unit length and the perpendicular-foot signs are retained. -/
theorem far_lobe_receipt {α h p m r R₀ : ℝ} (hh : 0 < h)
    (hp : 0 ≤ p) (hm : 0 ≤ m) (hunit : p+m=1) (hhr : h < r)
    (hrR : r < R₀) (hR : R₀ ≤ endpointRadius h p) :
    (fun φ => polarPoint r (α+φ)) ''
        Icc (endpointAngle h p) (Real.arcsin (h/r)) ⊆
          supportNeedleTriangle α h (p-1/2) ∧
      0 < Real.arcsin (h/r)-endpointAngle h p ∧
      endpointAngle h p / (Real.arcsin (h/r)-endpointAngle h p) ≤ r/(R₀-r) := by
  have hrRp := hrR.trans_le hR
  have hlt := endpointAngle_lt_arcsin hh hp hhr hrRp
  refine ⟨?_,sub_pos.mpr hlt,?_⟩
  · rintro _ ⟨φ,hφ,rfl⟩
    apply (internal_far_lobe_iff hh hm hunit hhr
      ⟨(endpointAngle_pos h p).le.trans hφ.1,
        hφ.2.trans (Real.arcsin_le_pi_div_two _)⟩).mpr hφ
  · exact (endpoint_lobe_gap hh hp hhr hrRp).trans
      ((div_le_div_iff₀ (sub_pos.mpr hrRp) (sub_pos.mpr hrR)).mpr
        (by nlinarith [hh.trans hhr]))

/-- Eligible-near physical lobe, positive length, and the SAME common-bank
extension ratio. No independent area/arc-length sum is asserted. -/
theorem near_lobe_receipt {α h p m r R₀ : ℝ} (hh : 0 < h)
    (hp : 0 ≤ p) (hm : 0 ≤ m) (hunit : p+m=1) (hhr : h < r)
    (hrR : r < R₀) (hR : R₀ ≤ endpointRadius h m) :
    (fun φ => polarPoint r (α+φ)) ''
        Icc (Real.pi-Real.arcsin (h/r)) (Real.pi-endpointAngle h m) ⊆
          supportNeedleTriangle α h (p-1/2) ∧
      0 < Real.arcsin (h/r)-endpointAngle h m ∧
      endpointAngle h m / (Real.arcsin (h/r)-endpointAngle h m) ≤ r/(R₀-r) := by
  have hrNm := hrR.trans_le hR
  refine ⟨internal_near_lobe_subset hh hp hm hunit hhr hrNm,
    sub_pos.mpr (endpointAngle_lt_arcsin hh hm hhr hrNm),?_⟩
  exact (endpoint_lobe_gap hh hm hhr hrNm).trans
    ((div_le_div_iff₀ (sub_pos.mpr hrNm) (sub_pos.mpr hrR)).mpr
      (by nlinarith [hh.trans hhr]))

#print axioms far_lobe_receipt
#print axioms near_lobe_receipt
#print axioms atan_arcsin_lobe_gap
end
end StarKakeyaLower.OneTenth
