import StarKakeyaLower.OneTenthLobesGeometry

/-! # Actual endpoint lobes and their extension gaps

The entire interval is proved to belong to the filled unit triangle. Neither
lobe containment nor the extension inequality is an input assumption.
-/
open Set
namespace StarKakeyaLower.OneTenth
noncomputable section

def endpointRadius (h x : ℝ) : ℝ := Real.sqrt (x^2+h^2)

theorem endpointRadius_pos {h x : ℝ} (hh : 0 < h) : 0 < endpointRadius h x := by
  exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg x])

theorem endpointAngle_sin {h x : ℝ} (hh : 0 < h) :
    Real.sin (endpointAngle h x) = h / endpointRadius h x := by
  have hR := endpointRadius_pos (x := x) hh
  have hRsq : (endpointRadius h x)^2 = x^2+h^2 :=
    Real.sq_sqrt (by positivity)
  have hS : Real.sqrt (1+(x/h)^2) = endpointRadius h x / h := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (div_nonneg hR.le hh.le)).mp
    rw [Real.sq_sqrt (by positivity)]
    simp only [div_pow, hRsq]
    field_simp [hh.ne']
    <;> ring
  simp only [endpointAngle, Real.sin_pi_div_two_sub, Real.cos_arctan, hS]
  field_simp

theorem endpointAngle_le_half {h x : ℝ} (hh : 0 < h) (hx : 0 ≤ x) :
    endpointAngle h x ≤ Real.pi/2 := by
  have ha : 0 ≤ Real.arctan (x/h) := Real.arctan_nonneg.mpr (div_nonneg hx hh.le)
  unfold endpointAngle
  linarith

theorem endpointAngle_eq_arcsin {h x : ℝ} (hh : 0 < h) (hx : 0 ≤ x) :
    endpointAngle h x = Real.arcsin (h / endpointRadius h x) := by
  rw [← endpointAngle_sin hh]
  exact (Real.arcsin_sin (by linarith [endpointAngle_pos h x, Real.pi_pos])
    (endpointAngle_le_half hh hx)).symm

theorem endpointAngle_eq_arctan {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    endpointAngle h x = Real.arctan (h/x) := by
  simpa only [inv_div, endpointAngle] using
    (Real.arctan_inv_of_pos (div_pos hx hh)).symm

theorem endpointAngle_neg (h x : ℝ) :
    endpointAngle h (-x) = Real.pi-endpointAngle h x := by
  simp only [endpointAngle, neg_div, Real.arctan_neg]
  ring

theorem endpointAngle_lt_arcsin {h x r : ℝ} (hh : 0 < h) (hx : 0 ≤ x)
    (hhr : h < r) (hrR : r < endpointRadius h x) :
    endpointAngle h x < Real.arcsin (h/r) := by
  rw [endpointAngle_eq_arcsin hh hx]
  have hr := hh.trans hhr
  have hR := endpointRadius_pos (x := x) hh
  apply Real.arcsin_lt_arcsin (by linarith [div_pos hh hR])
    ((div_lt_div_iff₀ hR hr).mpr (by nlinarith))
    ((div_le_one hr).mpr hhr.le)

/-- Far lobe with the compulsory external-foot cone cap. -/
theorem far_lobe_subset {α h x r : ℝ} (hh : 0 < h) (hx : 0 ≤ x)
    (hhr : h < r) (hrR : r < endpointRadius h x) :
    (fun φ => polarPoint r (α+φ)) ''
      Icc (endpointAngle h x)
        (min (endpointAngle h (x-1)) (Real.arcsin (h/r))) ⊆
      supportNeedleTriangle α h (x-1/2) := by
  rintro _ ⟨φ,hφ,rfl⟩
  have hcone : φ ∈ Icc (endpointAngle h x) (endpointAngle h (x-1)) :=
    ⟨hφ.1,hφ.2.trans (min_le_left _ _)⟩
  have hchart : φ ∈ Icc 0 Real.pi :=
    ⟨(endpointAngle_pos h x).le.trans hφ.1,
      hcone.2.trans (endpointAngle_lt_pi h (x-1)).le⟩
  apply (two_window_section_iff hh hhr hchart).mpr
  exact ⟨hcone,Or.inl ⟨hchart.1,hφ.2.trans (min_le_right _ _)⟩⟩

/-- The displayed far interval is nondegenerate whenever the circle is strictly
inside the far endpoint radius. -/
theorem far_lobe_length_pos {h x r : ℝ} (hh : 0 < h) (hx : 0 ≤ x)
    (hhr : h < r) (hrR : r < endpointRadius h x) :
    0 < min (endpointAngle h (x-1)) (Real.arcsin (h/r))-endpointAngle h x := by
  exact sub_pos.mpr (lt_min ((endpointAngle_strictAnti hh) (by linarith))
    (endpointAngle_lt_arcsin hh hx hhr hrR))

/-- For an internal/endpoint foot the positive-half section is exactly the
complete far lobe, not merely a small subinterval around its endpoint. -/
theorem internal_far_lobe_iff {α h p m r φ : ℝ} (hh : 0 < h)
    (hm : 0 ≤ m) (hunit : p+m=1) (hhr : h < r)
    (hφ : φ ∈ Icc 0 (Real.pi/2)) :
    polarPoint r (α+φ) ∈ supportNeedleTriangle α h (p-1/2) ↔
      φ ∈ Icc (endpointAngle h p) (Real.arcsin (h/r)) := by
  have hr := hh.trans hhr
  have hpi := Real.pi_pos
  have hd : Real.pi/2 ≤ endpointAngle h (p-1) := by
    rw [show p-1 = -m by linarith, endpointAngle_neg]
    linarith [endpointAngle_le_half hh hm]
  rw [entire_section_iff hh hr ⟨hφ.1,by linarith [hφ.2]⟩]
  have hs := sin_le_iff_le_arcsin_of_mem_left_half
    (div_nonneg hh.le hr.le) ((div_lt_one hr).mpr hhr) hφ.1 hφ.2
  have hheight : r*Real.sin φ ≤ h ↔ φ ≤ Real.arcsin (h/r) := by
    rw [← hs,le_div_iff₀ hr]
    constructor <;> intro H <;> nlinarith
  rw [hheight]
  change ((_ ∧ _) ∧ _) ↔ (_ ∧ _)
  constructor
  · exact fun H => ⟨H.1.1,H.2⟩
  · exact fun H => ⟨⟨H.1,hφ.2.trans hd⟩,H.2⟩

/-- Eligible-near counterpart. It is valid for every near radius; eligibility
is imposed only when choosing a common radial bank. -/
theorem internal_near_lobe_subset {α h p m r : ℝ} (hh : 0 < h)
    (hp : 0 ≤ p) (hm : 0 ≤ m) (hunit : p+m=1) (hhr : h < r)
    (hrN : r < endpointRadius h m) :
    (fun φ => polarPoint r (α+φ)) ''
      Icc (Real.pi-Real.arcsin (h/r)) (Real.pi-endpointAngle h m) ⊆
      supportNeedleTriangle α h (p-1/2) := by
  rintro _ ⟨φ,hφ,rfl⟩
  have hpi := Real.pi_pos
  have hhalf : Real.pi/2 ≤ φ := by linarith [hφ.1,Real.arcsin_le_pi_div_two (h/r)]
  have hφpi : φ < Real.pi := by linarith [hφ.2,endpointAngle_pos h m]
  apply (two_window_section_iff hh hhr ⟨by linarith, hφpi.le⟩).mpr
  refine ⟨⟨(endpointAngle_le_half hh hp).trans hhalf,?_⟩,
    Or.inr ⟨hφ.1,hφpi.le⟩⟩
  rw [show p-1 = -m by linarith,endpointAngle_neg]
  exact hφ.2

/-- No far/near endpoint is identified with a nearest segment point. -/
theorem unit_endpoint_radii {h p m : ℝ} (hunit : p+m=1) :
    1 ≤ endpointRadius h p + endpointRadius h m := by
  have hp := Real.sqrt_nonneg (p^2+h^2)
  have hm := Real.sqrt_nonneg (m^2+h^2)
  have hp' : |p| ≤ endpointRadius h p := by
    rw [endpointRadius,← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg h])
  have hm' : |m| ≤ endpointRadius h m := by
    rw [endpointRadius,← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg h])
  linarith [le_abs_self p,le_abs_self m]

#print axioms far_lobe_subset
#print axioms internal_far_lobe_iff
#print axioms internal_near_lobe_subset
end
end StarKakeyaLower.OneTenth
