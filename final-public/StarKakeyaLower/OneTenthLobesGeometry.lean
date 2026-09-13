import StarKakeyaLower.LiGeometry

/-!
# Entire physical sections of unit support triangles

The endpoint angle is `π/2 - atan(x/h)`, the continuous upper-half-plane
argument of `(x,h)` for `h>0`. In particular negative/zero `x` is not discarded.
All conclusions concern the existing filled `supportNeedleTriangle`, not a
segment-circle intersection or an assumed angular envelope.
-/

open Set
namespace StarKakeyaLower.OneTenth
noncomputable section

/-- Upper-half-plane argument, valid for every longitudinal coordinate. -/
def endpointAngle (h x : ℝ) : ℝ := Real.pi / 2 - Real.arctan (x / h)

theorem endpointAngle_pos (h x : ℝ) : 0 < endpointAngle h x := by
  unfold endpointAngle
  linarith [Real.arctan_lt_pi_div_two (x/h)]

theorem endpointAngle_lt_pi (h x : ℝ) : endpointAngle h x < Real.pi := by
  unfold endpointAngle
  linarith [Real.neg_pi_div_two_lt_arctan (x/h)]

theorem endpointAngle_strictAnti {h : ℝ} (hh : 0 < h) :
    StrictAnti (endpointAngle h) := by
  intro x y hxy
  unfold endpointAngle
  have := Real.arctan_strictMono ((div_lt_div_iff_of_pos_right hh).mpr hxy)
  linarith

/-- Cotangent inversion is used only on the genuine positive half-plane. -/
theorem arctan_cot {φ : ℝ} (hφ : φ ∈ Ioo 0 Real.pi) :
    Real.arctan (Real.cos φ / Real.sin φ) = Real.pi / 2 - φ := by
  have harg : Real.pi / 2 - φ ∈ Ioo (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [hφ.1, hφ.2]
  simpa only [Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub] using Real.arctan_tan harg.1 harg.2

theorem endpointAngle_le_iff {h x φ : ℝ} (hh : 0 < h)
    (hφ : φ ∈ Ioo 0 Real.pi) :
    endpointAngle h x ≤ φ ↔ h * Real.cos φ ≤ x * Real.sin φ := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2
  have hi := Real.arctan_le_arctan_iff (x := Real.cos φ / Real.sin φ) (y := x/h)
  rw [arctan_cot hφ, div_le_div_iff₀ hs hh] at hi
  unfold endpointAngle
  constructor <;> intro H
  · have := hi.mp (by linarith : Real.pi/2-φ ≤ Real.arctan (x/h))
    nlinarith
  · have := hi.mpr (by nlinarith : Real.cos φ * h ≤ x * Real.sin φ)
    linarith

theorem le_endpointAngle_iff {h x φ : ℝ} (hh : 0 < h)
    (hφ : φ ∈ Ioo 0 Real.pi) :
    φ ≤ endpointAngle h x ↔ x * Real.sin φ ≤ h * Real.cos φ := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2
  have hi := Real.arctan_le_arctan_iff (x := x/h) (y := Real.cos φ / Real.sin φ)
  rw [arctan_cot hφ, div_le_div_iff₀ hh hs] at hi
  unfold endpointAngle
  constructor <;> intro H
  · have := hi.mp (by linarith : Real.arctan (x/h) ≤ Real.pi/2-φ)
    nlinarith
  · have := hi.mpr (by nlinarith : x * Real.sin φ ≤ Real.cos φ * h)
    linarith

/-- Exact entire section in a physical support chart; `x-1` and `x` are the
actual two endpoints. This covers internal, endpoint, and external feet. -/
theorem entire_section_iff {α h x r φ : ℝ} (hh : 0 < h) (hr : 0 < r)
    (hφ : φ ∈ Icc 0 Real.pi) :
    polarPoint r (α+φ) ∈ supportNeedleTriangle α h (x-1/2) ↔
      φ ∈ Icc (endpointAngle h x) (endpointAngle h (x-1)) ∧
        r * Real.sin φ ≤ h := by
  change (α+φ) ∈ trianglePolarTrace (supportNeedleTriangle α h (x-1/2)) r ↔
    φ ∈ Icc (endpointAngle h x) (endpointAngle h (x-1)) ∧ r * Real.sin φ ≤ h
  rw [mem_trianglePolarTrace_eliminatedCoordinates_iff _ _ _ _ _ hr hh]
  simp only [add_sub_cancel_left]
  constructor
  · rintro ⟨hp, hhgt, hlo, hhi⟩
    have hs : 0 < Real.sin φ := (mul_pos_iff_of_pos_left hr).mp hp
    have hφ' : φ ∈ Ioo 0 Real.pi := by
      constructor
      · rcases hφ.1.eq_or_lt with H | H
        · rw [← H, Real.sin_zero] at hs; linarith
        · exact H
      · rcases hφ.2.lt_or_eq with H | H
        · exact H
        · rw [H, Real.sin_pi] at hs; linarith
    refine ⟨⟨(endpointAngle_le_iff hh hφ').mpr ?_,
      (le_endpointAngle_iff hh hφ').mpr ?_⟩, hhgt⟩
    · nlinarith
    · nlinarith
  · rintro ⟨⟨hlo,hhi⟩, hhgt⟩
    have hφ' : φ ∈ Ioo 0 Real.pi :=
      ⟨(endpointAngle_pos h x).trans_le hlo,
        hhi.trans_lt (endpointAngle_lt_pi h (x-1))⟩
    have h1 := (endpointAngle_le_iff hh hφ').mp hlo
    have h2 := (le_endpointAngle_iff hh hφ').mp hhi
    refine ⟨mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hφ'.1 hφ'.2), hhgt, ?_, ?_⟩
    · nlinarith
    · nlinarith

/-- Below the support height every ray of the full cone really occurs. -/
theorem full_cone_iff {α h x r φ : ℝ} (hh : 0 < h) (hr : 0 < r)
    (hrh : r ≤ h) (hφ : φ ∈ Icc 0 Real.pi) :
    polarPoint r (α+φ) ∈ supportNeedleTriangle α h (x-1/2) ↔
      φ ∈ Icc (endpointAngle h x) (endpointAngle h (x-1)) := by
  rw [entire_section_iff hh hr hφ]
  exact and_iff_left (by nlinarith [Real.sin_le_one φ])

/-- Above the support height the entire cone is cut by the two sine windows.
In particular the external-foot cone is not replaced by an oversized lobe. -/
theorem two_window_section_iff {α h x r φ : ℝ} (hh : 0 < h)
    (hhr : h < r) (hφ : φ ∈ Icc 0 Real.pi) :
    polarPoint r (α+φ) ∈ supportNeedleTriangle α h (x-1/2) ↔
      φ ∈ Icc (endpointAngle h x) (endpointAngle h (x-1)) ∩
        (Icc 0 (Real.arcsin (h/r)) ∪
          Icc (Real.pi-Real.arcsin (h/r)) Real.pi) := by
  have hr := hh.trans hhr
  rw [entire_section_iff hh hr hφ]
  have hw := positivePeriod_sin_le_eq_twoIntervals (φ := φ)
    (div_nonneg hh.le hr.le) ((div_lt_one hr).mpr hhr)
  have hm : r * Real.sin φ ≤ h ↔ Real.sin φ ≤ h/r := by
    rw [le_div_iff₀ hr]; constructor <;> intro H <;> nlinarith
  rw [hm]
  change (_ ∧ _) ↔ (_ ∧ _)
  exact and_congr_right (fun _ => by simpa only [hφ, true_and] using hw)

/-- Signed-height covariance transports the point AND the triangle, retaining
its original side. No union with a reflected copy is taken. -/
theorem signed_section_iff (α h c r φ : ℝ) :
    polarPoint r (α-φ) ∈ supportNeedleTriangle α (-h) c ↔
      polarPoint r (α+φ) ∈ supportNeedleTriangle α h c := by
  change (α-φ) ∈ trianglePolarTrace (supportNeedleTriangle α (-h) c) r ↔
    (α+φ) ∈ trianglePolarTrace (supportNeedleTriangle α h c) r
  rw [mem_trianglePolarTrace_supportCoordinates_iff,
    mem_trianglePolarTrace_supportCoordinates_iff]
  simp only [sub_sub_cancel_left, Real.sin_neg, Real.cos_neg, add_sub_cancel_left]
  constructor <;> rintro ⟨l,hl,x,hx,hn,ht⟩ <;>
    exact ⟨l,hl,x,hx,by nlinarith,ht⟩

/-- Zero-height rays are present, including the eligible opposite endpoint.
This is exact, and does not remove zero-height directions as a null set. -/
theorem zero_height_section_iff {α x r φ : ℝ} (hr : 0 < r)
    (hφ : φ ∈ Icc 0 Real.pi) :
    polarPoint r (α+φ) ∈ supportNeedleTriangle α 0 (x-1/2) ↔
      (φ=0 ∧ r ≤ x) ∨ (φ=Real.pi ∧ r ≤ 1-x) := by
  change (α+φ) ∈ trianglePolarTrace (supportNeedleTriangle α 0 (x-1/2)) r ↔
    (φ=0 ∧ r ≤ x) ∨ (φ=Real.pi ∧ r ≤ 1-x)
  rw [mem_trianglePolarTrace_zeroHeight_iff hr
    (by simpa using hφ.1) (by simpa using hφ.2)]
  constructor <;> rintro (⟨h1,h2⟩ | ⟨h1,h2⟩)
  · exact Or.inl ⟨by linarith,by linarith⟩
  · exact Or.inr ⟨by linarith,by linarith⟩
  · exact Or.inl ⟨by linarith,by linarith⟩
  · exact Or.inr ⟨by linarith,by linarith⟩

/-- Exact entire quotient-circle section, not just a statement restricted to
an arbitrarily assumed chart representative. Every physical trace point has a
representative in this upper-half-plane cone. -/
theorem entire_circle_section_eq {α h x r : ℝ} (hh : 0 < h) (hr : 0 < r) :
    polarCircleTrace (supportNeedleTriangle α h (x-1/2)) r =
      (fun φ : ℝ => ((α+φ : ℝ) : PolarAngle)) ''
        {φ | φ ∈ Icc (endpointAngle h x) (endpointAngle h (x-1)) ∧
          r*Real.sin φ ≤ h} := by
  rw [polarCircleTrace_supportNeedleTriangle_eq_positiveChart_image hr hh]
  ext q
  constructor
  · rintro ⟨θ,⟨hθ,hchart⟩,rfl⟩
    refine ⟨θ-α,?_,by
      change ((α+(θ-α) : ℝ) : PolarAngle) = (θ : PolarAngle)
      rw [show α+(θ-α)=θ by ring]⟩
    have hφ : θ-α ∈ Icc 0 Real.pi := ⟨by linarith [hchart.1],by linarith [hchart.2]⟩
    apply (entire_section_iff (α := α) (x := x) hh hr hφ).mp
    rw [show α+(θ-α)=θ by ring]
    exact hθ
  · rintro ⟨φ,⟨hφ,hhgt⟩,rfl⟩
    have hchart : φ ∈ Icc 0 Real.pi :=
      ⟨(endpointAngle_pos h x).le.trans hφ.1,
        hφ.2.trans (endpointAngle_lt_pi h (x-1)).le⟩
    exact ⟨α+φ,⟨(entire_section_iff hh hr hchart).mpr ⟨hφ,hhgt⟩,
      ⟨by linarith [hchart.1],by linarith [hchart.2]⟩⟩,rfl⟩

#print axioms entire_circle_section_eq
#print axioms entire_section_iff
#print axioms two_window_section_iff
#print axioms signed_section_iff
#print axioms zero_height_section_iff
end
end StarKakeyaLower.OneTenth
