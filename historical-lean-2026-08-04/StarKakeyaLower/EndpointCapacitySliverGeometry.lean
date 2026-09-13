import StarKakeyaLower.EndpointCapacityGeometry
import StarKakeyaLower.EndpointCapacitySliverCover

/-!
# Endpoint-capacity physical sliver geometry

The analytic and coordinate geometry behind the radial-sliver theorem.
For a support line at positive height `h` and a radial window `[r,R]`, the
positive and negative tangential sides generate the exact arcsine windows

* `[arcsin (h/R), arcsin (h/r)]`, and
* `[π - arcsin (h/r), π - arcsin (h/R)]`.

The module also proves that the paper dilation factor `(R+r)/(R-r)` is large
enough.  It works with the coordinate triangle `supportNeedleTriangle`; the
adapter from an arbitrary physical `DirectionNeedle` and the side-selection
argument are separate later steps.
-/

open Set Real

namespace StarKakeyaLower

noncomputable section

private theorem endpointCapacity_convexOn_arcsin_Icc
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ConvexOn ℝ (Icc 0 c) Real.arcsin := by
  apply convexOn_of_deriv2_nonneg (convex_Icc 0 c)
    Real.continuous_arcsin.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 < x := hx.1
    have hxc : x < c := hx.2
    exact (Real.hasDerivAt_arcsin (by linarith) (by linarith)).differentiableAt
      |>.differentiableWithinAt
  · intro x hx
    rw [Real.deriv_arcsin]
    rw [interior_Icc] at hx
    have hx0 : 0 < x := hx.1
    have hxc : x < c := hx.2
    have hp : 0 < 1 - x ^ 2 := by nlinarith
    have hs : DifferentiableAt ℝ (fun y : ℝ => √(1 - y ^ 2)) x := by
      exact ((Real.hasDerivAt_sqrt (ne_of_gt hp)).comp x
        ((hasDerivAt_const x (1 : ℝ)).sub
          ((hasDerivAt_id x).pow 2))).differentiableAt
    simpa [one_div] using (hs.inv (by positivity)).differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 < x := hx.1
    have hxc : x < c := hx.2
    have hp : 0 < 1 - x ^ 2 := by nlinarith
    have hs : HasDerivAt (fun y : ℝ => √(1 - y ^ 2))
        ((1 / (2 * √(1 - x ^ 2))) * (-(2 * x))) x := by
      convert (Real.hasDerivAt_sqrt (ne_of_gt hp)).comp x
        ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)) using 1
      all_goals simp [mul_comm]
    have hi : HasDerivAt (fun y : ℝ => 1 / √(1 - y ^ 2))
        (-((1 / (2 * √(1 - x ^ 2))) * (-(2 * x))) /
          (√(1 - x ^ 2)) ^ 2) x := by
      simpa [one_div] using hs.inv (by positivity)
    rw [show deriv^[2] Real.arcsin x = deriv (deriv Real.arcsin) x by rfl,
      Real.deriv_arcsin, hi.deriv]
    have hr : 0 < √(1 - x ^ 2) := Real.sqrt_pos.2 hp
    field_simp
    simpa using hx0.le

private theorem endpointCapacity_arcsin_div_mono
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < 1) :
    Real.arcsin x / x ≤ Real.arcsin y / y := by
  have hy0 : 0 ≤ y := le_trans (le_of_lt hx) hxy
  have hconv := endpointCapacity_convexOn_arcsin_Icc hy0 hy
  have hs := hconv.secant_mono (a := 0) (x := x) (y := y)
    ⟨le_rfl, hy0⟩ ⟨le_of_lt hx, hxy⟩ ⟨hy0, le_rfl⟩
    (ne_of_gt hx) (ne_of_gt (lt_of_lt_of_le hx hxy)) hxy
  simpa [Real.arcsin_zero] using hs

/-- The load-bearing inverse-sine scaling inequality, including `h = 0`. -/
theorem radius_mul_arcsin_le
    {h r R : ℝ} (hh : 0 ≤ h) (hhr : h < r) (hrR : r < R) :
    R * Real.arcsin (h / R) ≤ r * Real.arcsin (h / r) := by
  rcases hh.eq_or_lt with rfl | hh
  · simp [Real.arcsin_zero]
  have hr : 0 < r := lt_trans hh hhr
  have hR : 0 < R := lt_trans hr hrR
  have hx : 0 < h / R := div_pos hh hR
  have hxy : h / R ≤ h / r := by
    apply (div_le_div_iff₀ hR hr).2
    nlinarith
  have hy : h / r < 1 := (div_lt_one hr).2 hhr
  have hm := endpointCapacity_arcsin_div_mono hx hxy hy
  field_simp [ne_of_gt hh, ne_of_gt hr, ne_of_gt hR] at hm
  nlinarith

/-- The arcsine sliver dilation ratio is bounded by the paper factor
`(R+r)/(R-r)`.  At `h = 0`, totalized division makes the left side zero. -/
theorem arcsin_sum_div_diff_le
    {h r R : ℝ} (hh : 0 ≤ h) (hhr : h < r) (hrR : r < R) :
    (Real.arcsin (h / r) + Real.arcsin (h / R)) /
        (Real.arcsin (h / r) - Real.arcsin (h / R)) ≤
      (R + r) / (R - r) := by
  rcases hh.eq_or_lt with rfl | hh
  · simp only [zero_div, Real.arcsin_zero, add_zero, sub_self, div_zero]
    exact div_nonneg (by nlinarith) (sub_nonneg.2 hrR.le)
  have hr : 0 < r := lt_trans hh hhr
  have hR : 0 < R := lt_trans hr hrR
  have hxy : h / R < h / r := by
    apply (div_lt_div_iff₀ hR hr).2
    nlinarith
  have hxpos : 0 < h / R := div_pos hh hR
  have hxneg : -1 ≤ h / R := by linarith
  have hyone : h / r ≤ 1 := (div_le_one hr).2 hhr.le
  have harc : Real.arcsin (h / R) < Real.arcsin (h / r) :=
    Real.arcsin_lt_arcsin hxneg hxy hyone
  have hden : 0 < Real.arcsin (h / r) - Real.arcsin (h / R) :=
    sub_pos.2 harc
  have hRr : 0 < R - r := sub_pos.2 hrR
  apply (div_le_div_iff₀ hden hRr).2
  have hgate := radius_mul_arcsin_le
    (h := h) (r := r) (R := R) hh.le hhr hrR
  nlinarith

private theorem endpointCapacity_strictConvexOn_arcsin_Icc
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    StrictConvexOn ℝ (Icc 0 c) Real.arcsin := by
  apply strictConvexOn_of_deriv2_pos (convex_Icc 0 c)
    Real.continuous_arcsin.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  have hx0 : 0 < x := hx.1
  have hxc : x < c := hx.2
  have hp : 0 < 1 - x ^ 2 := by nlinarith
  have hs : HasDerivAt (fun y : ℝ => √(1 - y ^ 2))
      ((1 / (2 * √(1 - x ^ 2))) * (-(2 * x))) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hp)).comp x
      ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)) using 1
    all_goals simp [mul_comm]
  have hi : HasDerivAt (fun y : ℝ => 1 / √(1 - y ^ 2))
      (-((1 / (2 * √(1 - x ^ 2))) * (-(2 * x))) /
        (√(1 - x ^ 2)) ^ 2) x := by
    simpa [one_div] using hs.inv (by positivity)
  rw [show deriv^[2] Real.arcsin x = deriv (deriv Real.arcsin) x by rfl,
    Real.deriv_arcsin, hi.deriv]
  have hr : 0 < √(1 - x ^ 2) := Real.sqrt_pos.2 hp
  field_simp
  simpa using hx0

/-- On `(0,1]`, `arcsin x / x` is strictly increasing. -/
theorem arcsin_div_strictMono_pair
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y ≤ 1) :
    Real.arcsin x / x < Real.arcsin y / y := by
  have hy0 : 0 ≤ y := le_of_lt (hx.trans hxy)
  have hconv := endpointCapacity_strictConvexOn_arcsin_Icc hy0 hy
  have ha : 0 < 1 - x / y := by
    rw [sub_pos, div_lt_one (hx.trans hxy)]
    exact hxy
  have hb : 0 < x / y := div_pos hx (hx.trans hxy)
  have hab : (1 - x / y) + x / y = (1 : ℝ) := by ring
  have hs := hconv.2 (x := 0) (y := y)
    ⟨le_rfl, hy0⟩ ⟨hy0, le_rfl⟩ (ne_of_lt (hx.trans hxy)) ha hb hab
  have harg : (1 - x / y) • (0 : ℝ) + (x / y) • y = x := by
    simp [smul_eq_mul]
    field_simp [ne_of_gt (hx.trans hxy)]
  rw [harg, Real.arcsin_zero] at hs
  simp only [smul_eq_mul, mul_zero, zero_add] at hs
  apply (div_lt_iff₀ hx).2
  calc
    Real.arcsin x < x / y * Real.arcsin y := hs
    _ = Real.arcsin y / y * x := by ring

/-- Strict inverse-sine scaling inequality for `0 < h ≤ r < R`. -/
theorem radius_mul_arcsin_lt
    {h r R : ℝ} (hh : 0 < h) (hhr : h ≤ r) (hrR : r < R) :
    R * Real.arcsin (h / R) < r * Real.arcsin (h / r) := by
  have hr : 0 < r := lt_of_lt_of_le hh hhr
  have hR : 0 < R := hr.trans hrR
  have hx : 0 < h / R := div_pos hh hR
  have hxy : h / R < h / r := by
    apply (div_lt_div_iff₀ hR hr).2
    nlinarith
  have hy : h / r ≤ 1 := (div_le_one hr).2 hhr
  have hm := arcsin_div_strictMono_pair hx hxy hy
  field_simp [ne_of_gt hh, ne_of_gt hr, ne_of_gt hR] at hm
  nlinarith

/-- The positive-height arcsine sliver ratio is strictly smaller than the paper
factor, as required for membership in an open quotient dilation. -/
theorem arcsin_sum_div_diff_lt
    {h r R : ℝ} (hh : 0 < h) (hhr : h ≤ r) (hrR : r < R) :
    (Real.arcsin (h / r) + Real.arcsin (h / R)) /
        (Real.arcsin (h / r) - Real.arcsin (h / R)) <
      (R + r) / (R - r) := by
  have hr : 0 < r := lt_of_lt_of_le hh hhr
  have hR : 0 < R := hr.trans hrR
  have hxy : h / R < h / r := by
    apply (div_lt_div_iff₀ hR hr).2
    nlinarith
  have hxneg : -1 ≤ h / R := by
    linarith [div_pos hh hR]
  have hyone : h / r ≤ 1 := (div_le_one hr).2 hhr
  have harc : Real.arcsin (h / R) < Real.arcsin (h / r) :=
    Real.arcsin_lt_arcsin hxneg hxy hyone
  have hden : 0 < Real.arcsin (h / r) - Real.arcsin (h / R) :=
    sub_pos.2 harc
  have hRr : 0 < R - r := sub_pos.2 hrR
  apply (div_lt_div_iff₀ hden hRr).2
  have hgate := radius_mul_arcsin_lt
    (h := h) (r := r) (R := R) hh hhr hrR
  nlinarith

/-- Positive-side support-line/circle intersection in polar coordinates. -/
theorem supportPoint_sqrt_eq_polarPoint_arcsin
    {α h rho : ℝ} (hh : 0 ≤ h) (hhrho : h ≤ rho) (hrho : 0 < rho) :
    supportPoint α h (Real.sqrt (rho ^ 2 - h ^ 2)) =
      polarPoint rho (α + Real.arcsin (h / rho)) := by
  have hk0 : 0 ≤ h / rho := div_nonneg hh hrho.le
  have hk1 : h / rho ≤ 1 := (div_le_one hrho).2 hhrho
  have hrad : 0 ≤ rho ^ 2 - h ^ 2 := by nlinarith
  have hsqrt : Real.sqrt (rho ^ 2 - h ^ 2) =
      rho * Real.sqrt (1 - (h / rho) ^ 2) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg hrho.le (Real.sqrt_nonneg _))).mp
    rw [Real.sq_sqrt hrad, mul_pow, Real.sq_sqrt]
    · field_simp
    · nlinarith [sq_nonneg (h / rho)]
  have hsin : Real.sin (Real.arcsin (h / rho)) = h / rho :=
    Real.sin_arcsin (by linarith) hk1
  have hcos : Real.cos (Real.arcsin (h / rho)) =
      Real.sqrt (1 - (h / rho) ^ 2) := Real.cos_arcsin _
  ext <;>
    simp [supportPoint, polarPoint, addCoordinatePlane, scaleCoordinatePlane,
      unitDirection, unitNormal, Real.cos_add, Real.sin_add, hsin, hcos, hsqrt] <;>
    field_simp <;> ring

/-- Negative-side support-line/circle intersection in polar coordinates. -/
theorem supportPoint_neg_sqrt_eq_polarPoint_pi_sub_arcsin
    {α h rho : ℝ} (hh : 0 ≤ h) (hhrho : h ≤ rho) (hrho : 0 < rho) :
    supportPoint α h (-Real.sqrt (rho ^ 2 - h ^ 2)) =
      polarPoint rho (α + Real.pi - Real.arcsin (h / rho)) := by
  have hk0 : 0 ≤ h / rho := div_nonneg hh hrho.le
  have hk1 : h / rho ≤ 1 := (div_le_one hrho).2 hhrho
  have hrad : 0 ≤ rho ^ 2 - h ^ 2 := by nlinarith
  have hsqrt : Real.sqrt (rho ^ 2 - h ^ 2) =
      rho * Real.sqrt (1 - (h / rho) ^ 2) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg hrho.le (Real.sqrt_nonneg _))).mp
    rw [Real.sq_sqrt hrad, mul_pow, Real.sq_sqrt]
    · field_simp
    · nlinarith [sq_nonneg (h / rho)]
  have hsin : Real.sin (Real.arcsin (h / rho)) = h / rho :=
    Real.sin_arcsin (by linarith) hk1
  have hcos : Real.cos (Real.arcsin (h / rho)) =
      Real.sqrt (1 - (h / rho) ^ 2) := Real.cos_arcsin _
  ext <;>
    simp [supportPoint, polarPoint, addCoordinatePlane, scaleCoordinatePlane,
      unitDirection, unitNormal, Real.cos_sub, Real.sin_sub, Real.cos_add,
      Real.sin_add, hsin, hcos, hsqrt] <;>
    field_simp <;> ring

/-- Positive-side polar contact lies in the filled support triangle whenever its
signed tangential parameter lies on the unit chord. -/
theorem polarPoint_arcsin_mem_supportNeedleTriangle
    {α h c rho : ℝ} (hh : 0 ≤ h) (hhrho : h ≤ rho) (hrho : 0 < rho)
    (hx : Real.sqrt (rho ^ 2 - h ^ 2) ∈ Icc (c - 1 / 2) (c + 1 / 2)) :
    polarPoint rho (α + Real.arcsin (h / rho)) ∈
      supportNeedleTriangle α h c := by
  refine ⟨1, ⟨by norm_num, by norm_num⟩,
    Real.sqrt (rho ^ 2 - h ^ 2), hx, ?_⟩
  rw [show scaleCoordinatePlane 1
      (supportPoint α h (Real.sqrt (rho ^ 2 - h ^ 2))) =
      supportPoint α h (Real.sqrt (rho ^ 2 - h ^ 2)) by
    ext <;> simp [scaleCoordinatePlane]]
  exact (supportPoint_sqrt_eq_polarPoint_arcsin hh hhrho hrho).symm

/-- Negative-side analogue of `polarPoint_arcsin_mem_supportNeedleTriangle`. -/
theorem polarPoint_pi_sub_arcsin_mem_supportNeedleTriangle
    {α h c rho : ℝ} (hh : 0 ≤ h) (hhrho : h ≤ rho) (hrho : 0 < rho)
    (hx : -Real.sqrt (rho ^ 2 - h ^ 2) ∈ Icc (c - 1 / 2) (c + 1 / 2)) :
    polarPoint rho (α + Real.pi - Real.arcsin (h / rho)) ∈
      supportNeedleTriangle α h c := by
  refine ⟨1, ⟨by norm_num, by norm_num⟩,
    -Real.sqrt (rho ^ 2 - h ^ 2), hx, ?_⟩
  rw [show scaleCoordinatePlane 1
      (supportPoint α h (-Real.sqrt (rho ^ 2 - h ^ 2))) =
      supportPoint α h (-Real.sqrt (rho ^ 2 - h ^ 2)) by
    ext <;> simp [scaleCoordinatePlane]]
  exact (supportPoint_neg_sqrt_eq_polarPoint_pi_sub_arcsin hh hhrho hrho).symm

/-- Exact image of a positive radial window under the decreasing arcsine
offset. -/
theorem arcsin_div_image_Icc
    {h r R : ℝ} (hh : 0 < h) (hhr : h ≤ r) (hrR : r ≤ R) :
    (fun rho : ℝ => Real.arcsin (h / rho)) '' Icc r R =
      Icc (Real.arcsin (h / R)) (Real.arcsin (h / r)) := by
  have hrpos : 0 < r := lt_of_lt_of_le hh hhr
  have hRpos : 0 < R := hrpos.trans_le hrR
  have hratioR0 : 0 ≤ h / R := (div_pos hh hRpos).le
  have hratior0 : 0 ≤ h / r := (div_pos hh hrpos).le
  have hratioR1 : h / R ≤ 1 := (div_le_one hRpos).2 (hhr.trans hrR)
  have hratior1 : h / r ≤ 1 := (div_le_one hrpos).2 hhr
  ext φ
  constructor
  · rintro ⟨rho, hrho, rfl⟩
    have hrhopos : 0 < rho := hrpos.trans_le hrho.1
    have hlo : h / R ≤ h / rho := by
      apply (div_le_div_iff₀ hRpos hrhopos).2
      exact mul_le_mul_of_nonneg_left hrho.2 hh.le
    have hhi : h / rho ≤ h / r := by
      apply (div_le_div_iff₀ hrhopos hrpos).2
      exact mul_le_mul_of_nonneg_left hrho.1 hh.le
    exact ⟨Real.arcsin_le_arcsin hlo, Real.arcsin_le_arcsin hhi⟩
  · intro hφ
    have hφpos : 0 < φ :=
      (Real.arcsin_pos.2 (div_pos hh hRpos)).trans_le hφ.1
    have hφhalf : φ ≤ Real.pi / 2 :=
      hφ.2.trans (Real.arcsin_le_pi_div_two _)
    have hφpi : φ < Real.pi := hφhalf.trans_lt (by linarith [Real.pi_pos])
    have hsinpos : 0 < Real.sin φ :=
      Real.sin_pos_of_pos_of_lt_pi hφpos hφpi
    have hsinR : Real.sin (Real.arcsin (h / R)) = h / R :=
      Real.sin_arcsin (by linarith) hratioR1
    have hsinr : Real.sin (Real.arcsin (h / r)) = h / r :=
      Real.sin_arcsin (by linarith) hratior1
    have hsinlower : h / R ≤ Real.sin φ := by
      rw [← hsinR]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [Real.arcsin_nonneg.2 hratioR0, Real.pi_pos])
        hφhalf hφ.1
    have hsinupper : Real.sin φ ≤ h / r := by
      rw [← hsinr]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [hφpos, Real.pi_pos])
        (Real.arcsin_le_pi_div_two _) hφ.2
    let rho := h / Real.sin φ
    have hrhoLower : r ≤ rho := by
      dsimp [rho]
      apply (le_div_iff₀ hsinpos).2
      simpa [mul_comm] using (le_div_iff₀ hrpos).1 hsinupper
    have hrhoUpper : rho ≤ R := by
      dsimp [rho]
      apply (div_le_iff₀ hsinpos).2
      simpa [mul_comm] using (div_le_iff₀ hRpos).1 hsinlower
    refine ⟨rho, ⟨hrhoLower, hrhoUpper⟩, ?_⟩
    have hratio : h / rho = Real.sin φ := by
      dsimp [rho]
      field_simp [hh.ne']
    change Real.arcsin (h / rho) = φ
    rw [hratio]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) hφhalf

/-- Positive-side radial-window containment in the exact arcsine sliver. -/
theorem supportChord_positiveRadialWindow_mem_triangle
    {α h c r R rho : ℝ} (hh : 0 < h) (hhr : h ≤ r) (hrR : r ≤ R)
    (hleft : c - 1 / 2 ≤ Real.sqrt (r ^ 2 - h ^ 2))
    (hright : Real.sqrt (R ^ 2 - h ^ 2) ≤ c + 1 / 2)
    (hrho : rho ∈ Icc r R) :
    Real.arcsin (h / rho) ∈
        Icc (Real.arcsin (h / R)) (Real.arcsin (h / r)) ∧
      polarPoint rho (α + Real.arcsin (h / rho)) ∈
        supportNeedleTriangle α h c := by
  have hrpos : 0 < r := lt_of_lt_of_le hh hhr
  have hRpos : 0 < R := hrpos.trans_le hrR
  have hrhopos : 0 < rho := hrpos.trans_le hrho.1
  have hlo : h / R ≤ h / rho := by
    apply (div_le_div_iff₀ hRpos hrhopos).2
    exact mul_le_mul_of_nonneg_left hrho.2 hh.le
  have hhi : h / rho ≤ h / r := by
    apply (div_le_div_iff₀ hrhopos hrpos).2
    exact mul_le_mul_of_nonneg_left hrho.1 hh.le
  have hang := And.intro (Real.arcsin_le_arcsin hlo)
    (Real.arcsin_le_arcsin hhi)
  have hsqr : r ^ 2 - h ^ 2 ≤ rho ^ 2 - h ^ 2 := by
    nlinarith [hrho.1, hrpos.le, hrhopos.le]
  have hsqR : rho ^ 2 - h ^ 2 ≤ R ^ 2 - h ^ 2 := by
    nlinarith [hrho.2, hrhopos.le, hRpos.le]
  have hx : Real.sqrt (rho ^ 2 - h ^ 2) ∈
      Icc (c - 1 / 2) (c + 1 / 2) :=
    ⟨hleft.trans (Real.sqrt_le_sqrt hsqr),
      (Real.sqrt_le_sqrt hsqR).trans hright⟩
  exact ⟨hang,
    polarPoint_arcsin_mem_supportNeedleTriangle
      hh.le (hhr.trans hrho.1) hrhopos hx⟩

/-- Negative-side radial-window containment in the exact reflected arcsine
sliver. -/
theorem supportChord_negativeRadialWindow_mem_triangle
    {α h c r R rho : ℝ} (hh : 0 < h) (hhr : h ≤ r) (hrR : r ≤ R)
    (hleft : c - 1 / 2 ≤ -Real.sqrt (R ^ 2 - h ^ 2))
    (hright : -Real.sqrt (r ^ 2 - h ^ 2) ≤ c + 1 / 2)
    (hrho : rho ∈ Icc r R) :
    Real.pi - Real.arcsin (h / rho) ∈
        Icc (Real.pi - Real.arcsin (h / r))
          (Real.pi - Real.arcsin (h / R)) ∧
      polarPoint rho (α + Real.pi - Real.arcsin (h / rho)) ∈
        supportNeedleTriangle α h c := by
  have hrpos : 0 < r := lt_of_lt_of_le hh hhr
  have hRpos : 0 < R := hrpos.trans_le hrR
  have hrhopos : 0 < rho := hrpos.trans_le hrho.1
  have hlo : h / R ≤ h / rho := by
    apply (div_le_div_iff₀ hRpos hrhopos).2
    exact mul_le_mul_of_nonneg_left hrho.2 hh.le
  have hhi : h / rho ≤ h / r := by
    apply (div_le_div_iff₀ hrhopos hrpos).2
    exact mul_le_mul_of_nonneg_left hrho.1 hh.le
  have hang : Real.pi - Real.arcsin (h / rho) ∈
      Icc (Real.pi - Real.arcsin (h / r))
        (Real.pi - Real.arcsin (h / R)) :=
    ⟨by linarith [Real.arcsin_le_arcsin hhi],
      by linarith [Real.arcsin_le_arcsin hlo]⟩
  have hsqr : r ^ 2 - h ^ 2 ≤ rho ^ 2 - h ^ 2 := by
    nlinarith [hrho.1, hrpos.le, hrhopos.le]
  have hsqR : rho ^ 2 - h ^ 2 ≤ R ^ 2 - h ^ 2 := by
    nlinarith [hrho.2, hrhopos.le, hRpos.le]
  have hx : -Real.sqrt (rho ^ 2 - h ^ 2) ∈
      Icc (c - 1 / 2) (c + 1 / 2) :=
    ⟨hleft.trans (neg_le_neg (Real.sqrt_le_sqrt hsqR)),
      (neg_le_neg (Real.sqrt_le_sqrt hsqr)).trans hright⟩
  exact ⟨hang,
    polarPoint_pi_sub_arcsin_mem_supportNeedleTriangle
      hh.le (hhr.trans hrho.1) hrhopos hx⟩

/-- A radial window beyond the nearest point and before the farther endpoint of
a unit chord fits wholly on one signed tangential side.  The statement is pure
squared-radius geometry and therefore does not require a sign assumption on
`h`. -/
theorem unitChord_radial_side_selection
    {c h r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (hinner : h ^ 2 + (unitChordNearestParameter c) ^ 2 ≤ r ^ 2)
    (houter : R ^ 2 ≤
      h ^ 2 + max ((c - 1 / 2) ^ 2) ((c + 1 / 2) ^ 2)) :
    ((c - 1 / 2 ≤ Real.sqrt (r ^ 2 - h ^ 2) ∧
        Real.sqrt (R ^ 2 - h ^ 2) ≤ c + 1 / 2) ∨
      (c - 1 / 2 ≤ -Real.sqrt (R ^ 2 - h ^ 2) ∧
        -Real.sqrt (r ^ 2 - h ^ 2) ≤ c + 1 / 2)) := by
  let a : ℝ := c - 1 / 2
  let b : ℝ := c + 1 / 2
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hR : 0 ≤ R := hr.trans hrR
  have hrr : 0 ≤ r ^ 2 - h ^ 2 := by
    have ht0 : 0 ≤ (unitChordNearestParameter c) ^ 2 := sq_nonneg _
    nlinarith
  have hRR : 0 ≤ R ^ 2 - h ^ 2 := by
    have hrsq : r ^ 2 ≤ R ^ 2 := by nlinarith
    linarith
  have hsqrtr0 : 0 ≤ Real.sqrt (r ^ 2 - h ^ 2) := Real.sqrt_nonneg _
  have hsqrtR0 : 0 ≤ Real.sqrt (R ^ 2 - h ^ 2) := Real.sqrt_nonneg _
  have hsqrtr_sq : (Real.sqrt (r ^ 2 - h ^ 2)) ^ 2 = r ^ 2 - h ^ 2 :=
    Real.sq_sqrt hrr
  have hsqrtR_sq : (Real.sqrt (R ^ 2 - h ^ 2)) ^ 2 = R ^ 2 - h ^ 2 :=
    Real.sq_sqrt hRR
  by_cases ha : 0 < a
  · have hac : 0 < c - 1 / 2 := by simpa [a] using ha
    have ht : unitChordNearestParameter c = a := by
      rw [unitChordNearestParameter, if_pos hac]
    have hb : 0 ≤ b := ha.le.trans hab
    have habsq : a ^ 2 ≤ b ^ 2 := by nlinarith
    have hmax : max ((c - 1 / 2) ^ 2) ((c + 1 / 2) ^ 2) = b ^ 2 := by
      rw [max_eq_right]
      simpa [a, b] using habsq
    left
    constructor
    · change a ≤ Real.sqrt (r ^ 2 - h ^ 2)
      rw [ht] at hinner
      nlinarith
    · change Real.sqrt (R ^ 2 - h ^ 2) ≤ b
      rw [hmax] at houter
      nlinarith
  · by_cases hb : b < 0
    · have hbc : c + 1 / 2 < 0 := by simpa [b] using hb
      have hnac : ¬ 0 < c - 1 / 2 := by simpa [a] using ha
      have ht : unitChordNearestParameter c = b := by
        rw [unitChordNearestParameter, if_neg hnac, if_pos hbc]
      have ha0 : a ≤ 0 := hab.trans hb.le
      have hbasq : b ^ 2 ≤ a ^ 2 := by nlinarith
      have hmax : max ((c - 1 / 2) ^ 2) ((c + 1 / 2) ^ 2) = a ^ 2 := by
        rw [max_eq_left]
        simpa [a, b] using hbasq
      right
      constructor
      · change a ≤ -Real.sqrt (R ^ 2 - h ^ 2)
        rw [hmax] at houter
        nlinarith
      · change -Real.sqrt (r ^ 2 - h ^ 2) ≤ b
        rw [ht] at hinner
        nlinarith
    · have ha0 : a ≤ 0 := le_of_not_gt ha
      have hb0 : 0 ≤ b := le_of_not_gt hb
      by_cases hfar : a ^ 2 ≤ b ^ 2
      · have hmax : max ((c - 1 / 2) ^ 2) ((c + 1 / 2) ^ 2) = b ^ 2 := by
          rw [max_eq_right]
          simpa [a, b] using hfar
        left
        constructor
        · change a ≤ Real.sqrt (r ^ 2 - h ^ 2)
          exact ha0.trans hsqrtr0
        · change Real.sqrt (R ^ 2 - h ^ 2) ≤ b
          rw [hmax] at houter
          nlinarith
      · have hfar' : b ^ 2 ≤ a ^ 2 := le_of_not_ge hfar
        have hmax : max ((c - 1 / 2) ^ 2) ((c + 1 / 2) ^ 2) = a ^ 2 := by
          rw [max_eq_left]
          simpa [a, b] using hfar'
        right
        constructor
        · change a ≤ -Real.sqrt (R ^ 2 - h ^ 2)
          rw [hmax] at houter
          nlinarith
        · change -Real.sqrt (r ^ 2 - h ^ 2) ≤ b
          nlinarith

/-- The squared nearest/farthest-radius hypotheses choose one of the two exact
arcsine slivers, uniformly for the whole radial window. -/
theorem supportChord_radialWindow_exists_side
    {α h c r R rho : ℝ} (hh : 0 < h) (hhr : h ≤ r) (hrR : r ≤ R)
    (hinner : h ^ 2 + (unitChordNearestParameter c) ^ 2 ≤ r ^ 2)
    (houter : R ^ 2 ≤
      h ^ 2 + max ((c - 1 / 2) ^ 2) ((c + 1 / 2) ^ 2))
    (hrho : rho ∈ Icc r R) :
    (Real.arcsin (h / rho) ∈
          Icc (Real.arcsin (h / R)) (Real.arcsin (h / r)) ∧
        polarPoint rho (α + Real.arcsin (h / rho)) ∈
          supportNeedleTriangle α h c) ∨
      (Real.pi - Real.arcsin (h / rho) ∈
          Icc (Real.pi - Real.arcsin (h / r))
            (Real.pi - Real.arcsin (h / R)) ∧
        polarPoint rho (α + Real.pi - Real.arcsin (h / rho)) ∈
          supportNeedleTriangle α h c) := by
  rcases unitChord_radial_side_selection
      (r := r) (R := R) (c := c) (h := h) (lt_of_lt_of_le hh hhr).le hrR hinner houter with
    hpos | hneg
  · exact Or.inl (supportChord_positiveRadialWindow_mem_triangle
      hh hhr hrR hpos.1 hpos.2 hrho)
  · exact Or.inr (supportChord_negativeRadialWindow_mem_triangle
      hh hhr hrR hneg.1 hneg.2 hrho)

end

end StarKakeyaLower
