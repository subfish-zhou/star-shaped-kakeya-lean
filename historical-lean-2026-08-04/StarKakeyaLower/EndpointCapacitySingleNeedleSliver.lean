import StarKakeyaLower.EndpointCapacityRadialSuperlevel

/-!
# Single-needle projective radial slivers

For one positive-height `DirectionNeedle`, this module packages either signed
arcsine branch as a projective sliver certificate.  Each certificate records:

* positive half-width;
* membership of the needle direction in the strict open paper dilation; and
* containment of the undilated quotient arc in the projected strict radial
  superlevel of the literal needle triangle.

Zero height is handled in the same module by a hybrid singleton certificate;
the arbitrary-family choice is the later step.
-/

open Set Real

namespace StarKakeyaLower

noncomputable section

/-- Paper dilation factor for `[r,R]`. -/
def radialWindowDilation (r R : ℝ) : ℝ := (R + r) / (R - r)

/-- Common half-width of both signed arcsine slivers. -/
def DirectionNeedle.sliverRadius {d : ProjectiveDirection}
    (N : DirectionNeedle d) (r R : ℝ) : ℝ :=
  (Real.arcsin (N.height / r) - Real.arcsin (N.height / R)) / 2

/-- Centre of the positive-side sliver. -/
def DirectionNeedle.positiveSliverCenter {d : ProjectiveDirection}
    (N : DirectionNeedle d) (r R : ℝ) : ℝ :=
  N.angle +
    (Real.arcsin (N.height / R) + Real.arcsin (N.height / r)) / 2

/-- Centre of the negative-side sliver. -/
def DirectionNeedle.negativeSliverCenter {d : ProjectiveDirection}
    (N : DirectionNeedle d) (r R : ℝ) : ℝ :=
  N.angle + Real.pi -
    (Real.arcsin (N.height / r) + Real.arcsin (N.height / R)) / 2

/-- The local data consumed by the arbitrary-family quotient covering theorem. -/
structure SingleNeedleSliverCertificate
    {d : ProjectiveDirection} (N : DirectionNeedle d)
    (r R r0 : ℝ) where
  center : ℝ
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  direction_mem : d ∈ quotientHybridCenteredDilate
    (radialWindowDilation r R) Real.pi center radius
  base_subset : quotientHybridCenteredArc Real.pi center radius ⊆
    polarToProjective '' radialSuperlevelPolar N.triangle r0

/-- Positive height and a genuine radial window give positive sliver width. -/
theorem DirectionNeedle.sliverRadius_pos
    {d : ProjectiveDirection} (N : DirectionNeedle d)
    {r R : ℝ} (hh : 0 < N.height) (hhr : N.height ≤ r) (hrR : r < R) :
    0 < N.sliverRadius r R := by
  have hr : 0 < r := lt_of_lt_of_le hh hhr
  have hR : 0 < R := hr.trans hrR
  have hdiv : N.height / R < N.height / r := by
    apply (div_lt_div_iff₀ hR hr).2
    nlinarith
  have hlo : -1 ≤ N.height / R := by linarith [div_pos hh hR]
  have hhi : N.height / r ≤ 1 := (div_le_one hr).2 hhr
  have ha := Real.arcsin_lt_arcsin hlo hdiv hhi
  dsimp [DirectionNeedle.sliverRadius]
  linarith

/-- The needle direction lies in the open dilation of its positive sliver. -/
theorem DirectionNeedle.direction_mem_positiveSliverDilate
    {d : ProjectiveDirection} (N : DirectionNeedle d)
    {r R : ℝ} (hh : 0 < N.height) (hhr : N.height ≤ r) (hrR : r < R) :
    d ∈ quotientHybridCenteredDilate (radialWindowDilation r R) Real.pi
      (N.positiveSliverCenter r R) (N.sliverRadius r R) := by
  let a := Real.arcsin (N.height / R)
  let b := Real.arcsin (N.height / r)
  have hradpos := N.sliverRadius_pos hh hhr hrR
  have hrad : N.sliverRadius r R ≠ 0 := ne_of_gt hradpos
  rw [quotientHybridCenteredDilate, if_neg hrad]
  have hgate := arcsin_sum_div_diff_lt
    (h := N.height) (r := r) (R := R) hh hhr hrR
  have ha0 : 0 < a := Real.arcsin_pos.2
    (div_pos hh ((lt_of_lt_of_le hh hhr).trans hrR))
  have hab : 0 < b - a := by
    simpa [a, b, DirectionNeedle.sliverRadius] using
      (show 0 < 2 * N.sliverRadius r R by nlinarith)
  have hwide : (a + b) / 2 <
      radialWindowDilation r R * ((b - a) / 2) := by
    have hgate' : (a + b) / (b - a) < radialWindowDilation r R := by
      simpa [a, b, radialWindowDilation, add_comm] using hgate
    have hraw : a + b < radialWindowDilation r R * (b - a) :=
      (div_lt_iff₀ hab).mp hgate'
    nlinarith
  unfold quotientCenteredDilate
  by_cases hsat : Real.pi ≤
      (N.positiveSliverCenter r R + radialWindowDilation r R *
          N.sliverRadius r R) -
        (N.positiveSliverCenter r R - radialWindowDilation r R *
          N.sliverRadius r R)
  · rw [quotientInterval_eq_univ_of_le hsat]
    exact mem_univ _
  · rw [quotientInterval_of_lt (lt_of_not_ge hsat)]
    refine ⟨N.angle, ?_, N.direction_eq⟩
    dsimp [DirectionNeedle.positiveSliverCenter, DirectionNeedle.sliverRadius]
    dsimp [a, b] at hwide
    constructor <;> linarith

/-- The positive base arc occurs in the strict radial superlevel of the literal
needle triangle. -/
theorem DirectionNeedle.positiveSliverBase_subset_radialSuperlevel
    {d : ProjectiveDirection} (N : DirectionNeedle d)
    {r R r0 : ℝ} (hh : 0 < N.height) (hhr : N.height ≤ r)
    (hrR : r < R)
    (hleft : N.centre - 1 / 2 ≤ Real.sqrt (r ^ 2 - N.height ^ 2))
    (hright : Real.sqrt (R ^ 2 - N.height ^ 2) ≤ N.centre + 1 / 2)
    (hr0 : r0 < r) :
    quotientHybridCenteredArc Real.pi (N.positiveSliverCenter r R)
        (N.sliverRadius r R) ⊆
      polarToProjective '' radialSuperlevelPolar N.triangle r0 := by
  let a := Real.arcsin (N.height / R)
  let b := Real.arcsin (N.height / r)
  have hr : 0 < r := lt_of_lt_of_le hh hhr
  have hR : 0 < R := hr.trans hrR
  have hradpos := N.sliverRadius_pos hh hhr hrR
  have hrad : N.sliverRadius r R ≠ 0 := ne_of_gt hradpos
  have ha0 : 0 < a := Real.arcsin_pos.2 (div_pos hh hR)
  have hbhalf : b ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hproper :
      (N.positiveSliverCenter r R + N.sliverRadius r R) -
          (N.positiveSliverCenter r R - N.sliverRadius r R) < Real.pi := by
    dsimp [DirectionNeedle.positiveSliverCenter, DirectionNeedle.sliverRadius]
    dsimp [a, b] at ha0 hbhalf ⊢
    linarith [Real.pi_pos]
  rw [quotientHybridCenteredArc, if_neg hrad, quotientCenteredArc,
    quotientInterval_of_lt hproper]
  rintro _ ⟨theta, htheta, rfl⟩
  have hphi : theta - N.angle ∈ Icc a b := by
    dsimp [DirectionNeedle.positiveSliverCenter, DirectionNeedle.sliverRadius]
      at htheta
    dsimp [a, b] at htheta ⊢
    constructor <;> linarith [htheta.1, htheta.2]
  have himage := (Set.ext_iff.1 (arcsin_div_image_Icc
    (h := N.height) (r := r) (R := R) hh hhr hrR.le)
    (theta - N.angle)).2 hphi
  rcases himage with ⟨rho, hrho, harcsin⟩
  have htri := (supportChord_positiveRadialWindow_mem_triangle
    (α := N.angle) (h := N.height) (c := N.centre)
    hh hhr hrR.le hleft hright hrho).2
  refine ⟨((theta : ℝ) : PolarAngle), ?_, rfl⟩
  refine ⟨theta, rho, rfl, hr0.trans_le hrho.1, ?_⟩
  convert htri using 1
  have hangle : theta = N.angle + Real.arcsin (N.height / rho) := by
    dsimp at harcsin
    linarith
  rw [hangle]

private theorem endpointCapacity_projectiveDirection_add_pi (alpha : ℝ) :
    ((alpha + Real.pi : ℝ) : ProjectiveDirection) =
      (alpha : ProjectiveDirection) := by
  rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]

/-- The needle direction lies in the open dilation of its negative sliver. -/
theorem DirectionNeedle.direction_mem_negativeSliverDilate
    {d : ProjectiveDirection} (N : DirectionNeedle d)
    {r R : ℝ} (hh : 0 < N.height) (hhr : N.height ≤ r) (hrR : r < R) :
    d ∈ quotientHybridCenteredDilate (radialWindowDilation r R) Real.pi
      (N.negativeSliverCenter r R) (N.sliverRadius r R) := by
  let a := Real.arcsin (N.height / r)
  let b := Real.arcsin (N.height / R)
  let g := radialWindowDilation r R
  have hrad : N.sliverRadius r R ≠ 0 :=
    ne_of_gt (N.sliverRadius_pos hh hhr hrR)
  rw [quotientHybridCenteredDilate, if_neg hrad]
  have hratio := arcsin_sum_div_diff_lt hh hhr hrR
  have hab : 0 < a - b := by
    simpa [a, b, DirectionNeedle.sliverRadius] using
      (show 0 < 2 * N.sliverRadius r R by
        nlinarith [N.sliverRadius_pos hh hhr hrR])
  have hgm : (a + b) / 2 < g * ((a - b) / 2) := by
    change (a + b) / 2 < ((R + r) / (R - r)) * ((a - b) / 2)
    have hratio' : (a + b) / (a - b) < (R + r) / (R - r) := by
      simpa [a, b] using hratio
    have hcross := (div_lt_iff₀ hab).mp hratio'
    nlinarith
  have habpos : 0 < a + b := by
    have hb : 0 < b := Real.arcsin_pos.2
      (div_pos hh ((lt_of_lt_of_le hh hhr).trans hrR))
    have ha : 0 < a := Real.arcsin_pos.2 (div_pos hh (lt_of_lt_of_le hh hhr))
    linarith
  unfold quotientCenteredDilate
  by_cases hsat : Real.pi ≤
      (N.negativeSliverCenter r R + g * N.sliverRadius r R) -
        (N.negativeSliverCenter r R - g * N.sliverRadius r R)
  · rw [quotientInterval_eq_univ_of_le hsat]
    exact mem_univ _
  · rw [quotientInterval_of_lt (lt_of_not_ge hsat)]
    refine ⟨N.angle + Real.pi, ?_, ?_⟩
    · dsimp [DirectionNeedle.negativeSliverCenter,
        DirectionNeedle.sliverRadius, a, b, g]
      constructor <;> nlinarith
    · change ((N.angle + Real.pi : ℝ) : ProjectiveDirection) = d
      rw [endpointCapacity_projectiveDirection_add_pi]
      exact N.direction_eq

/-- The negative base arc occurs in the strict radial superlevel of the literal
needle triangle. -/
theorem DirectionNeedle.negativeSliverBase_subset_radialSuperlevel
    {d : ProjectiveDirection} (N : DirectionNeedle d)
    {r R r0 : ℝ} (hh : 0 < N.height) (hhr : N.height ≤ r)
    (hrR : r < R)
    (hleft : N.centre - 1 / 2 ≤ -Real.sqrt (R ^ 2 - N.height ^ 2))
    (hright : -Real.sqrt (r ^ 2 - N.height ^ 2) ≤ N.centre + 1 / 2)
    (hr0 : r0 < r) :
    quotientHybridCenteredArc Real.pi (N.negativeSliverCenter r R)
        (N.sliverRadius r R) ⊆
      polarToProjective '' radialSuperlevelPolar N.triangle r0 := by
  let a := Real.arcsin (N.height / r)
  let b := Real.arcsin (N.height / R)
  have hr : 0 < r := lt_of_lt_of_le hh hhr
  have hR : 0 < R := hr.trans hrR
  have hradpos := N.sliverRadius_pos hh hhr hrR
  have hrad : N.sliverRadius r R ≠ 0 := ne_of_gt hradpos
  have hb0 : 0 < b := Real.arcsin_pos.2 (div_pos hh hR)
  have ha_le : a ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hproper :
      (N.negativeSliverCenter r R + N.sliverRadius r R) -
          (N.negativeSliverCenter r R - N.sliverRadius r R) < Real.pi := by
    dsimp [DirectionNeedle.negativeSliverCenter, DirectionNeedle.sliverRadius,
      a, b]
    linarith [Real.pi_pos]
  rw [quotientHybridCenteredArc, if_neg hrad, quotientCenteredArc,
    quotientInterval_of_lt hproper]
  rintro _ ⟨theta, htheta, rfl⟩
  let phi := N.angle + Real.pi - theta
  have hphi : phi ∈ Icc b a := by
    dsimp [DirectionNeedle.negativeSliverCenter, DirectionNeedle.sliverRadius,
      phi, a, b] at htheta ⊢
    constructor <;> linarith [htheta.1, htheta.2]
  have himage :
      (fun rho : ℝ => Real.arcsin (N.height / rho)) '' Icc r R = Icc b a := by
    simpa [a, b] using arcsin_div_image_Icc hh hhr hrR.le
  have hpre : phi ∈
      (fun rho : ℝ => Real.arcsin (N.height / rho)) '' Icc r R := by
    rw [himage]
    exact hphi
  rcases hpre with ⟨rho, hrho, hphi_eq⟩
  have hgeom := supportChord_negativeRadialWindow_mem_triangle
    (α := N.angle) (h := N.height) (c := N.centre)
    hh hhr hrR.le hleft hright hrho
  refine ⟨(theta : PolarAngle), ?_, polarToProjective_coe theta⟩
  refine ⟨theta, rho, rfl, hr0.trans_le hrho.1, ?_⟩
  have hangle : theta =
      N.angle + Real.pi - Real.arcsin (N.height / rho) := by
    dsimp [phi] at hphi_eq
    linarith
  rw [hangle]
  exact hgeom.2

/-- Positive-side packaged certificate. -/
def DirectionNeedle.positiveSliverCertificate
    {d : ProjectiveDirection} (N : DirectionNeedle d)
    {r R r0 : ℝ} (hh : 0 < N.height) (hhr : N.height ≤ r)
    (hrR : r < R)
    (hleft : N.centre - 1 / 2 ≤ Real.sqrt (r ^ 2 - N.height ^ 2))
    (hright : Real.sqrt (R ^ 2 - N.height ^ 2) ≤ N.centre + 1 / 2)
    (hr0 : r0 < r) : SingleNeedleSliverCertificate N r R r0 where
  center := N.positiveSliverCenter r R
  radius := N.sliverRadius r R
  radius_nonneg := (N.sliverRadius_pos hh hhr hrR).le
  direction_mem := N.direction_mem_positiveSliverDilate hh hhr hrR
  base_subset := N.positiveSliverBase_subset_radialSuperlevel
    hh hhr hrR hleft hright hr0

/-- Negative-side packaged certificate. -/
def DirectionNeedle.negativeSliverCertificate
    {d : ProjectiveDirection} (N : DirectionNeedle d)
    {r R r0 : ℝ} (hh : 0 < N.height) (hhr : N.height ≤ r)
    (hrR : r < R)
    (hleft : N.centre - 1 / 2 ≤ -Real.sqrt (R ^ 2 - N.height ^ 2))
    (hright : -Real.sqrt (r ^ 2 - N.height ^ 2) ≤ N.centre + 1 / 2)
    (hr0 : r0 < r) : SingleNeedleSliverCertificate N r R r0 where
  center := N.negativeSliverCenter r R
  radius := N.sliverRadius r R
  radius_nonneg := (N.sliverRadius_pos hh hhr hrR).le
  direction_mem := N.direction_mem_negativeSliverDilate hh hhr hrR
  base_subset := N.negativeSliverBase_subset_radialSuperlevel
    hh hhr hrR hleft hright hr0

/-- Zero-height certificate: the hybrid owner is the singleton needle direction,
represented at radius `R` on whichever signed side reaches the outer endpoint. -/
def DirectionNeedle.zeroHeightSliverCertificate
    {d : ProjectiveDirection} (N : DirectionNeedle d)
    {r R r0 : ℝ} (hheight : N.height = 0) (hr : 0 < r) (hrR : r < R)
    (hinner : N.nearestRadiusSq ≤ r ^ 2)
    (houter : R ^ 2 ≤ N.maxEndpointRadiusSq)
    (hr0 : r0 < r) : SingleNeedleSliverCertificate N r R r0 := by
  have hR : 0 < R := hr.trans hrR
  have hside := unitChord_radial_side_selection
    (c := N.centre) (h := N.height) (r := r) (R := R)
    hr.le hrR.le (by
      simpa [DirectionNeedle.nearestRadiusSq] using hinner) (by
      simpa [DirectionNeedle.maxEndpointRadiusSq] using houter)
  have hpoint :
      polarPoint R N.angle ∈ N.triangle ∨
        polarPoint R (N.angle + Real.pi) ∈ N.triangle := by
    rcases hside with hpos | hneg
    · left
      have hx : Real.sqrt (R ^ 2 - N.height ^ 2) ∈
          Icc (N.centre - 1 / 2) (N.centre + 1 / 2) := by
        constructor
        · calc
            N.centre - 1 / 2 ≤ Real.sqrt (r ^ 2 - N.height ^ 2) := hpos.1
            _ ≤ Real.sqrt (R ^ 2 - N.height ^ 2) := by
              apply Real.sqrt_le_sqrt
              nlinarith
        · exact hpos.2
      have hp := polarPoint_arcsin_mem_supportNeedleTriangle
        (α := N.angle) (h := N.height) (c := N.centre) (rho := R)
        (by rw [hheight]) (by rw [hheight]; exact hR.le) hR hx
      simpa [DirectionNeedle.triangle, hheight] using hp
    · right
      have hx : -Real.sqrt (R ^ 2 - N.height ^ 2) ∈
          Icc (N.centre - 1 / 2) (N.centre + 1 / 2) := by
        refine ⟨hneg.1, ?_⟩
        have hs : Real.sqrt (r ^ 2 - N.height ^ 2) ≤
            Real.sqrt (R ^ 2 - N.height ^ 2) := by
          apply Real.sqrt_le_sqrt
          nlinarith
        exact (neg_le_neg hs).trans hneg.2
      have hp := polarPoint_pi_sub_arcsin_mem_supportNeedleTriangle
        (α := N.angle) (h := N.height) (c := N.centre) (rho := R)
        (by rw [hheight]) (by rw [hheight]; exact hR.le) hR hx
      simpa [DirectionNeedle.triangle, hheight, sub_eq_add_neg, add_assoc] using hp
  refine
    { center := N.angle
      radius := 0
      radius_nonneg := le_rfl
      direction_mem := ?_
      base_subset := ?_ }
  · rw [quotientHybridCenteredDilate, if_pos rfl, Set.mem_singleton_iff]
    exact N.direction_eq.symm
  · rw [quotientHybridCenteredArc, if_pos rfl]
    rintro q hq
    rw [Set.mem_singleton_iff] at hq
    subst q
    rcases hpoint with hp | hp
    · refine ⟨(N.angle : PolarAngle), ?_, polarToProjective_coe N.angle⟩
      exact ⟨N.angle, R, rfl, hr0.trans hrR, hp⟩
    · refine ⟨((N.angle + Real.pi : ℝ) : PolarAngle), ?_, ?_⟩
      · exact ⟨N.angle + Real.pi, R, rfl, hr0.trans hrR, hp⟩
      · rw [polarToProjective_coe, AddCircle.coe_add, AddCircle.coe_period,
          add_zero]

end

end StarKakeyaLower
