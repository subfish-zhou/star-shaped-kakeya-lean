import StarKakeyaLower.LiLemma23

open Set MeasureTheory Real
open scoped ENNReal

namespace StarKakeyaLower

noncomputable section

/-- The fixed-parameter form of Li 2.5 used by the stronger certificate. -/
def StrongLiLemma25OuterStatement : Prop :=
  ∀ (A : Set ProjectiveDirection)
    (N : (d : ProjectiveDirection) → DirectionNeedle d) (s₀ m : ℝ),
    0 ≤ s₀ → 0 ≤ m →
    ENNReal.ofReal m ≤ directionOuterMass A →
    (∀ d ∈ A, |(N d).height| ≤ strongA) →
    ENNReal.ofReal s₀ ≤ volume.toOuterMeasure
      (directionTriangleUnion N A ∩ originOpenDisk strongR₀) →
    ENNReal.ofReal
      (m / 4 * liF strongR₀ +
        (1 - liF strongR₀ / (2 * strongR₀ ^ 2)) * s₀) ≤
      volume.toOuterMeasure (directionTriangleUnion N A)

/-- Carathéodory summation of the strong Li-2.3 payment over one fixed
finite or countable selection. -/
theorem liSelectedExteriorUnion_area_strong
    {ι : Type*} [Countable ι] (d : ι → ProjectiveDirection)
    (N : (i : ι) → DirectionNeedle (d i))
    (hheightA : ∀ i, |(N i).height| ≤ strongA)
    (hsep : Pairwise (fun i j =>
      Real.arcsin (|(N i).height| / strongR₀) +
        Real.arcsin (|(N j).height| / strongR₀) ≤ dist (d i) (d j))) :
    (∑' i, ENNReal.ofReal
        (liF strongR₀ * Real.arcsin (|(N i).height| / strongR₀))) ≤
      volume (liSelectedExteriorUnion d N strongR₀) := by
  have hr : 0 < strongR₀ := lt_of_lt_of_le (by norm_num)
    strongParameterDomain.r₀_ge_three_twentieths
  have hheight : ∀ i, |(N i).height| < strongR₀ := by
    intro i
    exact (hheightA i).trans_lt (by norm_num [strongA, strongR₀])
  have hpair := pairwise_disjoint_liExteriorInterior d N hr
    (fun i => (hheight i).le) hsep
  rw [liSelectedExteriorUnion, MeasureTheory.measure_iUnion hpair
    (fun i => measurableSet_liExteriorInterior (N i) strongR₀)]
  apply ENNReal.tsum_le_tsum
  intro i
  change ENNReal.ofReal
      (liF strongR₀ * Real.arcsin (|(N i).height| / strongR₀)) ≤
    (volume.prod volume).toOuterMeasure (interior (liExterior (N i) strongR₀))
  rw [outerMeasure_interior_liExterior_eq]
  exact liLemma23_strong (N i) (hheightA i)

/-- Elementary ENNReal bookkeeping used after either actual fixed-selection
outcome.  Infinite ambient area, infinite deletion cost, and finite costs are
all handled without applying `toReal` to `⊤`. -/
theorem strongLi25_epsilon_from_geometry
    {s₀ m q s : ℝ} {B R S M : ENNReal}
    (hs₀ : 0 ≤ s₀) (hm : 0 ≤ m) (hq : 0 < q) (hs : 0 < s)
    (hqs : q ≤ s)
    (hinner : ENNReal.ofReal s₀ + S ≤ M)
    (hcover : ENNReal.ofReal m ≤ R + B)
    (hpay : ENNReal.ofReal q * B ≤ S)
    (hfan : ENNReal.ofReal s * R + S ≤ M) :
    ENNReal.ofReal (q * m + (1 - q / s) * s₀) ≤ M := by
  by_cases hM : M = ⊤
  · rw [hM]
    exact le_top
  have hS : S ≠ ⊤ := ne_top_of_le_ne_top hM (hinner.trans' (le_add_left le_rfl))
  have hqtop : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.2 hq).ne'
  have hB : B ≠ ⊤ := by
    intro h
    have : S = ⊤ := by
      apply top_unique
      simpa [h, ENNReal.mul_top, hqtop] using hpay
    exact hS this
  have hsTop : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.2 hs).ne'
  have hR : R ≠ ⊤ := by
    intro h
    have : M = ⊤ := by
      apply top_unique
      have : ENNReal.ofReal s * R + S = ⊤ := by
        simp [h, ENNReal.mul_top, hsTop]
      simpa [this] using hfan
    exact hM this
  have hinnerR := (ENNReal.toReal_le_toReal
    (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hS⟩) hM).2 hinner
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hS,
    ENNReal.toReal_ofReal hs₀] at hinnerR
  have hcoverR := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
    (ENNReal.add_ne_top.mpr ⟨hR, hB⟩)).2 hcover
  rw [ENNReal.toReal_ofReal hm, ENNReal.toReal_add hR hB] at hcoverR
  have hpayR := (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB) hS).2 hpay
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq.le] at hpayR
  have hfanR := (ENNReal.toReal_le_toReal
    (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hR, hS⟩) hM).2 hfan
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hR) hS,
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hs.le] at hfanR
  have hreal : q * m + (1 - q / s) * s₀ ≤ M.toReal := by
    have hid : s * (q * m + (1 - q / s) * s₀) =
        q * s * m + (s - q) * s₀ := by
      field_simp [ne_of_gt hs]
    by_cases hcase : s₀ ≤ s * R.toReal
    · have hnonneg : 0 ≤ s - q := sub_nonneg.mpr hqs
      have hc := mul_le_mul_of_nonneg_left hcoverR (mul_nonneg hq.le hs.le)
      have hp := mul_le_mul_of_nonneg_left hpayR hs.le
      have hx := mul_le_mul_of_nonneg_left hcase hnonneg
      have hf := mul_le_mul_of_nonneg_left hfanR hs.le
      nlinarith
    · have hcase' : s * R.toReal < s₀ := lt_of_not_ge hcase
      have hc := mul_le_mul_of_nonneg_left hcoverR (mul_nonneg hq.le hs.le)
      have hp := mul_le_mul_of_nonneg_left hpayR hs.le
      have hx := mul_lt_mul_of_pos_left hcase' hq
      have hi := mul_le_mul_of_nonneg_left hinnerR hs.le
      nlinarith
  exact (ENNReal.ofReal_le_ofReal hreal).trans (ENNReal.ofReal_toReal hM).le

/-- A positive polar radius has the projective direction represented by its
polar angle.  The proof first moves the angle to the canonical complex-argument
chart; this avoids any accidental assertion that `Complex.arg` is literally
the identity outside `(-π,π]`. -/
theorem rayDirection_coordinatePolarPoint {s θ : ℝ} (hs : 0 < s) :
    rayDirection 0 (coordinatePlaneEquiv (polarPoint s θ)) =
      directionQuotient θ := by
  let u : Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) :=
    AddCircle.equivIoc (2 * Real.pi) (-Real.pi) (θ : PolarAngle)
  have hucoe : (((u : ℝ) : PolarAngle)) = (θ : PolarAngle) :=
    AddCircle.coe_equivIoc
  have huIoc : (u : ℝ) ∈ Ioc (-Real.pi) Real.pi := by
    exact ⟨u.property.1, by linarith [u.property.2]⟩
  have hp : polarPoint s θ = polarPoint s (u : ℝ) :=
    polarPoint_eq_of_polar_coe_eq hucoe.symm
  have hv : coordinatePlaneEquiv (polarPoint s (u : ℝ)) =
      s • angleVector (u : ℝ) := by
    ext i
    fin_cases i <;>
      simp [polarPoint, scaleCoordinatePlane, unitDirection, angleVector]
  have ha : vectorAngle (angleVector (u : ℝ)) = (u : ℝ) := by
    change Complex.arg
      ({ re := Real.cos (u : ℝ), im := Real.sin (u : ℝ) } : ℂ) = (u : ℝ)
    have heq : ({ re := Real.cos (u : ℝ), im := Real.sin (u : ℝ) } : ℂ) =
        Complex.cos ((u : ℝ) : ℂ) + Complex.sin ((u : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;>
        simp [Complex.sin_ofReal_re, Complex.sin_ofReal_im,
          Complex.cos_ofReal_re, Complex.cos_ofReal_im]
    rw [heq]
    exact Complex.arg_cos_add_sin_mul_I huIoc
  rw [hp, rayDirection, sub_zero, hv, vectorAngle_pos_smul hs, ha]
  exact congrArg polarToProjective hucoe

/-- The inverse-sine rescaling profile used by fixed deletion is concave on the
first quadrant. -/
theorem strong_concaveOn_arcsin_mul_sin {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) :
    ConcaveOn ℝ (Icc (0 : ℝ) (Real.pi / 2))
      (fun u => Real.arcsin (m * Real.sin u)) := by
  let f : ℝ → ℝ := fun u => Real.arcsin (m * Real.sin u)
  let g : ℝ → ℝ := fun u =>
    m * Real.cos u / Real.sqrt (1 - (m * Real.sin u) ^ 2)
  have harg (u : ℝ) : |m * Real.sin u| < 1 := by
    calc
      |m * Real.sin u| = m * |Real.sin u| := by rw [abs_mul, abs_of_pos hm0]
      _ ≤ m * 1 := mul_le_mul_of_nonneg_left (abs_sin_le_one u) hm0.le
      _ < 1 := by simpa using hm1
  have hD (u : ℝ) : 0 < 1 - (m * Real.sin u) ^ 2 := by
    have h := harg u
    rw [abs_lt] at h
    nlinarith [sq_nonneg (m * Real.sin u - 1), sq_nonneg (m * Real.sin u + 1)]
  have hfderiv (u : ℝ) : HasDerivAt f (g u) u := by
    have hn1 : m * Real.sin u ≠ -1 := ne_of_gt (abs_lt.mp (harg u)).1
    have hp1 : m * Real.sin u ≠ 1 := ne_of_lt (abs_lt.mp (harg u)).2
    dsimp [f, g]
    convert (Real.hasDerivAt_arcsin hn1 hp1).comp u
      ((hasDerivAt_const u m).mul (Real.hasDerivAt_sin u)) using 1 <;> ring
  have hfg : deriv f = g := funext fun u => (hfderiv u).deriv
  have hgderiv (u : ℝ) : HasDerivAt g
      (m * (m ^ 2 - 1) * Real.sin u /
        (Real.sqrt (1 - (m * Real.sin u) ^ 2)) ^ 3) u := by
    let D : ℝ → ℝ := fun x => 1 - (m * Real.sin x) ^ 2
    have hD' : HasDerivAt D
        (-2 * m ^ 2 * Real.sin u * Real.cos u) u := by
      dsimp [D]
      convert (hasDerivAt_const u 1).sub
        (((Real.hasDerivAt_sin u).const_mul m).pow 2) using 1 <;>
        ring_nf
    have hsqrt : HasDerivAt (fun x => Real.sqrt (D x))
        ((-2 * m ^ 2 * Real.sin u * Real.cos u) /
          (2 * Real.sqrt (D u))) u := by
      convert (Real.hasDerivAt_sqrt
        (ne_of_gt (by simpa [D] using hD u))).comp u hD' using 1 <;> ring
    have hnum : HasDerivAt (fun x => m * Real.cos x)
        (-m * Real.sin u) u := by
      convert (hasDerivAt_const u m).mul (Real.hasDerivAt_cos u) using 1 <;> ring
    have hsne : Real.sqrt (D u) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by simpa [D] using hD u))
    have hq := hnum.div hsqrt hsne
    have hs2 : (Real.sqrt (D u)) ^ 2 = D u := Real.sq_sqrt (hD u).le
    dsimp [g]
    convert hq using 1
    dsimp [D] at hs2 ⊢
    let t := Real.sqrt (1 - (m * Real.sin u) ^ 2)
    have ht : t ≠ 0 := by simpa [t, D] using hsne
    have ht2 : t ^ 2 = 1 - (m * Real.sin u) ^ 2 := by simpa [t] using hs2
    change m * (m ^ 2 - 1) * Real.sin u / t ^ 3 =
      (-m * Real.sin u * t - m * Real.cos u *
        (-2 * m ^ 2 * Real.sin u * Real.cos u / (2 * t))) / t ^ 2
    field_simp [ht]
    rw [ht2]
    have hcos : Real.cos u ^ 2 = 1 - Real.sin u ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq u]
    rw [hcos]
    ring
  apply concaveOn_of_deriv2_nonpos (convex_Icc (0 : ℝ) (Real.pi / 2))
  · exact Real.continuous_arcsin.comp
      (continuous_const.mul Real.continuous_sin) |>.continuousOn
  · intro u _
    exact (hfderiv u).differentiableAt.differentiableWithinAt
  · rw [hfg]
    intro u _
    exact (hgderiv u).differentiableAt.differentiableWithinAt
  · intro u hu
    change deriv (deriv f) u ≤ 0
    rw [hfg, (hgderiv u).deriv]
    have hsin : 0 ≤ Real.sin u := Real.sin_nonneg_of_nonneg_of_le_pi
      (interior_subset hu).1 (by linarith [interior_subset hu |>.2, Real.pi_pos])
    have hcoef : m ^ 2 - 1 ≤ 0 := by nlinarith
    have hmsin : 0 ≤ m * Real.sin u := mul_nonneg hm0.le hsin
    exact div_nonpos_of_nonpos_of_nonneg
      (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hmsin hcoef])
      (by positivity)

/-- The chord from `0` to `π/2` in the concave inverse-sine profile is exactly
Li's exterior factor. -/
theorem li25ExteriorFactor_mul_deletionWeight_le
    {eps r δ : ℝ} (heps0 : 0 < eps) (heps1 : eps < 1)
    (hr : 0 < r) (hδ0 : 0 ≤ δ) (hδ : δ ≤ (1 - eps) * r) :
    li25ExteriorFactor eps * Real.arcsin (δ / ((1 - eps) * r)) ≤
      Real.arcsin (δ / r) := by
  let m := 1 - eps
  let u := Real.arcsin (δ / (m * r))
  have hm0 : 0 < m := by dsimp [m]; linarith
  have hm1 : m < 1 := by dsimp [m]; linarith
  have harg0 : 0 ≤ δ / (m * r) := div_nonneg hδ0 (mul_pos hm0 hr).le
  have harg1 : δ / (m * r) ≤ 1 := (div_le_one (mul_pos hm0 hr)).2 hδ
  have hu0 : 0 ≤ u := Real.arcsin_nonneg.2 harg0
  have hu1 : u ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hsin : Real.sin u = δ / (m * r) := by
    dsimp [u]
    exact Real.sin_arcsin (by linarith) harg1
  have hconc := strong_concaveOn_arcsin_mul_sin hm0 hm1
  let a := 2 * u / Real.pi
  let b := 1 - a
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    apply (div_le_one Real.pi_pos).2
    linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hab : a + b = 1 := by dsimp [b]; ring
  have hchord := hconc.2 ⟨by positivity, le_rfl⟩
    (Set.left_mem_Icc.mpr (by positivity : (0 : ℝ) ≤ Real.pi / 2)) ha hb hab
  have hzero : Real.arcsin (m * Real.sin 0) = 0 := by simp
  have hend : Real.arcsin (m * Real.sin (Real.pi / 2)) = Real.arcsin m := by simp
  have hmδ : m * Real.sin u = δ / r := by
    rw [hsin]
    field_simp [ne_of_gt hm0, ne_of_gt hr]
  dsimp only at hchord
  rw [hzero, hend, smul_eq_mul, smul_eq_mul, mul_zero, add_zero] at hchord
  dsimp [li25ExteriorFactor]
  change 2 * Real.arcsin m / Real.pi * u ≤ Real.arcsin (δ / r)
  rw [← hmδ]
  convert hchord using 1 <;> dsimp [a, b] <;>
    field_simp [ne_of_gt Real.pi_pos] <;> ring

/-- Subtraction bookkeeping for the residual angular mass. -/
theorem ofReal_sub_le_of_le_add_ofReal {m b : ℝ} {R : ENNReal}
    (hm : 0 ≤ m) (hb : 0 ≤ b)
    (hcover : ENNReal.ofReal m ≤ R + ENNReal.ofReal b) :
    ENNReal.ofReal (m - b) ≤ R := by
  by_cases hR : R = ⊤
  · rw [hR]
    exact le_top
  have hadd : R + ENNReal.ofReal b ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hR, ENNReal.ofReal_ne_top⟩
  have hreal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hadd).2 hcover
  rw [ENNReal.toReal_ofReal hm, ENNReal.toReal_add hR ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hb] at hreal
  rw [← ENNReal.ofReal_toReal hR]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- The concrete oriented residual sector is contained in the residual ray fan. -/
theorem polarSector_liResidualAngles_subset_liResidualRayFan
    (N : (d : ProjectiveDirection) → DirectionNeedle d)
    (R : Set ProjectiveDirection) {r : ℝ} (hr : 0 ≤ r) :
    polarSector 0 r (liResidualAngles N R) ⊆ liResidualRayFan R := by
  rintro z ⟨s, hs, θ, hθ, rfl⟩
  by_cases hs0 : s = 0
  · left
    subst s
    simp [polarPoint, scaleCoordinatePlane]
  · right
    refine ⟨?_, ?_⟩
    · intro hz
      have hp0 : polarPoint s θ = 0 := by
        apply coordinatePlaneEquiv.injective
        simpa using hz
      have hx := congrArg Prod.fst hp0
      have hy := congrArg Prod.snd hp0
      simp [polarPoint, scaleCoordinatePlane, unitDirection] at hx hy
      rcases hx with hx | hx
      · exact hs0 hx
      rcases hy with hy | hy
      · exact hs0 hy
      have htrig := Real.sin_sq_add_cos_sq θ
      nlinarith
    · rcases hθ.1 with ⟨d, hd, hθd⟩
      have hp := congrArg polarToProjective hθd
      have hdir : directionQuotient θ = d := by
        split at hp
        · simpa only [polarToProjective_coe, (N d).direction_eq] using hp
        · simpa only [map_add, polarToProjective_coe, AddCircle.coe_period,
            add_zero, (N d).direction_eq] using hp
      simp only [zero_add]
      rw [rayDirection_coordinatePolarPoint
        (lt_of_le_of_ne hs.1 (Ne.symm hs0)), hdir]
      exact hd

/-- The exact strong-parameter Li-2.5 contract consumed by universal Case I. -/
def StrongLiLemma25Theorem : Prop :=
  ∀ (N : (d : ProjectiveDirection) → DirectionNeedle d),
    (∀ d, |(N d).height| ≤ strongA) →
    ENNReal.ofReal (Real.pi * strongP * strongILower) ≤
      volume.toOuterMeasure
        (directionTriangleUnion N Set.univ ∩ originOpenDisk strongR₀) →
    ENNReal.ofReal
      (Real.pi / 4 * liF strongR₀ +
        (1 - liF strongR₀ / (2 * strongR₀ ^ 2)) *
          (Real.pi * strongP * strongILower)) ≤
      volume.toOuterMeasure (directionTriangleUnion N Set.univ)

/-- A checked fixed selection at one sufficiently small epsilon gives the
factor-weighted strong Li bound.  Both branches use the existing certificate
constructors; `max π b` lets the same construction also cover deletion cost
larger than the circle mass. -/
theorem strongLiLemma25_epsilon
    (N : (d : ProjectiveDirection) → DirectionNeedle d)
    (hheightA : ∀ d, |(N d).height| ≤ strongA)
    (hinner : ENNReal.ofReal (Real.pi * strongP * strongILower) ≤
      volume.toOuterMeasure
        (directionTriangleUnion N Set.univ ∩ originOpenDisk strongR₀))
    (eps : ℝ) (heps0 : 0 < eps) (hepshalf : eps ≤ 1 / 2) :
    ENNReal.ofReal
      (Real.pi / 4 * (liF strongR₀ * li25ExteriorFactor eps) +
        (1 - liF strongR₀ * li25ExteriorFactor eps /
          (2 * strongR₀ ^ 2)) * (Real.pi * strongP * strongILower)) ≤
      volume.toOuterMeasure (directionTriangleUnion N Set.univ) := by
  let height := li25Height N
  let H := li25DeletionWeight N eps strongR₀
  let q : ℝ := 1 - eps
  have heps1 : eps < 1 := hepshalf.trans_lt (by norm_num)
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hr0 := strongParameterDomain.r₀_ge_three_twentieths
  have hr1 := strongParameterDomain.r₀_lt_half.le
  have hr : 0 < strongR₀ := lt_of_lt_of_le (by norm_num) hr0
  have hbound : ∀ d ∈ (Set.univ : Set ProjectiveDirection), height d ≤ strongA := by
    intro d _
    exact hheightA d
  have hheight : ∀ d, height d = |(N d).height| := fun _ => rfl
  have hscaled_all : ∀ d, height d ≤ q * strongR₀ := by
    intro d
    have hd := hheightA d
    dsimp [height, li25Height, q]
    norm_num [strongA, strongR₀] at hd ⊢
    linarith
  have hH0_all : ∀ d, 0 ≤ H d := by
    intro d
    dsimp [H, li25DeletionWeight, caseIIPaperWeight]
    exact Real.arcsin_nonneg.2
      (div_nonneg (abs_nonneg _) (mul_pos hq0 hr).le)

  have hraw_all : ∀ d,
      li25ExteriorFactor eps * H d ≤
        Real.arcsin (|(N d).height| / strongR₀) := by
    intro d
    apply li25ExteriorFactor_mul_deletionWeight_le heps0 heps1 hr (abs_nonneg _)
    simpa [height, q] using hscaled_all d
  have huniv : ENNReal.ofReal Real.pi ≤
      directionAngleOuter (Set.univ : Set ProjectiveDirection) := by
    rw [← directionOuterMeasure_eq_directionAngleOuter]
    exact directionOuterMass_univ
  cases li25FixedSelectionOutcome N Set.univ eps strongR₀ strongA hbound with
  | finite F =>
      have hpos : ∀ i, 0 < height (F.selected i) := by
        intro i
        have hex := exists_chooseAbove hq0 hq1
          (fixedGreedyRemaining_subset height H q Set.univ i) hbound
          (F.positive_before i)
        rw [F.selected_eq i, fixedGreedySelected, chooseAbove, dif_pos hex]
        exact (mul_pos hq0 (F.positive_before i)).trans
          (Classical.choose_spec hex).2
      have hscaled : ∀ i, height (F.selected i) < q * strongR₀ := by
        intro i
        exact (hheightA _).trans_lt (by
          dsimp [q]
          norm_num [strongA, strongR₀]
          linarith)
      have hHeq : ∀ i, H (F.selected i) =
          Real.arcsin (height (F.selected i) / (q * strongR₀)) := fun _ => rfl
      let b := ∑ i : Fin F.N, 4 * H (F.selected i)
      let mc := max Real.pi b
      have hb0 : 0 ≤ b := Finset.sum_nonneg fun i _ =>
        mul_nonneg (by norm_num) (hH0_all _)
      have hB : (∑' i : Fin F.N, ENNReal.ofReal (4 * H (F.selected i))) =
          ENNReal.ofReal b := by
        rw [tsum_fintype, ENNReal.ofReal_sum_of_nonneg]
        intro i _
        exact mul_nonneg (by norm_num) (hH0_all _)
      have hcover : ENNReal.ofReal Real.pi ≤
          directionAngleOuter F.residual + ENNReal.ofReal b := by
        rw [← hB]
        exact huniv.trans (F.initial_directionAngleOuter_le_residual_add_cost
          (fun i => hH0_all _))
      let Θ := liResidualAngles N F.residual
      have hzero : ∀ d ∈ F.residual, height d = 0 :=
        F.residual_height_zero (fun _ => abs_nonneg _) hbound
      have hres : ENNReal.ofReal (mc - b) ≤ angleSetOuter Θ := by
        by_cases hbp : b ≤ Real.pi
        · rw [show mc = Real.pi by simp [mc, hbp]]
          exact (ofReal_sub_le_of_le_add_ofReal Real.pi_pos.le hb0 hcover).trans
            (directionAngleOuter_le_angleSetOuter_liResidualAngles N F.residual)
        · have hpb : Real.pi ≤ b := le_of_not_ge hbp
          rw [show mc = b by simp [mc, hpb], sub_self, ENNReal.ofReal_zero]
          exact bot_le
      have hselectedArea := liSelectedExteriorUnion_area_strong F.selected
        (fun i => N (F.selected i)) (fun i => hheightA _)
        (fun i j hij => by
          rcases lt_or_gt_of_ne hij with hij | hji
          · simpa [hheight] using (F.triangle_shadow_sum_lt_distance hq0 hq1
              hbound hr hpos hscaled hHeq hij).le
          · simpa [hheight, dist_comm, add_comm] using
              (F.triangle_shadow_sum_lt_distance hq0 hq1 hbound hr hpos hscaled hHeq hji).le)
      have hfacpos : 0 < li25ExteriorFactor eps := by
        unfold li25ExteriorFactor
        exact div_pos (mul_pos (by norm_num) (Real.arcsin_pos.2 (by linarith)))
          Real.pi_pos
      have hfac0 : 0 ≤ li25ExteriorFactor eps := hfacpos.le
      have harea : ENNReal.ofReal
          (liF strongR₀ * li25ExteriorFactor eps / 4 * b) ≤
          volume (F.liSelectedExterior N strongR₀) := by
        have heq : liF strongR₀ * li25ExteriorFactor eps / 4 * b =
            ∑ i : Fin F.N, liF strongR₀ *
              (li25ExteriorFactor eps * H (F.selected i)) := by
          dsimp [b]; rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _; ring
        rw [heq, ENNReal.ofReal_sum_of_nonneg]
        · simpa only [tsum_fintype] using
            (ENNReal.tsum_le_tsum (fun i => ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_left (hraw_all _) (by unfold liF; positivity)))).trans
              hselectedArea
        · intro i _
          exact mul_nonneg (by unfold liF; positivity)
            (mul_nonneg hfac0 (hH0_all _))
      have hsectorRay := polarSector_liResidualAngles_subset_liResidualRayFan
        N F.residual hr.le
      have hsectorE := polarSector_liResidualAngles_subset_directionTriangleUnion
        N Set.univ F.residual hr.le hr1 F.residual_subset_initial
        (fun d hd => by
          apply abs_eq_zero.mp
          simpa [height, li25Height] using hzero d hd)
      have hdisj := F.disjoint_liResidualRayFan_liSelectedExterior N hr hq0 hq1
        hbound hheight hpos hscaled hHeq
      let C : LiLemma25GreedyCertificate Set.univ N strongR₀ mc :=
        { epsilon := eps
          epsilon_pos := heps0
          epsilon_lt_one := heps1
          deletionCost := b
          deletionCost_nonneg := hb0
          deletionCost_le_mass := le_max_right _ _
          selectedExterior := F.liSelectedExterior N strongR₀
          residualFan := polarSector 0 strongR₀ Θ
          selectedExterior_measurable := measurableSet_liSelectedExteriorUnion _ _ _
          selectedExterior_subset := by
            intro z hz
            simp only [FiniteFixedSelection.liSelectedExterior,
              liSelectedExteriorUnion, mem_iUnion] at hz
            obtain ⟨i, hzi⟩ := hz
            exact Set.mem_iUnion_of_mem
              (⟨F.selected i, Set.mem_univ _⟩ : (Set.univ : Set ProjectiveDirection))
              (diff_subset (interior_subset hzi))
          selectedExterior_outside := by
            intro z hz
            simp only [FiniteFixedSelection.liSelectedExterior,
              liSelectedExteriorUnion, mem_iUnion] at hz
            obtain ⟨i, hzi⟩ := hz
            exact (interior_subset hzi).2
          residualFan_subset := hsectorE
          residualFan_disjoint_selected := hdisj.mono hsectorRay Subset.rfl
          selectedExteriorArea := harea
          residualFanArea := by
            have hc : 0 ≤ strongR₀ ^ 2 / 2 := by positivity
            rw [ENNReal.ofReal_mul hc]
            exact (mul_le_mul_left' hres _).trans
              (polarSector_outerMeasure_ge 0 hr.le Θ) }
      have hmc0 : 0 ≤ mc := Real.pi_pos.le.trans (le_max_left _ _)
      have hout := liLemma25OuterStatement_epsilon Set.univ N strongR₀
        (Real.pi * strongP * strongILower) mc hr0 hr1
        (by
          exact mul_nonneg
            (mul_nonneg Real.pi_pos.le (by norm_num [strongP]))
            (by norm_num [strongILower])) hmc0 hinner C
      dsimp [C] at hout
      apply (ENNReal.ofReal_le_ofReal ?_).trans hout
      have hcoef : 0 ≤ liF strongR₀ * li25ExteriorFactor eps := by
        exact mul_nonneg (by unfold liF; positivity)
          (by unfold li25ExteriorFactor; positivity)
      have hpimc : Real.pi ≤ mc := le_max_left _ _
      nlinarith
  | infinite hp =>
      let G := infiniteGreedyData hq0 hq1 hbound hp
        (fun n => directionAngleOuter_fixedDeletionBall_le (hH0_all _))
      have hpos : ∀ i, 0 < height (G.selected i) := by
        intro i
        have hex := exists_chooseAbove hq0 hq1
          (fixedGreedyRemaining_subset height H q Set.univ i) hbound (hp i)
        change 0 < height (fixedGreedySelected height H q Set.univ i)
        rw [fixedGreedySelected, chooseAbove, dif_pos hex]
        exact (mul_pos hq0 (hp i)).trans (Classical.choose_spec hex).2
      have hscaled : ∀ i, height (G.selected i) < G.multiplier * strongR₀ := by
        intro i
        change height (G.selected i) < q * strongR₀
        exact (hheightA _).trans_lt (by
          dsimp [q]
          norm_num [strongA, strongR₀]
          linarith)
      have hHeq : ∀ i, H (G.selected i) =
          Real.arcsin (height (G.selected i) / (G.multiplier * strongR₀)) := fun _ => rfl
      let B : ENNReal := ∑' i, ENNReal.ofReal (4 * H (G.selected i))
      by_cases hBtop : B = ⊤
      · have hfacpos : 0 < li25ExteriorFactor eps := by
          unfold li25ExteriorFactor
          exact div_pos (mul_pos (by norm_num) (Real.arcsin_pos.2 (by linarith)))
            Real.pi_pos
        have hfpos : 0 < liF strongR₀ := by
          norm_num [liF, strongR₀]
        have hrawtop : (∑' i, ENNReal.ofReal
            (liF strongR₀ * Real.arcsin (|(N (G.selected i)).height| / strongR₀))) = ⊤ := by
          apply top_unique
          calc
            ⊤ = ENNReal.ofReal (liF strongR₀ * li25ExteriorFactor eps / 4) * B := by
              rw [hBtop, ENNReal.mul_top]
              exact (ENNReal.ofReal_pos.2 (div_pos
                (mul_pos hfpos hfacpos) (by norm_num : (0 : ℝ) < 4))).ne'
            _ = ∑' i, ENNReal.ofReal (liF strongR₀ * li25ExteriorFactor eps / 4) *
                ENNReal.ofReal (4 * H (G.selected i)) := by
              rw [ENNReal.tsum_mul_left]
            _ ≤ ∑' i, ENNReal.ofReal
                (liF strongR₀ * Real.arcsin (|(N (G.selected i)).height| / strongR₀)) := by
              apply ENNReal.tsum_le_tsum
              intro i
              rw [← ENNReal.ofReal_mul (by
                exact div_nonneg
                  (mul_nonneg (by unfold liF; positivity) hfacpos.le)
                  (by norm_num) :
                0 ≤ liF strongR₀ * li25ExteriorFactor eps / 4)]
              apply ENNReal.ofReal_le_ofReal
              have hh := hraw_all (G.selected i)
              have hf : 0 ≤ liF strongR₀ := by unfold liF; positivity
              nlinarith
        have hselectedArea := liSelectedExteriorUnion_area_strong G.selected
          (fun i => N (G.selected i)) (fun i => hheightA _)
          (fun i j hij => by
            rcases lt_or_gt_of_ne hij with hij | hji
            · simpa [hheight] using
                (G.future_triangle_shadow_sum_lt_distance hr hpos hscaled hHeq hij).le
            · simpa [hheight, dist_comm, add_comm] using
                (G.future_triangle_shadow_sum_lt_distance hr hpos hscaled hHeq hji).le)
        have htop : volume (G.liSelectedExterior N strongR₀) = ⊤ := by
          apply top_unique
          rw [← hrawtop]
          exact hselectedArea
        have hsubset : G.liSelectedExterior N strongR₀ ⊆
            directionTriangleUnion N Set.univ := by
          intro z hz
          simp only [FixedDeletionGreedyData.liSelectedExterior,
            liSelectedExteriorUnion, mem_iUnion] at hz
          obtain ⟨i, hzi⟩ := hz
          exact Set.mem_iUnion_of_mem
            (⟨G.selected i, Set.mem_univ _⟩ : (Set.univ : Set ProjectiveDirection))
            (diff_subset (interior_subset hzi))
        have hmeas : MeasurableSet (G.liSelectedExterior N strongR₀) :=
          measurableSet_liSelectedExteriorUnion _ _ _
        have htop' : volume.toOuterMeasure (G.liSelectedExterior N strongR₀) = ⊤ := by
          simpa [hmeas] using htop
        have hm := volume.toOuterMeasure.mono hsubset
        change volume.measureOf (G.liSelectedExterior N strongR₀) = ⊤ at htop'
        change volume.measureOf (G.liSelectedExterior N strongR₀) ≤
          volume.measureOf (directionTriangleUnion N Set.univ) at hm
        rw [htop'] at hm
        change _ ≤ volume.measureOf (directionTriangleUnion N Set.univ)
        rw [top_unique hm]
        exact le_top
      · have hsummable := summable_of_cost_tsum_ne_top
          (fun i => hH0_all (G.selected i)) (by simpa [B] using hBtop)
        have hsum4 : Summable (fun i => 4 * H (G.selected i)) := hsummable.mul_left 4
        let b := ∑' i, 4 * H (G.selected i)
        let mc := max Real.pi b
        have hb0 : 0 ≤ b := tsum_nonneg fun i =>
          mul_nonneg (by norm_num) (hH0_all _)
        have hBeq : B = ENNReal.ofReal b := by
          dsimp [B, b]
          rw [← ENNReal.ofReal_tsum_of_nonneg]
          · intro i
            exact mul_nonneg (by norm_num) (hH0_all _)
          · exact hsum4
        have hcover : ENNReal.ofReal Real.pi ≤
            directionAngleOuter (greedyResidual G.remaining) + ENNReal.ofReal b := by
          rw [← hBeq]
          exact huniv.trans (by
            change directionAngleOuter G.initial ≤
              directionAngleOuter (greedyResidual G.remaining) + B
            exact G.initial_directionAngleOuter_le_residual_add_cost)
        let Θ := liResidualAngles N (greedyResidual G.remaining)
        have hres : ENNReal.ofReal (mc - b) ≤ angleSetOuter Θ := by
          by_cases hbp : b ≤ Real.pi
          · rw [show mc = Real.pi by simp [mc, hbp]]
            exact (ofReal_sub_le_of_le_add_ofReal Real.pi_pos.le hb0 hcover).trans
              (directionAngleOuter_le_angleSetOuter_liResidualAngles N _)
          · have hpb : Real.pi ≤ b := le_of_not_ge hbp
            rw [show mc = b by simp [mc, hpb], sub_self, ENNReal.ofReal_zero]
            exact bot_le
        have hselectedArea := liSelectedExteriorUnion_area_strong G.selected
          (fun i => N (G.selected i)) (fun i => hheightA _)
          (fun i j hij => by
            rcases lt_or_gt_of_ne hij with hij | hji
            · simpa [hheight] using
                (G.future_triangle_shadow_sum_lt_distance hr hpos hscaled hHeq hij).le
            · simpa [hheight, dist_comm, add_comm] using
                (G.future_triangle_shadow_sum_lt_distance hr hpos hscaled hHeq hji).le)
        have hfacpos : 0 < li25ExteriorFactor eps := by
          unfold li25ExteriorFactor
          exact div_pos (mul_pos (by norm_num) (Real.arcsin_pos.2 (by linarith)))
            Real.pi_pos
        have hfac0 : 0 ≤ li25ExteriorFactor eps := hfacpos.le
        have harea : ENNReal.ofReal
            (liF strongR₀ * li25ExteriorFactor eps / 4 * b) ≤
            volume (G.liSelectedExterior N strongR₀) := by
          have heq : liF strongR₀ * li25ExteriorFactor eps / 4 * b = ∑' i,
              liF strongR₀ * (li25ExteriorFactor eps * H (G.selected i)) := by
            dsimp [b]
            rw [← hsum4.tsum_mul_left (liF strongR₀ * li25ExteriorFactor eps / 4)]
            apply tsum_congr
            intro i
            ring
          rw [heq, ENNReal.ofReal_tsum_of_nonneg]
          · exact (ENNReal.tsum_le_tsum (fun i => ENNReal.ofReal_le_ofReal
                (mul_le_mul_of_nonneg_left (hraw_all _) (by unfold liF; positivity)))).trans
              hselectedArea
          · intro i
            exact mul_nonneg (by unfold liF; positivity)
              (mul_nonneg hfac0 (hH0_all _))
          · exact (hsummable.mul_left (liF strongR₀ * li25ExteriorFactor eps)).congr
              (fun i => by ring)
        have hheight_le_H : ∀ i, height (G.selected i) ≤ H (G.selected i) := by
          intro i
          have hd := height_eq_multiplier_rho_sin_paperWeight G.multiplier_pos hr
            (abs_nonneg _) (hscaled i).le
          change height (G.selected i) = G.multiplier * strongR₀ *
            Real.sin (Real.arcsin (height (G.selected i) /
              (G.multiplier * strongR₀))) at hd
          rw [← hHeq i] at hd
          have hs := Real.sin_le (hH0_all (G.selected i))
          have hmr : G.multiplier * strongR₀ ≤ 1 := by
            nlinarith [G.multiplier_lt_one, hr1]
          have hsin0 : 0 ≤ Real.sin (H (G.selected i)) := by
            rw [hHeq i, Real.sin_arcsin]
            · exact div_nonneg (by
                dsimp [height, li25Height]
                exact abs_nonneg (N (G.selected i)).height)
                (mul_pos G.multiplier_pos hr).le
            · have hh : 0 ≤ height (G.selected i) /
                  (G.multiplier * strongR₀) := div_nonneg (by
                    dsimp [height, li25Height]
                    exact abs_nonneg (N (G.selected i)).height)
                  (mul_pos G.multiplier_pos hr).le
              linarith
            · rw [div_le_one (mul_pos G.multiplier_pos hr)]
              exact (hscaled i).le
          nlinarith
        have hzero := G.residual_height_zero_of_summable_cost
          (fun _ => abs_nonneg _) hheight_le_H hsummable
        have hsectorRay := polarSector_liResidualAngles_subset_liResidualRayFan
          N (greedyResidual G.remaining) hr.le
        have hsectorE := polarSector_liResidualAngles_subset_directionTriangleUnion
          N Set.univ (greedyResidual G.remaining) hr.le hr1 (fun _ _ => Set.mem_univ _)
          (fun d hd => by
          apply abs_eq_zero.mp
          simpa [height, li25Height] using hzero d hd)
        have hdisj := G.disjoint_liResidualRayFan_liSelectedExterior N hr hheight
          hpos hscaled hHeq
        let C : LiLemma25GreedyCertificate Set.univ N strongR₀ mc :=
          { epsilon := eps
            epsilon_pos := heps0
            epsilon_lt_one := heps1
            deletionCost := b
            deletionCost_nonneg := hb0
            deletionCost_le_mass := le_max_right _ _
            selectedExterior := G.liSelectedExterior N strongR₀
            residualFan := polarSector 0 strongR₀ Θ
            selectedExterior_measurable := measurableSet_liSelectedExteriorUnion _ _ _
            selectedExterior_subset := by
              intro z hz
              simp only [FixedDeletionGreedyData.liSelectedExterior,
                liSelectedExteriorUnion, mem_iUnion] at hz
              obtain ⟨i, hzi⟩ := hz
              exact Set.mem_iUnion_of_mem
                (⟨G.selected i, Set.mem_univ _⟩ : (Set.univ : Set ProjectiveDirection))
                (diff_subset (interior_subset hzi))
            selectedExterior_outside := by
              intro z hz
              simp only [FixedDeletionGreedyData.liSelectedExterior,
                liSelectedExteriorUnion, mem_iUnion] at hz
              obtain ⟨i, hzi⟩ := hz
              exact (interior_subset hzi).2
            residualFan_subset := hsectorE
            residualFan_disjoint_selected := hdisj.mono hsectorRay Subset.rfl
            selectedExteriorArea := harea
            residualFanArea := by
              have hc : 0 ≤ strongR₀ ^ 2 / 2 := by positivity
              rw [ENNReal.ofReal_mul hc]
              exact (mul_le_mul_left' hres _).trans
                (polarSector_outerMeasure_ge 0 hr.le Θ) }
        have hmc0 : 0 ≤ mc := Real.pi_pos.le.trans (le_max_left _ _)
        have hout := liLemma25OuterStatement_epsilon Set.univ N strongR₀
          (Real.pi * strongP * strongILower) mc hr0 hr1
          (by
          exact mul_nonneg
            (mul_nonneg Real.pi_pos.le (by norm_num [strongP]))
            (by norm_num [strongILower])) hmc0 hinner C
        dsimp [C] at hout
        apply (ENNReal.ofReal_le_ofReal ?_).trans hout
        have hcoef : 0 ≤ liF strongR₀ * li25ExteriorFactor eps := by
          exact mul_nonneg (by unfold liF; positivity)
            (by unfold li25ExteriorFactor; positivity)
        have hpimc : Real.pi ≤ mc := le_max_left _ _
        nlinarith

/-- The strong-parameter Li 2.5 theorem, obtained by letting the independently
chosen fixed-selection normalization tend to one. -/
theorem strongLiLemma25 : StrongLiLemma25Theorem := by
  intro N hheightA hinner
  let eps : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have heps0 (n : ℕ) : 0 < eps n := by
    dsimp [eps]
    positivity
  have hepshalf (n : ℕ) : eps n ≤ 1 / 2 := by
    dsimp [eps]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) + 2)]
    nlinarith
  have hlower (n : ℕ) :=
    strongLiLemma25_epsilon N hheightA hinner (eps n) (heps0 n) (hepshalf n)
  have heps_tendsto : Filter.Tendsto eps Filter.atTop (nhds 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (Filter.tendsto_add_atTop_nat 1)
    convert h using 1
    funext n
    dsimp [eps, Function.comp_def]
    push_cast
    ring
  have hfactor : Filter.Tendsto
      (fun n => li25ExteriorFactor (eps n)) Filter.atTop (nhds 1) := by
    have harg : Filter.Tendsto (fun n => 1 - eps n) Filter.atTop
        (nhds (1 - 0)) := heps_tendsto.const_sub 1
    have hasin := Real.continuous_arcsin.continuousAt.tendsto.comp harg
    have hquot := (hasin.const_mul 2).div_const Real.pi
    have hpi : 2 * (Real.pi / 2) / Real.pi = (1 : ℝ) := by
      field_simp [ne_of_gt Real.pi_pos]
    simpa only [li25ExteriorFactor, Function.comp_apply, sub_zero,
      Real.arcsin_one, hpi] using hquot
  let phi : ℝ → ℝ := fun x =>
    Real.pi / 4 * (liF strongR₀ * x) +
      (1 - liF strongR₀ * x / (2 * strongR₀ ^ 2)) *
        (Real.pi * strongP * strongILower)
  have hphi : Continuous phi := by
    dsimp [phi]
    fun_prop
  have hreal : Filter.Tendsto
      (fun n => phi (li25ExteriorFactor (eps n))) Filter.atTop
      (nhds (phi 1)) := hphi.continuousAt.tendsto.comp hfactor
  have henn : Filter.Tendsto
      (fun n => ENNReal.ofReal (phi (li25ExteriorFactor (eps n))))
      Filter.atTop (nhds (ENNReal.ofReal (phi 1))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hlim := le_of_tendsto henn (Filter.Eventually.of_forall (fun n => by
    simpa [phi] using hlower n))
  simpa [phi] using hlim

/-- Strong-parameter adapter for the conditional Case-I assembly.  Unlike the
 generic conditional theorem, this consumes the proved strong Li-2.5 theorem
 directly, including the required uniform height cap. -/
theorem strongCaseI_conditional_area_lower_bound_strong
    {a : ℝ} (ha : 0 ≤ a)
    (N : (d : ProjectiveDirection) → DirectionNeedle d)
    (htrace : ∀ r ∈ Icc a strongR₀, ∀ d,
      FirstArcData (N d).triangle r)
    (A : ℝ → Set ProjectiveDirection) (g : ℝ → ℝ) (q : ℝ → ℝ≥0∞)
    (hg : ∀ r ∈ Icc a strongR₀, 1 ≤ g r)
    (hmass : ∀ r (hr : r ∈ Icc a strongR₀),
      ENNReal.ofReal (g r) * q r ≤ directionOuterMass (A r))
    (hcritical : ∀ r (hr : r ∈ Icc a strongR₀),
      FirstArcPointwiseHybridCriticalContainment
        (directionNeedleFamilyOfRaw N (htrace r hr)) (A r) (g r))
    (hI : ENNReal.ofReal (Real.pi * strongP * strongILower) ≤
      ∫⁻ r in Icc a strongR₀, ENNReal.ofReal r * q r)
    (hheight : ∀ d, |(N d).height| ≤ strongA) :
    ENNReal.ofReal (Real.pi * strongTarget) <
      volume.toOuterMeasure (directionTriangleUnion N Set.univ) := by
  let Eall := directionTriangleUnion N Set.univ
  have hinner : ENNReal.ofReal (Real.pi * strongP * strongILower) ≤
      volume.toOuterMeasure (Eall ∩ originClosedDisk strongR₀) :=
    hI.trans (outerMeasure_inner_ge_caseI_lintegral_of_raw ha N htrace A g q
      hg hmass hcritical)
  have hinnerOpen : ENNReal.ofReal (Real.pi * strongP * strongILower) ≤
      volume.toOuterMeasure (Eall ∩ originOpenDisk strongR₀) := by
    rw [outerMeasure_inter_originOpenDisk_eq_closedDisk]
    exact hinner
  have hLi := strongLiLemma25 N hheight hinnerOpen
  have hstrict : ENNReal.ofReal (Real.pi * strongTarget) <
      ENNReal.ofReal (Real.pi * strongCaseI strongILower) := by
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ?_).2
    · exact mul_lt_mul_of_pos_left strong_caseI_strict Real.pi_pos
    · exact mul_nonneg Real.pi_pos.le (by norm_num [strongTarget])
  rw [strong_li25_output_eq] at hLi
  exact hstrict.trans_le hLi

end

end StarKakeyaLower
