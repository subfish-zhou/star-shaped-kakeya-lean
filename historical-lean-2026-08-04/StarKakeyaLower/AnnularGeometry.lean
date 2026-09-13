import StarKakeyaLower.CaseIIGeometry

/-!
# Annular geometry for one escaping needle triangle

This module proves the *weak form* of `PROOF.md` Proposition 4.5 (the exterior
area of a single escaping origin triangle) and the scalar payment corollary of
`PROOF.md` Proposition 5.3.  The sharp width `W_ρ` of Lemma 4.3 is deliberately
**not** formalised: §5 of `PROOF.md` uses only the weaker bound
`A(s) ≤ arcsin (δ/ρ)`, and that is what is proved here.

The file is generic: no frozen witness constant occurs in it, and its imports
(`CaseIIGeometry` and its transitive closure) are all CLEAN modules.
-/

open Set MeasureTheory Metric

namespace StarKakeyaLower

noncomputable section

/-! ## Closed circular sectors over a real angular interval

`euclideanPolarSector` (`PolarOuterMeasure.lean`) intersects the angle set with
the standard cut `Ioo (-π) π`, which is exactly right for the *lower* bounds it
is used for, but useless for covering a triangle whose angular arc happens to
straddle the cut.  The sector used here therefore carries no cut; it is a
genuine compact set, and the cut is reintroduced only inside the proof of the
area bound, after a rotation has moved the arc into `Ioo (-π) π`. -/

/-- The closed circular sector of radius `r0` at `o` spanned by the real angular
interval `Icc a b`.  No branch cut is imposed. -/
def arcSector (o : Plane) (r0 a b : ℝ) : Set Plane :=
  {z | ∃ r ∈ Icc (0 : ℝ) r0, ∃ θ ∈ Icc a b, z = o + r • angleVector θ}

theorem continuous_angleVector : Continuous angleVector := by
  have h : angleVector = fun t : ℝ =>
      Real.cos t • (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) +
        Real.sin t • (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) := by
    funext t
    ext i
    fin_cases i <;> simp [angleVector]
  rw [h]
  fun_prop

theorem arcSector_eq_image (o : Plane) (r0 a b : ℝ) :
    arcSector o r0 a b =
      (fun p : ℝ × ℝ => o + p.1 • angleVector p.2) '' (Icc 0 r0 ×ˢ Icc a b) := by
  ext z
  simp only [arcSector, mem_setOf_eq, mem_image, Prod.exists, mem_prod]
  constructor
  · rintro ⟨r, hr, θ, hθ, rfl⟩
    exact ⟨r, θ, ⟨hr, hθ⟩, rfl⟩
  · rintro ⟨r, θ, ⟨hr, hθ⟩, rfl⟩
    exact ⟨r, hr, θ, hθ, rfl⟩

theorem isCompact_arcSector (o : Plane) (r0 a b : ℝ) :
    IsCompact (arcSector o r0 a b) := by
  rw [arcSector_eq_image]
  exact (isCompact_Icc.prod isCompact_Icc).image
    ((continuous_const.add
      ((continuous_fst.smul (continuous_angleVector.comp continuous_snd)))))

theorem measurableSet_arcSector (o : Plane) (r0 a b : ℝ) :
    MeasurableSet (arcSector o r0 a b) :=
  (isCompact_arcSector o r0 a b).isClosed.measurableSet

theorem arcSector_subset_closedBall (o : Plane) (r0 a b : ℝ) :
    arcSector o r0 a b ⊆ Metric.closedBall o r0 := by
  rintro _ ⟨r, hr, θ, _, rfl⟩
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
    norm_angleVector, mul_one, Real.norm_eq_abs, abs_of_nonneg hr.1]
  exact hr.2

/-! ### Rotations of the coordinate plane

The area bound below is obtained by moving the arc into the standard cut, which
requires the rotation invariance of planar Lebesgue measure.  The rotation is
built by hand as a linear map with determinant one; `Measure.addHaar_image_linearMap`
then supplies invariance. -/

/-- Rotation of the coordinate plane by the angle `c`. -/
def rotLinear (c : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun p := WithLp.toLp 2
    ![Real.cos c * p 0 - Real.sin c * p 1, Real.sin c * p 0 + Real.cos c * p 1]
  map_add' p q := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a p := by ext i; fin_cases i <;> simp <;> ring

@[simp] theorem rotLinear_apply_zero (c : ℝ) (p : Plane) :
    rotLinear c p 0 = Real.cos c * p 0 - Real.sin c * p 1 := by
  simp [rotLinear]

@[simp] theorem rotLinear_apply_one (c : ℝ) (p : Plane) :
    rotLinear c p 1 = Real.sin c * p 0 + Real.cos c * p 1 := by
  simp [rotLinear]

theorem det_rotLinear (c : ℝ) : LinearMap.det (rotLinear c) = 1 := by
  rw [← LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin 2)), Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, PiLp.basisFun_apply]
  norm_num
  linear_combination Real.cos_sq_add_sin_sq c

theorem rotLinear_angleVector (c θ : ℝ) :
    rotLinear c (angleVector θ) = angleVector (θ + c) := by
  ext i
  fin_cases i
  · simp [Real.cos_add]
    ring
  · simp [Real.sin_add]
    ring

theorem volume_image_rotLinear (c : ℝ) (s : Set Plane) :
    volume (rotLinear c '' s) = volume s := by
  rw [Measure.addHaar_image_linearMap, det_rotLinear]
  simp

theorem image_rotLinear_arcSector (c : ℝ) (o : Plane) (r0 a b : ℝ) :
    rotLinear c '' arcSector o r0 a b = arcSector (rotLinear c o) r0 (a + c) (b + c) := by
  ext z
  simp only [arcSector, mem_image, mem_setOf_eq]
  constructor
  · rintro ⟨w, ⟨r, hr, θ, hθ, rfl⟩, rfl⟩
    refine ⟨r, hr, θ + c, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩, ?_⟩
    rw [map_add, map_smul, rotLinear_angleVector]
  · rintro ⟨r, hr, θ, hθ, rfl⟩
    refine ⟨o + r • angleVector (θ - c), ⟨r, hr, θ - c,
      ⟨by linarith [hθ.1], by linarith [hθ.2]⟩, rfl⟩, ?_⟩
    rw [map_add, map_smul, rotLinear_angleVector, sub_add_cancel]

theorem volume_arcSector_congr_center (o o' : Plane) (r0 a b : ℝ) :
    volume (arcSector o r0 a b) = volume (arcSector o' r0 a b) := by
  have himage : arcSector o r0 a b =
      (fun z : Plane => (o - o') + z) '' arcSector o' r0 a b := by
    ext z
    simp only [arcSector, mem_image, mem_setOf_eq]
    constructor
    · rintro ⟨r, hr, θ, hθ, rfl⟩
      exact ⟨o' + r • angleVector θ, ⟨r, hr, θ, hθ, rfl⟩, by abel⟩
    · rintro ⟨w, ⟨r, hr, θ, hθ, rfl⟩, rfl⟩
      exact ⟨r, hr, θ, hθ, by abel⟩
  rw [himage, Set.image_add_left, measure_preimage_add]

/-! ### The sector area bound

The upper bound is obtained by complementation inside the disc: the sector and
the *complementary* radial fan are disjoint apart from the centre, and the
complementary fan already has a lower area bound in `PolarOuterMeasure`. -/

private theorem volume_closedBall_plane (o : Plane) {r0 : ℝ} (hr0 : 0 ≤ r0) :
    volume (Metric.closedBall o r0) = ENNReal.ofReal (Real.pi * r0 ^ 2) := by
  rw [EuclideanSpace.volume_closedBall, Fintype.card_fin]
  have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hg : Real.Gamma (((2 : ℕ) : ℝ) / 2 + 1) = 1 := by
    norm_num
  rw [hsq, hg, div_one, ← ENNReal.ofReal_pow hr0,
    ← ENNReal.ofReal_mul (by positivity)]
  rw [mul_comm]

private theorem volume_arcSector_le_of_mem_cut (o : Plane) {r0 a b : ℝ}
    (hr0 : 0 ≤ r0) (ha : -Real.pi < a) (hb : b < Real.pi) :
    volume (arcSector o r0 a b) ≤ ENNReal.ofReal (r0 ^ 2 / 2 * (b - a)) := by
  classical
  set S := arcSector o r0 a b with hSdef
  set Theta : Set ℝ := Ioo (-Real.pi) Real.pi \ Icc a b with hThetaDef
  have hIcc : Icc a b ⊆ Ioo (-Real.pi) Real.pi := fun x hx =>
    ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hThetaCut : Theta ⊆ Ioo (-Real.pi) Real.pi := fun _ hx => hx.1
  -- the complementary radial fan meets the sector only at the centre
  have hdisj : euclideanPolarSector o r0 Theta \ {o} ⊆ Metric.closedBall o r0 \ S := by
    rintro z ⟨hzs, hz0⟩
    obtain ⟨r', hr', θ', hθ', hzeq⟩ := hzs
    have hnorm : ‖z - o‖ = r' := by
      rw [hzeq, add_sub_cancel_left, norm_smul, norm_angleVector, mul_one,
        Real.norm_eq_abs, abs_of_nonneg hr'.1]
    have hrpos : 0 < r' := by
      rcases eq_or_lt_of_le hr'.1 with h | h
      · exact absurd (by rw [hzeq, ← h]; simp) hz0
      · exact h
    refine ⟨by rw [Metric.mem_closedBall, dist_eq_norm, hnorm]; exact hr'.2, ?_⟩
    intro hzS
    obtain ⟨r, hr, θ, hθ, hz2⟩ := hzS
    have hnorm2 : ‖z - o‖ = r := by
      rw [hz2, add_sub_cancel_left, norm_smul, norm_angleVector, mul_one,
        Real.norm_eq_abs, abs_of_nonneg hr.1]
    have hrr : r = r' := by rw [← hnorm2, hnorm]
    have hvec : r' • angleVector θ = r' • angleVector θ' := by
      have h1 : z - o = r • angleVector θ := by rw [hz2, add_sub_cancel_left]
      have h2 : z - o = r' • angleVector θ' := by rw [hzeq, add_sub_cancel_left]
      rw [← hrr, ← h1, h2, hrr]
    have hav : angleVector θ = angleVector θ' := by
      have := congrArg (fun v : Plane => (r')⁻¹ • v) hvec
      simpa [inv_smul_smul₀ (ne_of_gt hrpos)] using this
    have hc : Real.cos θ = Real.cos θ' := by
      have := congrArg (fun v : Plane => v 0) hav
      simpa using this
    have hs : Real.sin θ = Real.sin θ' := by
      have := congrArg (fun v : Plane => v 1) hav
      simpa using this
    have hcos1 : Real.cos (θ - θ') = 1 := by
      rw [Real.cos_sub, hc, hs, ← Real.cos_sq_add_sin_sq θ']
      ring
    have hθcut : θ ∈ Ioo (-Real.pi) Real.pi := hIcc hθ
    have hθ'cut : θ' ∈ Ioo (-Real.pi) Real.pi := hθ'.2
    have hzero : θ - θ' = 0 :=
      (Real.cos_eq_one_iff_of_lt_of_lt
        (by linarith [hθcut.1, hθ'cut.2]) (by linarith [hθcut.2, hθ'cut.1])).1 hcos1
    exact hθ'.1.2 (by rwa [show θ' = θ by linarith])
  -- Carathéodory split of the disc along the (compact, hence measurable) sector
  have hSmeas : MeasurableSet S := measurableSet_arcSector o r0 a b
  have hSsub : S ⊆ Metric.closedBall o r0 := arcSector_subset_closedBall o r0 a b
  have hsplit : volume S + volume (Metric.closedBall o r0 \ S) =
      volume (Metric.closedBall o r0) := by
    have h := measure_inter_add_diff (μ := volume) (Metric.closedBall o r0) hSmeas
    rwa [Set.inter_eq_self_of_subset_right hSsub] at h
  -- area lower bound for the complementary fan
  have hfan : ENNReal.ofReal (r0 ^ 2 / 2) * volume Theta ≤
      volume (Metric.closedBall o r0 \ S) := by
    have h1 := euclideanPolarSector_outerMeasure_ge o hr0 Theta
    rw [angleSetOuter, Set.inter_eq_self_of_subset_left hThetaCut,
      Measure.toOuterMeasure_apply, Measure.toOuterMeasure_apply] at h1
    refine h1.trans ?_
    calc volume (euclideanPolarSector o r0 Theta)
        ≤ volume ((euclideanPolarSector o r0 Theta \ {o}) ∪ {o}) := by
          apply measure_mono
          intro x hx
          by_cases hxo : x = o
          · exact Or.inr hxo
          · exact Or.inl ⟨hx, hxo⟩
      _ ≤ volume (euclideanPolarSector o r0 Theta \ {o}) + volume ({o} : Set Plane) :=
          measure_union_le _ _
      _ = volume (euclideanPolarSector o r0 Theta \ {o}) := by
          rw [measure_singleton, add_zero]
      _ ≤ volume (Metric.closedBall o r0 \ S) := measure_mono hdisj
  -- angular budget
  have hThetaMeas : ENNReal.ofReal (b - a) + volume Theta =
      ENNReal.ofReal (2 * Real.pi) := by
    have h := measure_inter_add_diff (μ := volume) (Ioo (-Real.pi) Real.pi)
      (measurableSet_Icc (a := a) (b := b))
    rw [Set.inter_eq_self_of_subset_right hIcc, Real.volume_Icc, Real.volume_Ioo] at h
    rw [hThetaDef, h]
    congr 1
    ring
  have hThetaLe : volume Theta ≤ ENNReal.ofReal (2 * Real.pi) := by
    rw [← hThetaMeas]
    exact le_add_self
  have hThetaFinite : ENNReal.ofReal (r0 ^ 2 / 2) * volume Theta ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hThetaLe)
  refine ENNReal.le_of_add_le_add_right hThetaFinite ?_
  calc volume S + ENNReal.ofReal (r0 ^ 2 / 2) * volume Theta
      ≤ volume S + volume (Metric.closedBall o r0 \ S) := by gcongr
    _ = volume (Metric.closedBall o r0) := hsplit
    _ = ENNReal.ofReal (Real.pi * r0 ^ 2) := volume_closedBall_plane o hr0
    _ = ENNReal.ofReal (r0 ^ 2 / 2) * ENNReal.ofReal (2 * Real.pi) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ = ENNReal.ofReal (r0 ^ 2 / 2) * (ENNReal.ofReal (b - a) + volume Theta) := by
        rw [hThetaMeas]
    _ = ENNReal.ofReal (r0 ^ 2 / 2 * (b - a)) +
          ENNReal.ofReal (r0 ^ 2 / 2) * volume Theta := by
        rw [mul_add, ← ENNReal.ofReal_mul (by positivity)]

/-- **Sector area bound.**  A closed circular sector of radius `r0` over a real
angular interval of length at most `π` has at most the expected polar area. -/
theorem volume_arcSector_le (o : Plane) {r0 a b : ℝ} (hr0 : 0 ≤ r0)
    (hlen : b - a ≤ Real.pi) :
    volume (arcSector o r0 a b) ≤ ENNReal.ofReal (r0 ^ 2 / 2 * (b - a)) := by
  have hpi := Real.pi_pos
  set c : ℝ := -(a + b) / 2 with hc
  have hrot : volume (arcSector o r0 a b) =
      volume (arcSector (0 : Plane) r0 (a + c) (b + c)) := by
    rw [← volume_image_rotLinear c (arcSector o r0 a b), image_rotLinear_arcSector,
      volume_arcSector_congr_center (rotLinear c o) 0]
  have hlow : -Real.pi < a + c := by rw [hc]; linarith
  have hhigh : b + c < Real.pi := by rw [hc]; linarith
  have h := volume_arcSector_le_of_mem_cut (0 : Plane) hr0 hlow hhigh
  rw [hrot]
  simpa [show b + c - (a + c) = b - a by ring] using h

/-! ## One-sided support coordinates of an escaping needle

`normalCoord t` is the signed distance to the support line of the oriented
needle; `supportCoord t` is the complementary tangential coordinate.  Together
they are Euclidean coordinates adapted to the needle, which is what turns the
`OutsideBall` hypothesis into a *one-sided* angular statement for the whole
segment (not merely for its endpoints). -/

/-- Tangential coordinate along the oriented support line of angle `t`. -/
def supportCoord (t : ℝ) (x : Plane) : ℝ := x 0 * Real.cos t + x 1 * Real.sin t

theorem supportCoord_add (t : ℝ) (x y : Plane) :
    supportCoord t (x + y) = supportCoord t x + supportCoord t y := by
  simp only [supportCoord, PiLp.add_apply]; ring

theorem supportCoord_smul (t k : ℝ) (x : Plane) :
    supportCoord t (k • x) = k * supportCoord t x := by
  simp only [supportCoord, PiLp.smul_apply, smul_eq_mul]; ring

@[simp] theorem supportCoord_angleVector_self (t : ℝ) :
    supportCoord t (angleVector t) = 1 := by
  simp only [supportCoord, angleVector_zero, angleVector_one]
  rw [← Real.cos_sq_add_sin_sq t]; ring

theorem angleVector_add_pi (t : ℝ) : angleVector (t + Real.pi) = -angleVector t := by
  ext i
  fin_cases i <;> simp [angleVector, Real.cos_add, Real.sin_add]

theorem supportCoord_add_pi (t : ℝ) (x : Plane) :
    supportCoord (t + Real.pi) x = -supportCoord t x := by
  simp only [supportCoord, Real.cos_add, Real.sin_add]
  simp
  ring

theorem norm_sq_plane (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

theorem supportCoord_sq_add_normalCoord_sq (t : ℝ) (x : Plane) :
    supportCoord t x ^ 2 + normalCoord t x ^ 2 = ‖x‖ ^ 2 := by
  rw [norm_sq_plane]
  simp only [supportCoord, normalCoord, det, angleVector_zero, angleVector_one]
  linear_combination (x 0 ^ 2 + x 1 ^ 2) * Real.cos_sq_add_sin_sq t

/-- Polar reconstruction adapted to the support line: when the tangential
coordinate is positive, the point's polar angle is `t` plus an explicit
arcsine of the (constant) normal coordinate divided by the radius. -/
theorem eq_smul_angleVector_arcsin {t : ℝ} {x : Plane}
    (hs : 0 < supportCoord t x) :
    x = ‖x‖ • angleVector (t + Real.arcsin (normalCoord t x / ‖x‖)) := by
  set s := supportCoord t x with hsdef
  set N := normalCoord t x with hNdef
  set r := ‖x‖ with hrdef
  have hpyth : s ^ 2 + N ^ 2 = r ^ 2 := supportCoord_sq_add_normalCoord_sq t x
  have hrpos : 0 < r := by
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ r from norm_nonneg x) with h | h
    · exfalso
      rw [← h] at hpyth
      nlinarith [sq_nonneg N]
    · exact h
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have habs : |N / r| ≤ 1 := by
    rw [abs_div, abs_of_pos hrpos, div_le_one hrpos]
    nlinarith [sq_abs N, sq_abs r, abs_nonneg N, abs_nonneg r, sq_nonneg s]
  have hb := abs_le.1 habs
  have hsin : Real.sin (Real.arcsin (N / r)) = N / r := Real.sin_arcsin hb.1 hb.2
  have hcos : Real.cos (Real.arcsin (N / r)) = s / r := by
    rw [Real.cos_arcsin]
    rw [show 1 - (N / r) ^ 2 = (s / r) ^ 2 by field_simp; nlinarith]
    exact Real.sqrt_sq (by positivity)
  have hkey0 : Real.cos t * s - Real.sin t * N = x 0 := by
    simp only [hsdef, hNdef, supportCoord, normalCoord, det, angleVector_zero,
      angleVector_one]
    linear_combination (x 0) * Real.cos_sq_add_sin_sq t
  have hkey1 : Real.sin t * s + Real.cos t * N = x 1 := by
    simp only [hsdef, hNdef, supportCoord, normalCoord, det, angleVector_zero,
      angleVector_one]
    linear_combination (x 1) * Real.cos_sq_add_sin_sq t
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, PiLp.smul_apply, smul_eq_mul,
      angleVector_zero, Real.cos_add, hsin, hcos]
    rw [← hkey0]
    field_simp
  · simp only [Fin.mk_one, PiLp.smul_apply, smul_eq_mul,
      angleVector_one, Real.sin_add, hsin, hcos]
    rw [← hkey1]
    field_simp

/-- The normal coordinate is constant along the needle and its absolute value
is the determinant height. -/
theorem UnitNeedle.normalCoord_carrier_eq {o : Plane} {n : UnitNeedle} {t c : ℝ}
    (hd : n.right - n.left = c • angleVector t)
    {K : Plane} (hK : K ∈ n.carrier) :
    normalCoord t (K - o) = normalCoord t (n.left - o) := by
  have hline : normalCoord t (K - n.left) = 0 :=
    n.onSupportLine_of_mem_carrier hd hK
  have hsplit : K - o = (K - n.left) + (n.left - o) := by abel
  rw [hsplit, normalCoord_add, hline, zero_add]

theorem UnitNeedle.abs_normalCoord_left_eq_height {o : Plane} {n : UnitNeedle}
    {t c : ℝ} (hc : |c| = 1) (hd : n.right - n.left = c • angleVector t) :
    |normalCoord t (n.left - o)| = n.height o := by
  rw [n.height_eq_abs_normalCoord hc hd]
  rw [show n.left - o = (-1 : ℝ) • (o - n.left) by module, normalCoord_smul]
  rw [abs_mul]
  norm_num

/-- **Layer 1 + 2 (arc containment).**  Under a positive tangential coordinate
along the whole needle, every point of the origin triangle inside the closed
ball of radius `r0` lies in one closed circular sector whose angular aperture is
at most `arcsin (height / ρ)`. -/
theorem UnitNeedle.triangleHull_inter_closedBall_subset_arcSector_of_pos
    {rho r0 : ℝ} {o : Plane} {n : UnitNeedle} {t c : ℝ}
    (hrho : 0 < rho)
    (hc : |c| = 1) (hd : n.right - n.left = c • angleVector t)
    (hout : n.OutsideBall rho o)
    (hpos : ∀ K ∈ n.carrier, 0 < supportCoord t (K - o)) :
    ∃ a : ℝ, n.triangleHull o ∩ Metric.closedBall o r0 ⊆
      arcSector o r0 a (a + Real.arcsin (n.height o / rho)) := by
  classical
  set delta := n.height o with hdeltadef
  set A := Real.arcsin (delta / rho) with hAdef
  set Nval := normalCoord t (n.left - o) with hNvaldef
  have hdelta0 : 0 ≤ delta := n.height_nonneg o
  have hNabs : |Nval| = delta := n.abs_normalCoord_left_eq_height hc hd
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    simpa using Real.arcsin_le_arcsin (show (0 : ℝ) ≤ delta / rho by positivity)
  have hrad : ∀ K ∈ n.carrier, rho ≤ ‖K - o‖ := by
    intro K hK
    have h := hout K hK
    rwa [dist_eq_norm, ← norm_neg, neg_sub] at h
  refine ⟨if 0 ≤ Nval then t else t - A, ?_⟩
  rintro p ⟨hpT, hpB⟩
  obtain ⟨l, hl, sigma, hsig, hpl⟩ := n.mem_triangleHull_iff_barycentric.mp hpT
  set K : Plane := n.left + sigma • (n.right - n.left) with hKdef
  have hKcar : K ∈ n.carrier := by
    change K ∈ segment ℝ n.left n.right
    rw [segment_eq_image']
    exact ⟨sigma, hsig, rfl⟩
  have hKo : K - o = (n.left - o) + sigma • (n.right - n.left) := by
    rw [hKdef]; abel
  have hpK : p - o = l • (K - o) := by rw [hpl, hKo]
  have hsK : 0 < supportCoord t (K - o) := hpos K hKcar
  have hNK : normalCoord t (K - o) = Nval :=
    n.normalCoord_carrier_eq hd hKcar
  set r := ‖K - o‖ with hrdef
  have hrhor : rho ≤ r := hrad K hKcar
  have hrpos : 0 < r := lt_of_lt_of_le hrho hrhor
  set phi := Real.arcsin (Nval / r) with hphidef
  have hKeq : K - o = r • angleVector (t + phi) := by
    have h := eq_smul_angleVector_arcsin hsK
    rwa [hNK] at h
  have hquot : |Nval / r| ≤ delta / rho := by
    rw [abs_div, hNabs, abs_of_pos hrpos]
    gcongr
  have hqb := abs_le.1 hquot
  have hmem : t + phi ∈ Icc (if 0 ≤ Nval then t else t - A)
      ((if 0 ≤ Nval then t else t - A) + A) := by
    by_cases hN : 0 ≤ Nval
    · rw [if_pos hN]
      have hlo : 0 ≤ phi := by
        rw [hphidef]
        simpa using
          Real.arcsin_le_arcsin (show (0 : ℝ) ≤ Nval / r from div_nonneg hN hrpos.le)
      have hhi : phi ≤ A := by
        rw [hphidef, hAdef]
        exact Real.arcsin_le_arcsin hqb.2
      exact ⟨by linarith, by linarith⟩
    · rw [if_neg hN]
      have hNneg : Nval / r ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hN) hrpos.le
      have hhi : phi ≤ 0 := by
        rw [hphidef]
        simpa using Real.arcsin_le_arcsin hNneg
      have hlo : -A ≤ phi := by
        rw [hphidef, hAdef, ← Real.arcsin_neg]
        exact Real.arcsin_le_arcsin hqb.1
      exact ⟨by linarith, by linarith⟩
  have hnormp : ‖p - o‖ = l * r := by
    rw [hpK, norm_smul, Real.norm_eq_abs, abs_of_nonneg hl.1]
  refine ⟨l * r, ⟨mul_nonneg hl.1 hrpos.le, ?_⟩, t + phi, hmem, ?_⟩
  · rw [← hnormp, ← dist_eq_norm]
    exact hpB
  · have : p - o = (l * r) • angleVector (t + phi) := by
      rw [hpK, hKeq, smul_smul]
    rw [← this]
    abel

/-- Total area of a filled needle triangle.  `TriangleArea` proves this for the
topological interior and records that the boundary is null; the closed hull has
the same area. -/
theorem UnitNeedle.volume_triangleHull_eq (o : Plane) (n : UnitNeedle) :
    volume (n.triangleHull o) = ENNReal.ofReal (n.height o / 2) := by
  refine le_antisymm ?_ ?_
  · calc volume (n.triangleHull o)
        ≤ volume (interior (n.triangleHull o) ∪ frontier (n.triangleHull o)) := by
          refine measure_mono ?_
          rw [← closure_eq_interior_union_frontier]
          exact subset_closure
      _ ≤ volume (interior (n.triangleHull o)) +
            volume (frontier (n.triangleHull o)) := measure_union_le _ _
      _ = ENNReal.ofReal (n.height o / 2) := by
          rw [n.volume_frontier_triangleHull o, add_zero, n.volume_triangleInterior o]
  · rw [← n.volume_triangleInterior o]
    exact measure_mono interior_subset

/-- The needle's angular arc, with no auxiliary one-sidedness hypothesis: the
`OutsideBall` condition alone forces the tangential coordinate to have a
constant sign along the *entire* unit segment. -/
theorem UnitNeedle.exists_arcSector_of_outside
    {rho r0 : ℝ} {o : Plane} {n : UnitNeedle}
    (hrho : 0 < rho)
    (hdelta : n.height o < rho) (hout : n.OutsideBall rho o) :
    ∃ a : ℝ, n.triangleHull o ∩ Metric.closedBall o r0 ⊆
      arcSector o r0 a (a + Real.arcsin (n.height o / rho)) := by
  classical
  set v : Plane := n.right - n.left with hvdef
  have hvnorm : ‖v‖ = 1 := by rw [hvdef, ← dist_eq_norm, dist_comm, n.unit_length]
  have hvne : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hvnorm
    norm_num at hvnorm
  set t : ℝ := vectorAngle v with htdef
  have hveq : v = angleVector t := by
    have h := norm_smul_angleVector_vectorAngle hvne
    rw [hvnorm, one_smul] at h
    exact h.symm
  have hd1 : n.right - n.left = (1 : ℝ) • angleVector t := by
    rw [← hvdef, hveq, one_smul]
  have hc1 : |(1 : ℝ)| = 1 := abs_one
  have hcarparam : ∀ K ∈ n.carrier, ∃ sigma ∈ Icc (0 : ℝ) 1, K = n.left + sigma • v := by
    intro K hK
    rw [show n.carrier = segment ℝ n.left n.right from rfl, segment_eq_image'] at hK
    obtain ⟨sigma, hsig, rfl⟩ := hK
    exact ⟨sigma, hsig, rfl⟩
  have hsaff : ∀ sigma : ℝ,
      supportCoord t (n.left + sigma • v - o) = supportCoord t (n.left - o) + sigma := by
    intro sigma
    rw [show n.left + sigma • v - o = (n.left - o) + sigma • v by abel,
      supportCoord_add, supportCoord_smul, hveq, supportCoord_angleVector_self,
      mul_one]
  have hne : ∀ K ∈ n.carrier, supportCoord t (K - o) ≠ 0 := by
    intro K hK h0
    have hN : |normalCoord t (K - o)| = n.height o := by
      rw [n.normalCoord_carrier_eq hd1 hK]
      exact n.abs_normalCoord_left_eq_height hc1 hd1
    have hpy := supportCoord_sq_add_normalCoord_sq t (K - o)
    have hr : rho ≤ ‖K - o‖ := by
      have h := hout K hK
      rwa [dist_eq_norm, ← norm_neg, neg_sub] at h
    rw [h0] at hpy
    nlinarith [sq_abs (normalCoord t (K - o)), n.height_nonneg o, hr, hdelta,
      norm_nonneg (K - o)]
  set s0 : ℝ := supportCoord t (n.left - o) with hs0def
  have hleft : n.left ∈ n.carrier := left_mem_segment ℝ n.left n.right
  have hright : n.right ∈ n.carrier := right_mem_segment ℝ n.left n.right
  have hs0ne : s0 ≠ 0 := hne n.left hleft
  have hs1 : supportCoord t (n.right - o) = s0 + 1 := by
    have h := hsaff 1
    rw [one_smul, show n.left + v = n.right by rw [hvdef]; abel] at h
    exact h
  have hs1ne : s0 + 1 ≠ 0 := by rw [← hs1]; exact hne n.right hright
  rcases lt_or_gt_of_ne hs0ne with hneg | hpos0
  · rcases lt_or_gt_of_ne hs1ne with hcase | hcase
    · -- the whole segment has negative tangential coordinate: use the lift `t + π`
      refine n.triangleHull_inter_closedBall_subset_arcSector_of_pos
        (t := t + Real.pi) (c := -1) (r0 := r0) hrho (by norm_num) ?_ hout ?_
      · rw [angleVector_add_pi, smul_neg, neg_smul, neg_neg, one_smul, ← hveq, ← hvdef]
      · intro K hK
        obtain ⟨sigma, hsig, rfl⟩ := hcarparam K hK
        rw [supportCoord_add_pi, hsaff]
        have := hsig.2
        linarith
    · -- the tangential coordinate would vanish somewhere on the segment
      exfalso
      have hroot : (-s0) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
      have hmem : n.left + (-s0) • v ∈ n.carrier := by
        rw [show n.carrier = segment ℝ n.left n.right from rfl, segment_eq_image']
        exact ⟨-s0, hroot, rfl⟩
      have h := hne _ hmem
      rw [hsaff] at h
      exact h (by ring)
  · -- the whole segment has positive tangential coordinate: use the lift `t`
    refine n.triangleHull_inter_closedBall_subset_arcSector_of_pos
      (t := t) (c := 1) (r0 := r0) hrho hc1 hd1 hout ?_
    intro K hK
    obtain ⟨sigma, hsig, rfl⟩ := hcarparam K hK
    rw [hsaff]
    have := hsig.1
    linarith

/-- **`PROOF.md` Proposition 4.5, weak form.**  The part of one escaping origin
triangle lying outside the closed ball of radius `r0` has at least the displayed
area.  The right-hand side may be negative, in which case the statement is
vacuous but true. -/
theorem UnitNeedle.volume_triangleHull_diff_closedBall_ge
    {rho r0 : ℝ} {o : Plane} {n : UnitNeedle}
    (hr0 : 0 < r0) (hlt : r0 < rho)
    (hdelta : n.height o < rho) (hout : n.OutsideBall rho o) :
    ENNReal.ofReal
        (n.height o / 2 - r0 ^ 2 / 2 * Real.arcsin (n.height o / rho)) ≤
      volume (n.triangleHull o \ Metric.closedBall o r0) := by
  have hrho : 0 < rho := lt_trans hr0 hlt
  set A : ℝ := Real.arcsin (n.height o / rho) with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    simpa using
      Real.arcsin_le_arcsin (show (0 : ℝ) ≤ n.height o / rho by
        exact div_nonneg (n.height_nonneg o) hrho.le)
  have hApi : A ≤ Real.pi := le_trans (Real.arcsin_le_pi_div_two _) (by linarith [Real.pi_pos])
  obtain ⟨a, hsub⟩ := n.exists_arcSector_of_outside (r0 := r0) hrho hdelta hout
  have hinter : volume (n.triangleHull o ∩ Metric.closedBall o r0) ≤
      ENNReal.ofReal (r0 ^ 2 / 2 * A) := by
    refine le_trans (measure_mono hsub) ?_
    have h := volume_arcSector_le o (r0 := r0) (a := a) (b := a + A) hr0.le
      (by simpa using hApi)
    simpa using h
  have hsplit : volume (n.triangleHull o ∩ Metric.closedBall o r0) +
      volume (n.triangleHull o \ Metric.closedBall o r0) = volume (n.triangleHull o) :=
    measure_inter_add_diff _ measurableSet_closedBall
  rcases le_or_gt (n.height o / 2 - r0 ^ 2 / 2 * A) 0 with hD | hD
  · rw [ENNReal.ofReal_eq_zero.2 hD]
    exact zero_le _
  · have hAnn : ENNReal.ofReal (n.height o / 2) ≤
        ENNReal.ofReal (r0 ^ 2 / 2 * A) +
          volume (n.triangleHull o \ Metric.closedBall o r0) := by
      rw [← n.volume_triangleHull_eq o, ← hsplit]
      gcongr
    have hEq : ENNReal.ofReal (n.height o / 2) =
        ENNReal.ofReal (n.height o / 2 - r0 ^ 2 / 2 * A) +
          ENNReal.ofReal (r0 ^ 2 / 2 * A) := by
      rw [← ENNReal.ofReal_add hD.le (by positivity)]
      congr 1
      ring
    rw [hEq, add_comm (ENNReal.ofReal (r0 ^ 2 / 2 * A))] at hAnn
    exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top hAnn

/-! ## The exterior payment coefficient

Both calculus inputs of `PROOF.md` §5 are instances of the concavity of `sin`
on `[0, π]`, so no derivative computation is repeated here. -/

/-- `PROOF.md` Lemma 5.1 (chord form of the concavity of `sin`). -/
theorem sin_chord_le {u u0 : ℝ} (hu0 : 0 < u0) (hu0pi : u0 ≤ Real.pi)
    (hu : 0 ≤ u) (huu0 : u ≤ u0) :
    u / u0 * Real.sin u0 ≤ Real.sin u := by
  have hconc := strictConcaveOn_sin_Icc.concaveOn
  have hmem0 : (0 : ℝ) ∈ Icc (0 : ℝ) Real.pi := ⟨le_rfl, Real.pi_pos.le⟩
  have hmemu0 : u0 ∈ Icc (0 : ℝ) Real.pi := ⟨hu0.le, hu0pi⟩
  have ha : 0 ≤ u / u0 := div_nonneg hu hu0.le
  have hb : 0 ≤ 1 - u / u0 := by
    rw [sub_nonneg, div_le_one hu0]
    exact huu0
  have h := hconc.2 hmemu0 hmem0 ha hb (by ring)
  simp only [smul_eq_mul, Real.sin_zero, mul_zero, add_zero] at h
  rwa [show u / u0 * u0 = u by field_simp] at h

/-- `PROOF.md` Lemma 5.2 (arcsine contraction). -/
theorem arcsin_mul_sin_le {m u : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ Real.pi / 2) :
    Real.arcsin (m * Real.sin u) ≤ m * u := by
  have hconc := strictConcaveOn_sin_Icc.concaveOn
  have hmem0 : (0 : ℝ) ∈ Icc (0 : ℝ) Real.pi := ⟨le_rfl, Real.pi_pos.le⟩
  have hmemu : u ∈ Icc (0 : ℝ) Real.pi := ⟨hu0, by linarith [Real.pi_pos]⟩
  have h : m • Real.sin u + (1 - m) • Real.sin 0 ≤
      Real.sin (m • u + (1 - m) • (0 : ℝ)) :=
    hconc.2 hmemu hmem0 hm0 (by linarith) (by ring)
  simp only [smul_eq_mul, Real.sin_zero, mul_zero, add_zero] at h
  calc Real.arcsin (m * Real.sin u) ≤ Real.arcsin (Real.sin (m * u)) :=
        Real.arcsin_le_arcsin h
    _ = m * u := Real.arcsin_sin (by nlinarith [Real.pi_pos]) (by nlinarith)

/-- `PROOF.md` (2.3): the exterior payment coefficient. -/
def annularCExt (a r0 rho m : ℝ) : ℝ :=
  a / (2 * Real.arcsin (a / (m * rho))) - m * r0 ^ 2 / 2

/-- **`PROOF.md` Proposition 5.3 (exterior payment).**  The exterior area of one
escaping origin triangle is at least `annularCExt` times the weighted angular
width `H(δ) = arcsin (δ / (m ρ))`. -/
theorem UnitNeedle.annular_payment
    {a r0 rho m : ℝ} {o : Plane} {n : UnitNeedle}
    (hm0 : 0 < m) (hm1 : m < 1) (ha : 0 < a) (harho : a < m * rho)
    (hr0 : 0 < r0) (hlt : r0 < rho)
    (hheight : n.height o ≤ a) (hout : n.OutsideBall rho o) :
    ENNReal.ofReal
        (annularCExt a r0 rho m * Real.arcsin (n.height o / (m * rho))) ≤
      volume (n.triangleHull o \ Metric.closedBall o r0) := by
  have hrho : 0 < rho := lt_trans hr0 hlt
  have hmrho : 0 < m * rho := mul_pos hm0 hrho
  set delta := n.height o with hdeltadef
  have hdelta0 : 0 ≤ delta := n.height_nonneg o
  have hmrholt : m * rho < rho := by nlinarith
  have hdeltarho : delta < rho := by linarith
  set u : ℝ := Real.arcsin (delta / (m * rho)) with hudef
  set u0 : ℝ := Real.arcsin (a / (m * rho)) with hu0def
  rcases eq_or_lt_of_le hdelta0 with hzero | hpos
  · rw [hudef, ← hzero]
    simp
  · have hu0pos : 0 < u0 := by
      rw [hu0def]
      exact Real.arcsin_pos.2 (div_pos ha hmrho)
    have hu0lt : u0 < Real.pi / 2 := by
      rw [hu0def]
      exact Real.arcsin_lt_pi_div_two.2 ((div_lt_one hmrho).2 harho)
    have hupos : 0 < u := by
      rw [hudef]
      exact Real.arcsin_pos.2 (div_pos hpos hmrho)
    have huu0 : u ≤ u0 := by
      rw [hudef, hu0def]
      exact Real.arcsin_le_arcsin (by gcongr)
    have hsinu : Real.sin u = delta / (m * rho) := by
      have hnn : (0 : ℝ) ≤ delta / (m * rho) := by positivity
      rw [hudef]
      refine Real.sin_arcsin (by linarith) ?_
      rw [div_le_one hmrho]
      linarith
    have hsinu0 : Real.sin u0 = a / (m * rho) := by
      have hnn : (0 : ℝ) ≤ a / (m * rho) := by positivity
      rw [hu0def]
      refine Real.sin_arcsin (by linarith) ?_
      rw [div_le_one hmrho]
      linarith
    have hchord := sin_chord_le hu0pos (by linarith [Real.pi_pos]) hupos.le huu0
    rw [hsinu, hsinu0] at hchord
    have hstep1 : a / (2 * u0) * u ≤ delta / 2 := by
      have hexp : u / u0 * (a / (m * rho)) = a / (2 * u0) * u * (2 / (m * rho)) := by
        field_simp
      have hexp2 : delta / (m * rho) = delta / 2 * (2 / (m * rho)) := by
        field_simp
      rw [hexp, hexp2] at hchord
      exact le_of_mul_le_mul_right hchord (by positivity)
    have hstep2 : Real.arcsin (delta / rho) ≤ m * u := by
      have hrw : delta / rho = m * Real.sin u := by
        rw [hsinu]
        field_simp
      rw [hrw]
      exact arcsin_mul_sin_le hm0.le hm1.le hupos.le (by linarith)
    have hmain := n.volume_triangleHull_diff_closedBall_ge hr0 hlt hdeltarho hout
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hmain
    simp only [annularCExt]
    rw [← hu0def]
    have hr0sq : (0 : ℝ) ≤ r0 ^ 2 / 2 := by positivity
    have hterm : r0 ^ 2 / 2 * Real.arcsin (delta / rho) ≤ r0 ^ 2 / 2 * (m * u) :=
      mul_le_mul_of_nonneg_left hstep2 hr0sq
    nlinarith [hstep1, hterm]

/-! ## Hull / interior bridge for the restricted (exterior) triangle

The disjointness available downstream is for the *open* `triangleInterior`
(`pairwise_disjoint_triangleInterior_of_outside`, `CaseIIGeometry.lean:1067`),
whereas the payment above is stated for the closed `triangleHull`.  Deleting a
closed ball preserves the equality of the two volumes, because the discrepancy
is contained in the null frontier.  **No claim is made that closed hulls are
pairwise disjoint**; the bridge converts volumes only. -/

/-- **Hull / interior bridge.**  Removing a closed ball does not change the fact
that the open triangle and the closed triangle have the same area: their
difference lies in the frontier, which is null. -/
theorem UnitNeedle.volume_triangleInterior_diff_closedBall
    (o : Plane) (n : UnitNeedle) (r0 : ℝ) :
    volume (n.triangleInterior o \ Metric.closedBall o r0) =
      volume (n.triangleHull o \ Metric.closedBall o r0) := by
  refine le_antisymm
    (measure_mono (diff_subset_diff_left (n.triangleInterior_subset_triangleHull o))) ?_
  have hsub : n.triangleHull o \ Metric.closedBall o r0 ⊆
      (n.triangleInterior o \ Metric.closedBall o r0) ∪ frontier (n.triangleHull o) := by
    rintro x ⟨hxT, hxB⟩
    by_cases hint : x ∈ interior (n.triangleHull o)
    · exact Or.inl ⟨hint, hxB⟩
    · exact Or.inr ⟨subset_closure hxT, hint⟩
  calc volume (n.triangleHull o \ Metric.closedBall o r0)
      ≤ volume ((n.triangleInterior o \ Metric.closedBall o r0) ∪
          frontier (n.triangleHull o)) := measure_mono hsub
    _ ≤ volume (n.triangleInterior o \ Metric.closedBall o r0) +
          volume (frontier (n.triangleHull o)) := measure_union_le _ _
    _ = volume (n.triangleInterior o \ Metric.closedBall o r0) := by
        rw [n.volume_frontier_triangleHull o, add_zero]

/-- The payment bound transported to the **open** restricted triangle, which is
the shape the disjoint finite sum of the exterior ledger consumes. -/
theorem UnitNeedle.annular_payment_triangleInterior
    {a r0 rho m : ℝ} {o : Plane} {n : UnitNeedle}
    (hm0 : 0 < m) (hm1 : m < 1) (ha : 0 < a) (harho : a < m * rho)
    (hr0 : 0 < r0) (hlt : r0 < rho)
    (hheight : n.height o ≤ a) (hout : n.OutsideBall rho o) :
    ENNReal.ofReal
        (annularCExt a r0 rho m * Real.arcsin (n.height o / (m * rho))) ≤
      volume (n.triangleInterior o \ Metric.closedBall o r0) := by
  rw [n.volume_triangleInterior_diff_closedBall o r0]
  exact n.annular_payment hm0 hm1 ha harho hr0 hlt hheight hout

end

end StarKakeyaLower
