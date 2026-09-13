import StarKakeyaLower.StarKakeyaSet

open Set MeasureTheory
open scoped ENNReal

namespace StarKakeyaLower

noncomputable section

private def standardTriangle : Set Plane :=
  {p | 0 ≤ p 0 ∧ 0 ≤ p 1 ∧ p 0 + p 1 ≤ 1}

private def standardTriangleProd : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

private theorem standardTriangleProd_measurable : MeasurableSet standardTriangleProd := by
  have h1 : MeasurableSet {p : ℝ × ℝ | (0 : ℝ) ≤ p.1} :=
    measurableSet_le measurable_const measurable_fst
  have h2 : MeasurableSet {p : ℝ × ℝ | (0 : ℝ) ≤ p.2} :=
    measurableSet_le measurable_const measurable_snd
  have h3 : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 ≤ (1 : ℝ)} :=
    measurableSet_le (measurable_fst.add measurable_snd) measurable_const
  simpa only [standardTriangleProd, setOf_and] using h1.inter (h2.inter h3)

private theorem integral_one_sub : ∫ x in Icc (0 : ℝ) 1, (1 - x) = 1 / 2 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 :=
    intervalIntegrable_const
  have hid : IntervalIntegrable (fun x : ℝ => x) volume 0 1 :=
    continuousOn_id.intervalIntegrable
  rw [intervalIntegral.integral_sub hconst hid, intervalIntegral.integral_const]
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ (fun y : ℝ => y ^ 2 / 2) x := by fun_prop
  have hint : IntervalIntegrable (deriv (fun y : ℝ => y ^ 2 / 2)) volume 0 1 := by
    convert hid using 1
    funext x
    simp [deriv_fun_pow]
  have hi := intervalIntegral.integral_deriv_eq_sub hderiv hint
  have hd : deriv (fun y : ℝ => y ^ 2 / 2) = fun x : ℝ => x := by
    funext x
    simp [deriv_fun_pow]
  rw [hd] at hi
  rw [hi]
  norm_num

private theorem volume_standardTriangleProd :
    (volume.prod volume) standardTriangleProd = ENNReal.ofReal (1 / 2 : ℝ) := by
  rw [Measure.prod_apply standardTriangleProd_measurable]
  have hfib : ∀ x : ℝ, volume (Prod.mk x ⁻¹' standardTriangleProd) =
      (Icc (0 : ℝ) 1).indicator (fun x => ENNReal.ofReal (1 - x)) x := by
    intro x
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem hx]
      have heq : Prod.mk x ⁻¹' standardTriangleProd = Icc 0 (1 - x) := by
        ext y
        simp only [standardTriangleProd, mem_setOf_eq, mem_preimage, mem_Icc] at hx ⊢
        constructor
        · rintro ⟨_, hy, hxy⟩
          exact ⟨hy, by linarith⟩
        · rintro ⟨hy, hy'⟩
          exact ⟨hx.1, hy, by linarith⟩
      rw [heq, Real.volume_Icc]
      ring_nf
    · simp [Set.indicator, hx]
      have heq : Prod.mk x ⁻¹' standardTriangleProd = ∅ := by
        ext y
        simp only [standardTriangleProd, mem_setOf_eq, mem_preimage, mem_empty_iff_false,
          iff_false]
        intro h
        apply hx
        exact ⟨h.1, by linarith [h.2.1, h.2.2]⟩
      simp [heq]
  simp_rw [hfib]
  rw [lintegral_indicator measurableSet_Icc]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_one_sub]
  · exact continuousOn_const.sub continuousOn_id |>.integrableOn_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact sub_nonneg.mpr hx.2

private def coordEquiv : Plane ≃ᵐ (ℝ × ℝ) :=
  (MeasurableEquiv.toLp 2 ((Fin 2) → ℝ)).symm.trans
    (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))

private theorem coordEquiv_apply (p : Plane) : coordEquiv p = (p 0, p 1) := rfl

private theorem coord_measurePreserving :
    MeasurePreserving coordEquiv volume (volume.prod volume) := by
  have hLp := PiLp.volume_preserving_toLp (Fin 2)
  have hLp' := hLp.symm (MeasurableEquiv.toLp 2 ((Fin 2) → ℝ))
  have hpi := measurePreserving_piFinTwo (fun _ : Fin 2 => (volume : Measure ℝ))
  rw [← volume_pi] at hpi
  exact hLp'.trans hpi

private theorem volume_standardTriangle :
    volume standardTriangle = ENNReal.ofReal (1 / 2 : ℝ) := by
  have hpre : coordEquiv ⁻¹' standardTriangleProd = standardTriangle := by
    ext p
    rfl
  rw [← hpre, coord_measurePreserving.measure_preimage
    standardTriangleProd_measurable.nullMeasurableSet, volume_standardTriangleProd]

private theorem standardTriangle_isCompact : IsCompact standardTriangle := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · have hc0 : Continuous (fun p : Plane => p 0) :=
      PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
    have hc1 : Continuous (fun p : Plane => p 1) :=
      PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1
    have h0 : IsClosed {p : Plane | (0 : ℝ) ≤ p 0} :=
      isClosed_le continuous_const hc0
    have h1 : IsClosed {p : Plane | (0 : ℝ) ≤ p 1} :=
      isClosed_le continuous_const hc1
    have hsum : IsClosed {p : Plane | p 0 + p 1 ≤ (1 : ℝ)} :=
      isClosed_le (hc0.add hc1) continuous_const
    exact h0.inter (h1.inter hsum)
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨2, ?_⟩
    intro p hp
    rw [EuclideanSpace.norm_eq]
    simp only [Fin.sum_univ_two, Real.norm_eq_abs]
    have h0 : p 0 ≤ 1 := by linarith [hp.2.1, hp.2.2]
    have h1 : p 1 ≤ 1 := by linarith [hp.1, hp.2.2]
    have ha0 : |p 0| = p 0 := abs_of_nonneg hp.1
    have ha1 : |p 1| = p 1 := abs_of_nonneg hp.2.1
    rw [ha0, ha1]
    have hsqrt := Real.sq_sqrt (show 0 ≤ (p 0) ^ 2 + (p 1) ^ 2 by positivity)
    have hsqrt0 := Real.sqrt_nonneg ((p 0) ^ 2 + (p 1) ^ 2)
    have hs0 : (p 0) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h0) (by linarith [hp.1] : 0 ≤ 1 + p 0)]
    have hs1 : (p 1) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) (by linarith [hp.2.1] : 0 ≤ 1 + p 1)]
    nlinarith

private def triangleLinearMap (o : Plane) (n : UnitNeedle) : Plane →ₗ[ℝ] Plane where
  toFun p := p 0 • (n.right - n.left) + p 1 • (o - n.left)
  map_add' p q := by ext i; simp; ring
  map_smul' c p := by ext i; simp; ring

private theorem triangleLinearMap_apply (o : Plane) (n : UnitNeedle) (p : Plane) :
    triangleLinearMap o n p = p 0 • (n.right - n.left) + p 1 • (o - n.left) := rfl

private theorem det_triangleLinearMap (o : Plane) (n : UnitNeedle) :
    |LinearMap.det (triangleLinearMap o n)| = n.height o := by
  rw [← LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin 2)), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, triangleLinearMap, PiLp.basisFun]
  rw [UnitNeedle.height]
  change |(n.right 0 - n.left 0) * (o 1 - n.left 1) -
    (o 0 - n.left 0) * (n.right 1 - n.left 1)| =
    |(n.right 0 - n.left 0) * (o 1 - n.left 1) -
    (n.right 1 - n.left 1) * (o 0 - n.left 0)|
  congr 1
  ring

private theorem triangleHull_eq_affine_image (o : Plane) (n : UnitNeedle) :
    n.triangleHull o = (fun p => n.left + triangleLinearMap o n p) '' standardTriangle := by
  ext y
  constructor
  · intro hy
    simp only [UnitNeedle.triangleHull, mem_iUnion] at hy
    obtain ⟨x, hx, hy⟩ := hy
    change x ∈ segment ℝ n.left n.right at hx
    rw [segment_eq_image' ℝ n.left n.right] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    rw [segment_eq_image ℝ o (n.left + s • (n.right - n.left))] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    let p : Plane := WithLp.toLp 2 ![t * s, 1 - t]
    refine ⟨p, ?_, ?_⟩
    · exact ⟨mul_nonneg ht.1 hs.1, sub_nonneg.mpr ht.2, by
        change t * s + (1 - t) ≤ 1
        nlinarith [mul_le_mul_of_nonneg_left hs.2 ht.1]⟩
    · ext i
      fin_cases i <;> simp [p, triangleLinearMap] <;> ring
  · rintro ⟨p, hp, rfl⟩
    change 0 ≤ p 0 ∧ 0 ≤ p 1 ∧ p 0 + p 1 ≤ 1 at hp
    have ht : 0 ≤ 1 - p 1 ∧ 1 - p 1 ≤ 1 := ⟨by linarith [hp.2.2], by linarith [hp.2.1]⟩
    by_cases hzero : 1 - p 1 = 0
    · have hp0 : p 0 = 0 := by linarith [hp.1, hp.2.2]
      have hp1 : p 1 = 1 := by linarith
      have hleft : n.left ∈ n.carrier := by
        change n.left ∈ segment ℝ n.left n.right
        rw [segment_eq_image' ℝ]
        exact ⟨0, by simp, by simp⟩
      simp only [UnitNeedle.triangleHull, mem_iUnion]
      refine ⟨n.left, hleft, ?_⟩
      rw [segment_eq_image ℝ]
      refine ⟨0, by simp, ?_⟩
      ext i
      simp [triangleLinearMap, hp1, hp0]
    · let s : ℝ := p 0 / (1 - p 1)
      have hs : s ∈ Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg hp.1 ht.1
        · apply (div_le_one (lt_of_le_of_ne ht.1 (Ne.symm hzero))).mpr
          linarith [hp.2.2]
      have hx : n.left + s • (n.right - n.left) ∈ n.carrier := by
        rw [UnitNeedle.carrier, segment_eq_image' ℝ]
        exact ⟨s, hs, rfl⟩
      simp only [UnitNeedle.triangleHull, mem_iUnion]
      refine ⟨n.left + s • (n.right - n.left), hx, ?_⟩
      rw [segment_eq_image ℝ]
      refine ⟨1 - p 1, ht, ?_⟩
      ext i
      simp [triangleLinearMap, s]
      field_simp [hzero]
      ring

private theorem volume_triangleHull (o : Plane) (n : UnitNeedle) :
    volume (n.triangleHull o) = ENNReal.ofReal (n.height o / 2) := by
  let f := triangleLinearMap o n
  let S := f '' standardTriangle
  have hScompact : IsCompact S := standardTriangle_isCompact.image
    f.continuous_of_finiteDimensional
  have haffCompact : IsCompact ((fun x : Plane => n.left + x) '' S) :=
    hScompact.image (continuous_const.add continuous_id)
  have hpre : (fun x : Plane => n.left + x) ⁻¹' ((fun x : Plane => n.left + x) '' S) = S := by
    ext x
    simp
  have htrans := (measurePreserving_add_left volume n.left).measure_preimage
    haffCompact.nullMeasurableSet
  rw [hpre] at htrans
  rw [triangleHull_eq_affine_image]
  have himage : (fun p : Plane => n.left + f p) '' standardTriangle =
      (fun x : Plane => n.left + x) '' S := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨f p, ⟨p, hp, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
  rw [himage, ← htrans]
  -- `addHaar_image_linearMap` also covers the singular case: when the
  -- determinant is zero, its right-hand side (and hence the image volume) is zero.
  rw [Measure.addHaar_image_linearMap, det_triangleLinearMap,
    volume_standardTriangle]
  rw [← ENNReal.ofReal_mul (UnitNeedle.height_nonneg o n)]
  congr 1
  ring

private theorem standardTriangle_convex : Convex ℝ standardTriangle := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ (a • x + b • y) 0 ∧ 0 ≤ (a • x + b • y) 1 ∧
    (a • x + b • y) 0 + (a • x + b • y) 1 ≤ 1
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  constructor
  · exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
  constructor
  · exact add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1)
  · calc
      a * x 0 + b * y 0 + (a * x 1 + b * y 1) =
          a * (x 0 + x 1) + b * (y 0 + y 1) := by ring
      _ ≤ a * 1 + b * 1 := add_le_add
        (mul_le_mul_of_nonneg_left hx.2.2 ha)
        (mul_le_mul_of_nonneg_left hy.2.2 hb)
      _ = 1 := by linarith

/-- A filled needle triangle is compact. -/
theorem UnitNeedle.triangleHull_isCompact (o : Plane) (n : UnitNeedle) :
    IsCompact (n.triangleHull o) := by
  rw [triangleHull_eq_affine_image]
  exact standardTriangle_isCompact.image
    ((continuous_const.add (triangleLinearMap o n).continuous_of_finiteDimensional))

/-- A filled needle triangle is convex. -/
theorem UnitNeedle.triangleHull_convex (o : Plane) (n : UnitNeedle) :
    Convex ℝ (n.triangleHull o) := by
  rw [triangleHull_eq_affine_image]
  have h := (standardTriangle_convex.linear_image (triangleLinearMap o n)).translate n.left
  convert h using 1
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨_, ⟨p, hp, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩

/-- The ordinary topological interior of a complete unit-base triangle has
exactly half its determinant height.  This is the area identity used by the
selected *open* triangles in Case II. -/
theorem UnitNeedle.volume_triangleInterior (o : Plane) (n : UnitNeedle) :
    volume (interior (n.triangleHull o)) = ENNReal.ofReal (n.height o / 2) := by
  have hfrontier : volume (frontier (n.triangleHull o)) = 0 :=
    (n.triangleHull_convex o).addHaar_frontier volume
  have hae : interior (n.triangleHull o) =ᶠ[ae volume] n.triangleHull o := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · rw [show interior (n.triangleHull o) \ n.triangleHull o = ∅ by
        exact diff_eq_empty.mpr interior_subset]
      exact measure_empty
    · apply measure_mono_null _ hfrontier
      intro x hx
      exact ⟨subset_closure hx.1, hx.2⟩
  rw [measure_congr hae, volume_triangleHull]

/-- The boundary of a filled needle triangle is planar-null. -/
theorem UnitNeedle.volume_frontier_triangleHull (o : Plane) (n : UnitNeedle) :
    volume (frontier (n.triangleHull o)) = 0 :=
  (n.triangleHull_convex o).addHaar_frontier volume

/-- The filled triangle on a unit needle has outer area equal to half its
 determinant height. -/
theorem triangleAreaBridge : StarShapedKakeya.TriangleAreaBridge := by
  intro o n
  rw [Measure.toOuterMeasure_apply, volume_triangleHull]

end

end StarKakeyaLower
