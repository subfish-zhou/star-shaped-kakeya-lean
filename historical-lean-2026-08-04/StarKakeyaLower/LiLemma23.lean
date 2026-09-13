import StarKakeyaLower.CaseIAssemblyConditional

open Set MeasureTheory
open scoped ENNReal

namespace StarKakeyaLower

noncomputable section

private abbrev Li23Plane := EuclideanSpace ℝ (Fin 2)

private def li23e0 : Li23Plane := EuclideanSpace.single 0 1
private def li23e1 : Li23Plane := EuclideanSpace.single 1 1

/-- Barycentric/base-coordinate parametrisation of a support triangle, written
in the Euclidean model in order to use the finite-dimensional area formula. -/
private def li23Param (α δ : ℝ) (p : Li23Plane) : Li23Plane :=
  (p 0 * (-δ * Real.sin α + p 1 * Real.cos α)) • li23e0 +
  (p 0 * ( δ * Real.cos α + p 1 * Real.sin α)) • li23e1

private def li23Domain (r δ c : ℝ) : Set Li23Plane :=
  {p | p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 ∈ Icc (c - 1 / 2) (c + 1 / 2) ∧
    r ^ 2 ≤ (p 0) ^ 2 * (δ ^ 2 + (p 1) ^ 2)}

private theorem measurableSet_li23Domain (r δ c : ℝ) :
    MeasurableSet (li23Domain r δ c) := by
  have h0 : Continuous (fun p : Li23Plane => p 0) :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
  have h1 : Continuous (fun p : Li23Plane => p 1) :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1
  rw [li23Domain]
  exact (measurableSet_Icc.preimage h0.measurable).inter
    ((measurableSet_Icc.preimage h1.measurable).inter
      (measurableSet_le measurable_const
        ((h0.pow 2).mul (continuous_const.add (h1.pow 2))).measurable))

private theorem li23Param_hasFDerivAt (α δ : ℝ) (p : Li23Plane) :
    HasFDerivAt (li23Param α δ) (fderiv ℝ (li23Param α δ) p) p := by
  have h0 := PiLp.hasFDerivAt_apply (𝕜 := ℝ)
    (E := fun _ : Fin 2 => ℝ) 2 p (0 : Fin 2)
  have h1 := PiLp.hasFDerivAt_apply (𝕜 := ℝ)
    (E := fun _ : Fin 2 => ℝ) 2 p (1 : Fin 2)
  have ha := (h0.mul ((hasFDerivAt_const (-δ * Real.sin α) p).add
    (h1.mul_const (Real.cos α)))).smul_const li23e0
  have hb := (h0.mul ((hasFDerivAt_const (δ * Real.cos α) p).add
    (h1.mul_const (Real.sin α)))).smul_const li23e1
  have h := ha.add hb
  convert h using 1
  exact h.fderiv

private theorem li23Param_abs_det (α δ : ℝ) (p : Li23Plane) :
    |(fderiv ℝ (li23Param α δ) p).det| = |δ| * |p 0| := by
  have h0 := PiLp.hasFDerivAt_apply (𝕜 := ℝ)
    (E := fun _ : Fin 2 => ℝ) 2 p (0 : Fin 2)
  have h1 := PiLp.hasFDerivAt_apply (𝕜 := ℝ)
    (E := fun _ : Fin 2 => ℝ) 2 p (1 : Fin 2)
  have ha := (h0.mul ((hasFDerivAt_const (-δ * Real.sin α) p).add
    (h1.mul_const (Real.cos α)))).smul_const li23e0
  have hb := (h0.mul ((hasFDerivAt_const (δ * Real.cos α) p).add
    (h1.mul_const (Real.sin α)))).smul_const li23e1
  have h := ha.add hb
  let L : Li23Plane →L[ℝ] Li23Plane :=
    (((p 0 • (Real.cos α • PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1) +
      (-δ * Real.sin α + p 1 * Real.cos α) •
        PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0) : Li23Plane →L[ℝ] ℝ).smulRight li23e0 +
    ((p 0 • (Real.sin α • PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1) +
      (δ * Real.cos α + p 1 * Real.sin α) •
        PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0) : Li23Plane →L[ℝ] ℝ).smulRight li23e1)
  have h' : HasFDerivAt (li23Param α δ) L p := by
    convert h using 1 <;> simp [L]
  rw [h'.fderiv]
  change |LinearMap.det L.toLinearMap| = _
  rw [← LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin 2)), Matrix.det_fin_two]
  simp [L, LinearMap.toMatrix_apply, PiLp.basisFun, li23e0, li23e1]
  rw [show (-(δ * Real.sin α) + p 1 * Real.cos α) *
        (p 0 * Real.sin α) -
      (p 0 * Real.cos α) * (δ * Real.cos α + p 1 * Real.sin α) =
      -(δ * p 0) by
    nth_rewrite 1 [← mul_one (δ*p 0)]
    rw [← Real.sin_sq_add_cos_sq α]
    ring]
  rw [abs_neg, abs_mul]

private theorem li23Param_apply (α δ lam x : ℝ) :
    li23Param α δ (coordinatePlaneEquiv (lam, x)) =
      coordinatePlaneEquiv
        (scaleCoordinatePlane lam (supportPoint α δ x)) := by
  ext i
  fin_cases i <;>
    simp [li23Param, li23e0, li23e1, coordinatePlaneEquiv,
      scaleCoordinatePlane, supportPoint, addCoordinatePlane,
      unitDirection, unitNormal] <;> ring

private theorem li23Param_injective_of_pos
    {α δ : ℝ} (hδ : 0 < δ) :
    Set.InjOn (li23Param α δ) {p : Li23Plane | 0 < p 0} := by
  intro p hp q hq heq
  have h0 := congrArg (fun z : Li23Plane =>
    -Real.sin α * z 0 + Real.cos α * z 1) heq
  have h1 := congrArg (fun z : Li23Plane =>
    Real.cos α * z 0 + Real.sin α * z 1) heq
  simp only [li23Param, PiLp.add_apply, PiLp.smul_apply, li23e0, li23e1,
    EuclideanSpace.single_apply] at h0 h1
  simp at h0 h1
  have htrig := Real.sin_sq_add_cos_sq α
  have hlam : p 0 = q 0 := by
    have hmul : δ * p 0 = δ * q 0 := by
      linear_combination h0 - δ * (p 0 - q 0) * htrig
    exact mul_left_cancel₀ (ne_of_gt hδ) hmul
  have hx : p 1 = q 1 := by
    have hprod : p 0 * p 1 = q 0 * q 1 := by
      linear_combination h1 - (p 0 * p 1 - q 0 * q 1) * htrig
    rw [← hlam] at hprod
    exact mul_left_cancel₀ (ne_of_gt hp) hprod
  ext i
  fin_cases i
  · exact hlam
  · exact hx

private theorem li23Domain_first_pos
    {r δ c : ℝ} (hr : 0 < r) {p : Li23Plane}
    (hp : p ∈ li23Domain r δ c) : 0 < p 0 := by
  rw [li23Domain] at hp
  rcases hp with ⟨hp0, -, hrad⟩
  have hne : p 0 ≠ 0 := by
    intro h
    rw [h] at hrad
    nlinarith
  exact lt_of_le_of_ne hp0.1 (Ne.symm hne)

private theorem li23Param_injective_on_domain
    {α r δ c : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    Set.InjOn (li23Param α δ) (li23Domain r δ c) := by
  exact (li23Param_injective_of_pos hδ).mono
    (fun _ hp => li23Domain_first_pos hr hp)

private theorem li23Param_image_domain
    {α r δ c : ℝ} :
    li23Param α δ '' li23Domain r δ c =
      coordinatePlaneEquiv ''
        (supportNeedleTriangle α δ c \ originOpenDisk r) := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [li23Domain] at hp
    refine ⟨scaleCoordinatePlane (p 0) (supportPoint α δ (p 1)), ?_, ?_⟩
    · refine ⟨⟨p 0, hp.1, p 1, hp.2.1, rfl⟩, ?_⟩
      simp only [originOpenDisk, mem_setOf_eq]
      simp only [scaleCoordinatePlane, supportPoint, addCoordinatePlane,
        unitDirection, unitNormal]
      have ht := Real.sin_sq_add_cos_sq α
      nlinarith [hp.2.2]
    · exact li23Param_apply α δ (p 0) (p 1) |>.symm
  · rintro ⟨w, ⟨⟨lam, hlam, x, hx, rfl⟩, hout⟩, rfl⟩
    refine ⟨coordinatePlaneEquiv (lam, x), ?_, li23Param_apply α δ lam x⟩
    rw [li23Domain]
    refine ⟨by simpa using hlam, by simpa [coordinatePlaneEquiv] using hx, ?_⟩
    simp only [coordinatePlaneEquiv_apply_zero, coordinatePlaneEquiv_apply_one]
    simp only [originOpenDisk, mem_setOf_eq, scaleCoordinatePlane,
      supportPoint, addCoordinatePlane, unitDirection, unitNormal] at hout
    have ht := Real.sin_sq_add_cos_sq α
    nlinarith

private theorem li23_area_formula
    {α r δ c : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    volume.real (coordinatePlaneEquiv ''
      (supportNeedleTriangle α δ c \ originOpenDisk r)) =
      ∫ p in li23Domain r δ c, δ * p 0 := by
  rw [← li23Param_image_domain]
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume
    (measurableSet_li23Domain r δ c)
    (fun p _ => (li23Param_hasFDerivAt α δ p).hasFDerivWithinAt)
    (li23Param_injective_on_domain hr hδ) (fun _ => (1 : ℝ))
  calc
    volume.real (li23Param α δ '' li23Domain r δ c) =
        ∫ p in li23Domain r δ c, δ * |p 0| := by
      simpa [li23Param_abs_det, abs_of_pos hδ] using hcv
    _ = ∫ p in li23Domain r δ c, δ * p 0 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_li23Domain r δ c)] with p hp
      rw [abs_of_nonneg hp.1.1]

private def li23ProdDomain (r δ c : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc (c - 1 / 2) (c + 1 / 2) ∧
    r ^ 2 ≤ z.1 ^ 2 * (δ ^ 2 + z.2 ^ 2)}

private def li23ProdIntegrand (r δ c : ℝ) (z : ℝ × ℝ) : ℝ :=
  (li23ProdDomain r δ c).indicator (fun z => δ * z.1) z

private theorem measurableSet_li23ProdDomain (r δ c : ℝ) :
    MeasurableSet (li23ProdDomain r δ c) := by
  have h0 : Continuous (fun z : ℝ × ℝ => z.1) := continuous_fst
  have h1 : Continuous (fun z : ℝ × ℝ => z.2) := continuous_snd
  rw [li23ProdDomain]
  exact (measurableSet_Icc.preimage h0.measurable).inter
    ((measurableSet_Icc.preimage h1.measurable).inter
      (measurableSet_le measurable_const
        ((h0.pow 2).mul (continuous_const.add (h1.pow 2))).measurable))

private theorem integrable_li23ProdIntegrand (r δ c : ℝ) :
    Integrable (li23ProdIntegrand r δ c) (volume.prod volume) := by
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (c - 1 / 2) (c + 1 / 2)
  have hcont : Continuous (fun z : ℝ × ℝ => δ * z.1) :=
    continuous_const.mul continuous_fst
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hintK : IntegrableOn (fun z : ℝ × ℝ => δ * z.1) K
      (volume.prod volume) := hcont.continuousOn.integrableOn_compact hK
  have hsub : li23ProdDomain r δ c ⊆ K := fun _ hz => ⟨hz.1, hz.2.1⟩
  unfold li23ProdIntegrand
  exact (integrable_indicator_iff
    (measurableSet_li23ProdDomain r δ c)).2 (hintK.mono_set hsub)

/-- Change of variables followed by Tonelli--Fubini, in the `(x,λ)` order used
for the one-dimensional centred-interval comparison. -/
private theorem li23_fubini_formula
    {α r δ c : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    volume.real (coordinatePlaneEquiv ''
      (supportNeedleTriangle α δ c \ originOpenDisk r)) =
      ∫ x : ℝ, ∫ lam : ℝ,
        li23ProdIntegrand r δ c (lam, x) := by
  rw [li23_area_formula hr hδ]
  have hcomp := coordinatePlaneEquiv_measurePreserving.integral_comp
    coordinatePlaneEquiv.measurableEmbedding
    ((li23Domain r δ c).indicator (fun p : Li23Plane => δ * p 0))
  have hset :
      (∫ p in li23Domain r δ c, δ * p 0) =
        ∫ p : Li23Plane,
          (li23Domain r δ c).indicator (fun p => δ * p 0) p := by
    rw [integral_indicator (measurableSet_li23Domain r δ c)]
  rw [hset, ← hcomp]
  have hprod := integral_prod_symm (li23ProdIntegrand r δ c)
    (integrable_li23ProdIntegrand r δ c)
  calc
    (∫ z : ℝ × ℝ,
        (li23Domain r δ c).indicator (fun p => δ * p 0)
          (coordinatePlaneEquiv z)) =
        ∫ z : ℝ × ℝ, li23ProdIntegrand r δ c z := by
      congr 1
    _ = ∫ x : ℝ, ∫ lam : ℝ,
        li23ProdIntegrand r δ c (lam, x) := hprod

/-! ## The remaining one-dimensional rearrangement -/

/-- The vertical fibre area.  This normalization includes the Jacobian `δ`. -/
private def li23Phi (r δ x : ℝ) : ℝ :=
  δ / 2 * max 0 (1 - r ^ 2 / (δ ^ 2 + x ^ 2))

private theorem li23_inner_integral
    {r δ c x : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    (∫ lam : ℝ, li23ProdIntegrand r δ c (lam, x)) =
      (Icc (c - 1 / 2) (c + 1 / 2)).indicator (li23Phi r δ) x := by
  by_cases hx : x ∈ Icc (c - 1 / 2) (c + 1 / 2)
  · rw [Set.indicator_of_mem hx]
    let A := δ ^ 2 + x ^ 2
    have hA : 0 < A := by dsimp [A]; nlinarith [sq_pos_of_pos hδ]
    have hs : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
    have hs2 : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA.le
    by_cases hAr : r ^ 2 ≤ A
    · have ht0 : 0 ≤ r / Real.sqrt A := div_nonneg hr.le hs.le
      have ht1 : r / Real.sqrt A ≤ 1 := by
        apply (div_le_one hs).2
        nlinarith [sq_nonneg (Real.sqrt A - r)]
      have hslice : (fun lam => li23ProdIntegrand r δ c (lam, x)) =
          (Icc (r / Real.sqrt A) 1).indicator (fun lam => δ * lam) := by
        funext lam
        unfold li23ProdIntegrand
        by_cases hlam : lam ∈ Icc (r / Real.sqrt A) 1
        · have hz : (lam, x) ∈ li23ProdDomain r δ c := by
            refine ⟨⟨ht0.trans hlam.1, hlam.2⟩, hx, ?_⟩
            have hm := mul_self_le_mul_self (div_nonneg hr.le hs.le) hlam.1
            field_simp [ne_of_gt hs] at hm
            nlinarith
          simp [Set.indicator, hz, hlam]
        · have hz : (lam, x) ∉ li23ProdDomain r δ c := by
            intro hz
            apply hlam
            refine ⟨?_, hz.1.2⟩
            have hm : r ^ 2 / A ≤ lam ^ 2 :=
              (div_le_iff₀ hA).2 (by nlinarith [hz.2.2])
            have heq : (r / Real.sqrt A)^2 = r^2/A := by
              field_simp [ne_of_gt hA, ne_of_gt hs]
              nlinarith
            rw [← heq] at hm
            by_contra hlt
            have hp : 0 < (r / Real.sqrt A + lam) *
                (r / Real.sqrt A - lam) := mul_pos (add_pos_of_pos_of_nonneg
                  (div_pos hr hs) hz.1.1) (sub_pos.mpr (lt_of_not_ge hlt))
            nlinarith
          simp [Set.indicator, hz, hlam]
      change (∫ lam : ℝ, li23ProdIntegrand r δ c (lam, x)) = _
      rw [hslice, MeasureTheory.integral_indicator measurableSet_Icc,
        MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht1]
      have hanti : ∫ lam in r / Real.sqrt A..1, δ * lam =
          δ / 2 * (1 - r ^ 2 / A) := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun y : ℝ => δ / 2 * y^2)]
        · field_simp [ne_of_gt hA, ne_of_gt hs]
          nlinarith
        · intro y hy
          convert (((hasDerivAt_const y (δ/2)).mul ((hasDerivAt_id y).pow 2))) using 1
          simp
          ring
        · exact (continuous_const.mul continuous_id).intervalIntegrable _ _
      rw [hanti]
      unfold li23Phi
      rw [max_eq_right]
      exact sub_nonneg.mpr (div_le_one hA |>.2 hAr)
    · have hnone : ∀ lam : ℝ, li23ProdIntegrand r δ c (lam, x) = 0 := by
        intro lam
        have hz : (lam, x) ∉ li23ProdDomain r δ c := by
          intro hz
          apply hAr
          have hrad := hz.2.2
          have hlam := hz.1
          have hlam2 : lam^2 ≤ 1 := by
            simpa [pow_two] using (mul_self_le_mul_self hlam.1 hlam.2)
          have hmul : lam^2 * (δ^2+x^2) ≤ δ^2+x^2 := by
            nlinarith [mul_nonneg (sub_nonneg.mpr hlam2) hA.le]
          nlinarith
        simp [li23ProdIntegrand, Set.indicator, hz]
      simp_rw [hnone]
      simp only [integral_zero]
      unfold li23Phi
      rw [max_eq_left]
      · simp
      · exact sub_nonpos.mpr ((one_lt_div hA).2 (lt_of_not_ge hAr) |>.le)
  · have hrhs : (Icc (c - 1 / 2) (c + 1 / 2)).indicator
        (li23Phi r δ) x = 0 := by simp only [Set.indicator, hx, if_false]
    rw [hrhs]
    have hnone : ∀ lam : ℝ, li23ProdIntegrand r δ c (lam, x) = 0 := by
      intro lam
      have hz : (lam, x) ∉ li23ProdDomain r δ c := fun hz => hx hz.2.1
      simp [li23ProdIntegrand, Set.indicator, hz]
    simp_rw [hnone]
    simp

private theorem li23Phi_continuous (r δ : ℝ) (hδ : 0 < δ) :
    Continuous (li23Phi r δ) := by
  unfold li23Phi
  apply Continuous.mul continuous_const
  apply Continuous.max continuous_const
  apply Continuous.sub continuous_const
  apply Continuous.div continuous_const (continuous_const.add (continuous_id.pow 2))
  intro x
  dsimp
  nlinarith [sq_pos_of_pos hδ, sq_nonneg x]

@[simp] private theorem li23Phi_neg (r δ x : ℝ) :
    li23Phi r δ (-x) = li23Phi r δ x := by
  simp [li23Phi]

private theorem li23Phi_mono_sq {r δ x y : ℝ} (hδ : 0 < δ)
    (hxy : x^2 ≤ y^2) : li23Phi r δ x ≤ li23Phi r δ y := by
  unfold li23Phi
  apply mul_le_mul_of_nonneg_left
  · exact max_le_max_left _ (sub_le_sub_left
      (div_le_div_of_nonneg_left (sq_nonneg r)
        (by nlinarith [sq_pos_of_pos hδ, sq_nonneg x]) (by nlinarith)) _)
  · positivity

private def li23Window (r δ c : ℝ) : ℝ :=
  ∫ x in c - 1/2..c + 1/2, li23Phi r δ x

private theorem li23Window_even (r δ c : ℝ) :
    li23Window r δ (-c) = li23Window r δ c := by
  unfold li23Window
  calc
    (∫ x in -c-1/2..-c+1/2, li23Phi r δ x) =
        ∫ x in -(c+1/2)..-(c-1/2), li23Phi r δ x := by congr 1 <;> ring
    _ = ∫ x in c-1/2..c+1/2, li23Phi r δ (-x) := by
      rw [intervalIntegral.integral_comp_neg]
    _ = ∫ x in c-1/2..c+1/2, li23Phi r δ x := by
      apply intervalIntegral.integral_congr
      intro x hx
      simp

private theorem li23Window_min (r δ c : ℝ) (hδ : 0 < δ) :
    li23Window r δ 0 ≤ li23Window r δ c := by
  let P : ℝ → ℝ := fun u => ∫ x in 0..u, li23Phi r δ x
  have hP : ∀ u, HasDerivAt P (li23Phi r δ u) u := by
    intro u
    apply intervalIntegral.integral_hasDerivAt_right
    · exact (li23Phi_continuous r δ hδ).intervalIntegrable _ _
    · exact (li23Phi_continuous r δ hδ).stronglyMeasurable.stronglyMeasurableAtFilter
    · exact (li23Phi_continuous r δ hδ).continuousAt
  have hwin : li23Window r δ = fun c => P (c+1/2) - P (c-1/2) := by
    funext c
    unfold li23Window P
    rw [← intervalIntegral.integral_add_adjacent_intervals
      ((li23Phi_continuous r δ hδ).intervalIntegrable (c-1/2) 0)
      ((li23Phi_continuous r δ hδ).intervalIntegrable 0 (c+1/2))]
    rw [intervalIntegral.integral_symm]
    ring
  have hderiv : ∀ c, HasDerivAt (li23Window r δ)
      (li23Phi r δ (c+1/2) - li23Phi r δ (c-1/2)) c := by
    intro c
    rw [hwin]
    convert ((hP (c+1/2)).comp c ((hasDerivAt_id c).add_const (1/2))).sub
      ((hP (c-1/2)).comp c ((hasDerivAt_id c).sub_const (1/2))) using 1 <;> simp
  have hmono : MonotoneOn (li23Window r δ) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (fun x hx => (hderiv x).continuousAt.continuousWithinAt)
    · exact fun x hx => (hderiv x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hderiv x).deriv]
      have hx0 : 0 ≤ x := interior_subset hx
      exact sub_nonneg.mpr (li23Phi_mono_sq hδ (by nlinarith))
  by_cases hc : 0 ≤ c
  · exact hmono (by simp) hc hc
  · rw [← li23Window_even r δ c]
    exact hmono (by simp) (by simp; linarith) (by simp; linarith)

private theorem li23_area_as_window
    {α r δ c : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    volume.real (coordinatePlaneEquiv ''
      (supportNeedleTriangle α δ c \ originOpenDisk r)) = li23Window r δ c := by
  rw [li23_fubini_formula hr hδ]
  simp_rw [li23_inner_integral hr hδ]
  rw [MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : c-1/2 ≤ c+1/2)]
  rfl

private theorem li23Window_centered
    {r δ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1/2) (hδ : 0 < δ) (hδr : δ < r) :
    li23Window r δ 0 = liCenteredExteriorArea r δ := by
  let q := Real.sqrt (r^2-δ^2)
  have hrad : 0 < r^2-δ^2 := by nlinarith
  have hq : 0 < q := Real.sqrt_pos.2 hrad
  have hq2 : q^2 = r^2-δ^2 := Real.sq_sqrt hrad.le
  have hq1 : q ≤ 1/2 := by
    have : q ≤ r := by nlinarith [sq_nonneg (r-q)]
    linarith
  have hphi0 : ∀ x, x ∈ Icc (-q) q → li23Phi r δ x = 0 := by
    intro x hx
    unfold li23Phi
    rw [max_eq_left]
    · simp
    · apply sub_nonpos.mpr
      apply (one_le_div (by positivity)).2
      have hxx : x^2 ≤ q^2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hx.2)
          (sub_nonneg.mpr (by linarith [hx.1] : 0 ≤ x+q))]
      nlinarith
  have hphiform : ∀ x, q ≤ x → li23Phi r δ x =
      δ/2 * (1-r^2/(δ^2+x^2)) := by
    intro x hx
    unfold li23Phi
    rw [max_eq_right]
    apply sub_nonneg.mpr
    apply (div_le_one (by positivity)).2
    nlinarith [sq_nonneg (x-q)]
  let B : ℝ → ℝ := fun x => δ/2*x-r^2/2*Real.arctan (x/δ)
  have hB : ∀ x, HasDerivAt B (δ/2*(1-r^2/(δ^2+x^2))) x := by
    intro x
    have ha := Real.hasDerivAt_arctan (x/δ) |>.comp x
      ((hasDerivAt_id x).div_const δ)
    dsimp [B]
    convert ((hasDerivAt_const x (δ/2)).mul (hasDerivAt_id x)).sub
      (ha.const_mul (r^2/2)) using 1 <;> field_simp [ne_of_gt hδ] <;> ring
  have hright : (∫ x in q..1/2, li23Phi r δ x) = B (1/2)-B q := by
    rw [intervalIntegral.integral_congr (fun x hx => hphiform x (by
      rw [uIcc_of_le hq1] at hx
      exact hx.1))]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      exact hB x
    · have hden : ∀ x : ℝ, δ ^ 2 + x ^ 2 ≠ 0 := by
        intro x hx
        have hd2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
        nlinarith [sq_nonneg x]
      have hc : Continuous (fun y : ℝ =>
          δ / 2 * (1 - r ^ 2 / (δ ^ 2 + y ^ 2))) := by
        exact continuous_const.mul
          (continuous_const.sub
            (continuous_const.div
              (continuous_const.add (continuous_id.pow 2)) hden))
      exact hc.intervalIntegrable _ _
  have hleft : (∫ x in -(1/2)..-q, li23Phi r δ x) =
      ∫ x in q..1/2, li23Phi r δ x := by
    rw [← intervalIntegral.integral_comp_neg (li23Phi r δ)]
    · apply intervalIntegral.integral_congr
      intro x hx
      simp
  have hsplit : li23Window r δ 0 = 2 * (B (1/2)-B q) := by
    unfold li23Window
    rw [show (0:ℝ)-1/2 = -(1/2) by ring, show (0:ℝ)+1/2=1/2 by ring]
    have hadd1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((li23Phi_continuous r δ hδ).intervalIntegrable (-(1/2)) (-q))
      ((li23Phi_continuous r δ hδ).intervalIntegrable (-q) q)
    have hadd2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((li23Phi_continuous r δ hδ).intervalIntegrable (-(1/2)) q)
      ((li23Phi_continuous r δ hδ).intervalIntegrable q (1/2))
    have hmid : (∫ x in -q..q, li23Phi r δ x) = 0 := by
      rw [intervalIntegral.integral_congr (fun x hx => hphi0 x (by
        rw [uIcc_of_le (by linarith [hq])] at hx
        exact hx))]
      simp
    rw [← hadd2, ← hadd1, hmid, add_zero, hleft, hright]
    ring
  rw [hsplit]
  have hatan1 : Real.arctan ((1/2)/δ) = Real.pi/2-Real.arctan (2*δ) := by
    rw [show (1/2)/δ = (2*δ)⁻¹ by field_simp [ne_of_gt hδ]]
    exact Real.arctan_inv_of_pos (by positivity)
  have hasin : Real.arcsin (δ/r) = Real.arctan (δ/q) := by
    rw [Real.arcsin_eq_arctan]
    · congr 1
      have hsqrt : Real.sqrt (1-(δ/r)^2) = q/r := by
        have hs0 := Real.sqrt_nonneg (1-(δ/r)^2)
        have hs2 := Real.sq_sqrt (show 0 ≤ 1-(δ/r)^2 by
          have hx0 : 0 ≤ δ / r := div_nonneg hδ.le hr.le
          have hx1 : δ / r ≤ 1 := (div_le_one hr).2 hδr.le
          nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)])
        have hb0 : 0 ≤ q/r := div_nonneg hq.le hr.le
        have heq : (Real.sqrt (1-(δ/r)^2))^2 = (q/r)^2 := by
          rw [hs2]
          field_simp [ne_of_gt hr]
          nlinarith
        nlinarith [sq_nonneg (Real.sqrt (1-(δ/r)^2) - q/r),
          sq_nonneg (Real.sqrt (1-(δ/r)^2) + q/r)]
      rw [hsqrt]
      field_simp [ne_of_gt hr, ne_of_gt hq]
    · constructor
      · nlinarith [div_pos hδ hr]
      · exact (div_lt_one hr).2 hδr
  have hatanq : Real.arctan (q/δ) = Real.pi/2-Real.arcsin (δ/r) := by
    rw [hasin, show q/δ = (δ/q)⁻¹ by field_simp [ne_of_gt hδ, ne_of_gt hq]]
    exact Real.arctan_inv_of_pos (div_pos hδ hq)
  rw [liCenteredExteriorArea]
  dsimp [B, q]
  rw [hatan1, hatanq]
  ring

/-- The real-valued difference in the centred form of Li 2.3. -/
def liLemma23Gap (r δ : ℝ) : ℝ :=
  liCenteredExteriorArea r δ - liF r * Real.arcsin (δ / r)

private def liLemma23P (r s : ℝ) : ℝ :=
  16*r^4 + 16*r^3*s - 16*r^3 - 16*r^2*s + 8*r^2 +
    16*r*s^2 - 4*r + 16*s^3 - 4*s^2 - 4*s + 1

private theorem liLemma23_delta_le_two_fifths
    {r δ : ℝ} (hr0 : (3 / 20 : ℝ) ≤ r) (hr1 : r ≤ 1 / 2)
    (hcap : liLemma23ContextCap r δ) : δ ≤ 2 * r / 5 := by
  have hr : 0 < r := lt_of_lt_of_le (by norm_num) hr0
  have hpi : Real.pi ≤ 22 / 7 := by
    exact Real.pi_lt_d20.le.trans (by norm_num)
  have hsquare : (2 * r - 1) ^ 2 ≤ (7 / 10 : ℝ) ^ 2 := by
    have hleft : -(7 / 10 : ℝ) ≤ 2 * r - 1 := by linarith
    have hright : 2 * r - 1 ≤ 7 / 10 := by linarith
    nlinarith [sq_nonneg ((7 / 10 : ℝ) - (2*r-1)),
      sq_nonneg ((7 / 10 : ℝ) + (2*r-1))]
  have hf : liF r ≤ (49 / 200 : ℝ) * r := by
    rw [liF]
    nlinarith
  have hpif : Real.pi / 2 * liF r ≤ 2 * r / 5 := by
    have hf0 : 0 ≤ liF r := by unfold liF; positivity
    have hm := mul_le_mul_of_nonneg_right hpi
      (show 0 ≤ liF r / 2 by positivity)
    have hfr := mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ) ≤ 11 / 7)
    nlinarith
  exact hcap.2.trans hpif

private theorem liLemma23_sqrt_bounds
    {r δ : ℝ} (hr : 0 < r) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 2*r/5) :
    9*r/10 ≤ Real.sqrt (r^2-δ^2) ∧ Real.sqrt (r^2-δ^2) ≤ r := by
  have hδr : δ ≤ r := by nlinarith
  have hrad : 0 ≤ r^2-δ^2 := by nlinarith
  have hs_sq := Real.sq_sqrt hrad
  have hs0 := Real.sqrt_nonneg (r^2-δ^2)
  constructor
  · nlinarith [sq_nonneg (δ - 2*r/5)]
  · nlinarith

private theorem liLemma23_Q_nonpos
    {r : ℝ} (hr0 : (3/20 : ℝ) ≤ r) (hr1 : r ≤ 1/2) :
    3800*r^4-722*r^3+595*r^2-950*r+125 ≤ 0 := by
  let Q : ℝ := 3800*r^4-722*r^3+595*r^2-950*r+125
  let L : ℝ := -(28214*r-3307)/200
  have hpos : 0 ≤ 19000*r^2+8740*r+7231 := by positivity
  have hcert : L-Q =
      -(2*r-1)*(20*r-3)*(19000*r^2+8740*r+7231)/200 := by
    dsimp [L, Q]
    ring
  have hLQ : Q ≤ L := by
    apply sub_nonneg.mp
    rw [hcert]
    have h1 : 2*r-1 ≤ 0 := by linarith
    have h2 : 0 ≤ 20*r-3 := by linarith
    exact div_nonneg (mul_nonneg (mul_nonneg (neg_nonneg.mpr h1) h2) hpos)
      (by norm_num)
  have hL : L ≤ 0 := by dsimp [L]; linarith
  exact hLQ.trans hL

private theorem liLemma23_P_lower_nonpos
    {r : ℝ} (hr0 : (3/20 : ℝ) ≤ r) (hr1 : r ≤ 1/2) :
    liLemma23P r (9*r/10) ≤ 0 := by
  have hQ := liLemma23_Q_nonpos hr0 hr1
  have heq : liLemma23P r (9*r/10) =
      (3800*r^4-722*r^3+595*r^2-950*r+125)/125 := by
    unfold liLemma23P
    ring
  rw [heq]
  exact div_nonpos_of_nonpos_of_nonneg hQ (by norm_num)

private theorem liLemma23_P_upper_nonpos
    {r : ℝ} (hr0 : (3/20 : ℝ) ≤ r) (hr1 : r ≤ 1/2) :
    liLemma23P r r ≤ 0 := by
  have hcubic : 0 ≤ 16*r^3+8*r^2+6*r-1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr0) (sq_nonneg r), sq_nonneg r]
  have heq : liLemma23P r r = (2*r-1)*(16*r^3+8*r^2+6*r-1) := by
    unfold liLemma23P
    ring
  rw [heq]
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hcubic

private theorem liLemma23_P_nonpos
    {r s : ℝ} (hr0 : (3/20 : ℝ) ≤ r) (hr1 : r ≤ 1/2)
    (hs0 : 9*r/10 ≤ s) (hs1 : s ≤ r) : liLemma23P r s ≤ 0 := by
  have hr : 0 < r := lt_of_lt_of_le (by norm_num) hr0
  let P0 := liLemma23P r (9*r/10)
  let P1 := liLemma23P r r
  let L := (10*(r-s)*P0 + (10*s-9*r)*P1) / r
  have h0 : P0 ≤ 0 := liLemma23_P_lower_nonpos hr0 hr1
  have h1 : P1 ≤ 0 := liLemma23_P_upper_nonpos hr0 hr1
  have hw0 : 0 ≤ 10*(r-s) := mul_nonneg (by norm_num) (sub_nonneg.mpr hs1)
  have hw1 : 0 ≤ 10*s-9*r := by linarith
  have hL : L ≤ 0 := by
    dsimp [L]
    exact div_nonpos_of_nonpos_of_nonneg
      (add_nonpos (mul_nonpos_of_nonneg_of_nonpos hw0 h0)
        (mul_nonpos_of_nonneg_of_nonpos hw1 h1)) hr.le
  have hcert : L - liLemma23P r s =
      -2*(r-s)*(9*r-10*s)*(58*r+20*s-5)/25 := by
    dsimp [L, P0, P1]
    field_simp [ne_of_gt hr]
    unfold liLemma23P
    ring
  have hfactor : 0 ≤ 58*r+20*s-5 := by nlinarith
  have hPL : liLemma23P r s ≤ L := by
    apply sub_nonneg.mp
    rw [hcert]
    have ha : 0 ≤ r-s := sub_nonneg.mpr hs1
    have hb : 9*r-10*s ≤ 0 := by linarith
    have hab : 0 ≤ -2*(r-s)*(9*r-10*s) :=
      mul_nonneg_of_nonpos_of_nonpos
        (mul_nonpos_of_nonpos_of_nonneg (by norm_num) ha) hb
    exact div_nonneg
      (mul_nonneg hab hfactor)
      (by norm_num)
  exact hPL.trans hL

private theorem liLemma23_gap_hasDerivAt
    {r δ : ℝ} (hr : 0 < r) (hδ0 : 0 ≤ δ) (hδr : δ < r) :
    HasDerivAt (liLemma23Gap r)
      (1/2 - Real.sqrt (r^2-δ^2) + δ^2 / Real.sqrt (r^2-δ^2) -
        r^2 / Real.sqrt (r^2-δ^2) + 2*r^2/(1+4*δ^2) -
        liF r / Real.sqrt (r^2-δ^2)) δ := by
  have hrad : 0 < r^2-δ^2 := by nlinarith
  have hs : Real.sqrt (r^2-δ^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hrad)
  have harcsin : HasDerivAt (fun x : ℝ => Real.arcsin (x/r))
      (1 / Real.sqrt (r^2-δ^2)) δ := by
    have hargneg : δ/r ≠ -1 := ne_of_gt
      ((by norm_num : (-1 : ℝ) < 0).trans_le (div_nonneg hδ0 hr.le))
    have hargpos : δ/r ≠ 1 := ne_of_lt ((div_lt_one hr).2 hδr)
    convert (Real.hasDerivAt_arcsin hargneg hargpos).comp δ
        ((hasDerivAt_id δ).div_const r) using 1
    have hq0 : 0 ≤ (r^2-δ^2)/r^2 := div_nonneg hrad.le (sq_nonneg r)
    have hq_sq := Real.sq_sqrt hq0
    have heq : r * Real.sqrt ((r^2-δ^2)/r^2) = Real.sqrt (r^2-δ^2) := by
      have hl0 : 0 ≤ r * Real.sqrt ((r^2-δ^2)/r^2) :=
        mul_nonneg hr.le (Real.sqrt_nonneg _)
      have hr0 := Real.sqrt_nonneg (r^2-δ^2)
      have hs_sq := Real.sq_sqrt hrad.le
      field_simp [ne_of_gt hr] at hq_sq
      nlinarith
    rw [show 1-(δ/r)^2 = (r^2-δ^2)/r^2 by
      field_simp [ne_of_gt hr], ← heq]
    field_simp [ne_of_gt hr, hs]
  have hsqrt : HasDerivAt (fun x : ℝ => Real.sqrt (r^2-x^2))
      (-δ / Real.sqrt (r^2-δ^2)) δ := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hrad)).comp δ
      (hasDerivAt_const δ (r^2) |>.sub ((hasDerivAt_id δ).pow 2)) using 1 <;>
      field_simp [hs] <;> simp <;> ring
  have hatan : HasDerivAt (fun x : ℝ => Real.arctan (2*x))
      (2/(1+4*δ^2)) δ := by
    convert (Real.hasDerivAt_arctan (2*δ)).comp δ
      ((hasDerivAt_const δ 2).mul (hasDerivAt_id δ)) using 1 <;> simp <;> ring
  unfold liLemma23Gap liCenteredExteriorArea
  convert ((hasDerivAt_id δ).div_const 2 |>.sub
      (((hasDerivAt_id δ).mul hsqrt).add
        ((harcsin.sub hatan).mul_const (r^2)))) |>.sub
      (harcsin.const_mul (liF r)) using 1 <;> simp <;> ring

private theorem liLemma23_gap_deriv_nonneg
    {r δ : ℝ} (hr0 : (3/20 : ℝ) ≤ r) (hr1 : r ≤ 1/2)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 2*r/5) :
    0 ≤ deriv (liLemma23Gap r) δ := by
  have hr : 0 < r := lt_of_lt_of_le (by norm_num) hr0
  have hδr : δ < r := by nlinarith
  let s := Real.sqrt (r^2-δ^2)
  have hsbound := liLemma23_sqrt_bounds hr hδ0 hδ
  have hrad : 0 < r^2-δ^2 := by nlinarith
  have hs : 0 < s := by dsimp [s]; exact Real.sqrt_pos.2 hrad
  have hs_sq : s^2 = r^2-δ^2 := by dsimp [s]; exact Real.sq_sqrt hrad.le
  have hP : liLemma23P r s ≤ 0 := liLemma23_P_nonpos hr0 hr1 hsbound.1 hsbound.2
  let D : ℝ := 1/2 - s + δ^2/s-r^2/s+2*r^2/(1+4*δ^2)-liF r/s
  have hcert : D*s*(1+4*δ^2) = -(r-s)*liLemma23P r s/2 := by
    have hrel : -δ^2+r^2-s^2 = 0 := by nlinarith [hs_sq]
    dsimp [D]
    field_simp [ne_of_gt hs]
    rw [liF]
    unfold liLemma23P
    ring_nf at hrel ⊢
    linear_combination
      (2*(-4*δ^2+8*r^3-8*r^2+2*r+8*s^2-2*s-1)) * hrel
  have hrs : 0 ≤ r-s := sub_nonneg.mpr hsbound.2
  have hD : 0 ≤ D := by
    have hrhs : 0 ≤ -(r-s)*liLemma23P r s/2 :=
      div_nonneg (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hrs) hP)
        (by norm_num)
    have hprod : 0 ≤ D*s*(1+4*δ^2) := hcert.symm ▸ hrhs
    have hfac : 0 < s * (1+4*δ^2) := mul_pos hs (by positivity)
    nlinarith
  rw [(liLemma23_gap_hasDerivAt hr hδ0 hδr).deriv]
  exact hD

/-- Calculus core of Li 2.3: under the actual contextual cap, the centred
exterior area pays `f(r) asin(δ/r)`. -/
theorem liLemma23_centered_calculus
    {r δ : ℝ} (hr0 : (3/20 : ℝ) ≤ r) (hr1 : r ≤ 1/2)
    (hcap : liLemma23ContextCap r δ) :
    liF r * Real.arcsin (δ/r) ≤ liCenteredExteriorArea r δ := by
  have hδ := liLemma23_delta_le_two_fifths hr0 hr1 hcap
  have hmono : MonotoneOn (liLemma23Gap r) (Icc 0 δ) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 δ)
    · apply continuousOn_of_forall_continuousAt
      intro x hx
      exact (liLemma23_gap_hasDerivAt
        (lt_of_lt_of_le (by norm_num) hr0) (by linarith [hx.1])
        (by nlinarith [hx.2, hδ])).continuousAt
    · intro x hx
      have hx' : x ∈ Ioo 0 δ := by simpa [interior_Icc] using hx
      exact (liLemma23_gap_hasDerivAt
        (lt_of_lt_of_le (by norm_num) hr0) hx'.1.le
        (by nlinarith [hx'.2, hδ])).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Ioo 0 δ := by simpa [interior_Icc] using hx
      exact liLemma23_gap_deriv_nonneg hr0 hr1 hx'.1.le
        (by linarith [hx'.2, hδ])
  have hzero : liLemma23Gap r 0 = 0 := by simp [liLemma23Gap]
  have := hmono ⟨le_rfl, hcap.1⟩ ⟨hcap.1, le_rfl⟩ hcap.1
  rw [hzero] at this
  dsimp [liLemma23Gap] at this
  linarith

/-- The calculus core in the form needed by the fixed strong parameters.  The
small-height hypothesis is placed before any contextual cap: this is exactly
the quantitative input used by the derivative certificate. -/
theorem liLemma23_centered_calculus_of_delta_le
    {r δ : ℝ} (hr0 : (3/20 : ℝ) ≤ r) (hr1 : r ≤ 1/2)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 2*r/5) :
    liF r * Real.arcsin (δ/r) ≤ liCenteredExteriorArea r δ := by
  have hmono : MonotoneOn (liLemma23Gap r) (Icc 0 δ) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 δ)
    · apply continuousOn_of_forall_continuousAt
      intro x hx
      exact (liLemma23_gap_hasDerivAt
        (lt_of_lt_of_le (by norm_num) hr0) (by linarith [hx.1])
        (by nlinarith [hx.2, hδ])).continuousAt
    · intro x hx
      have hx' : x ∈ Ioo 0 δ := by simpa [interior_Icc] using hx
      exact (liLemma23_gap_hasDerivAt
        (lt_of_lt_of_le (by norm_num) hr0) hx'.1.le
        (by nlinarith [hx'.2, hδ])).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Ioo 0 δ := by simpa [interior_Icc] using hx
      exact liLemma23_gap_deriv_nonneg hr0 hr1 hx'.1.le
        (by linarith [hx'.2, hδ])
  have hzero : liLemma23Gap r 0 = 0 := by simp [liLemma23Gap]
  have h := hmono ⟨le_rfl, hδ0⟩ ⟨hδ0, le_rfl⟩ hδ0
  rw [hzero] at h
  dsimp [liLemma23Gap] at h
  linarith

/-! ## Final geometric glue -/

private theorem supportNeedleTriangle_abs_height (α δ c : ℝ) :
    supportNeedleTriangle α δ c =
      supportNeedleTriangle (if 0 ≤ δ then α else α + Real.pi) |δ|
        (if 0 ≤ δ then c else -c) := by
  by_cases hδ : 0 ≤ δ
  · simp [hδ, abs_of_nonneg hδ]
  · have hδ' : |δ| = -δ := abs_of_neg (lt_of_not_ge hδ)
    simp only [if_neg hδ, hδ']
    ext z
    constructor
    · rintro ⟨lam, hlam, x, hx, rfl⟩
      refine ⟨lam, hlam, -x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, ?_⟩
      congr 1
      ext <;>
        simp [supportPoint, addCoordinatePlane, scaleCoordinatePlane,
          unitDirection, unitNormal, Real.sin_add, Real.cos_add] <;> ring
    · rintro ⟨lam, hlam, x, hx, rfl⟩
      refine ⟨lam, hlam, -x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, ?_⟩
      congr 1
      ext <;>
        simp [supportPoint, addCoordinatePlane, scaleCoordinatePlane,
          unitDirection, unitNormal, Real.sin_add, Real.cos_add] <;> ring

private theorem liExterior_image_nullMeasurable
    {d : ProjectiveDirection} (N : DirectionNeedle d) (r : ℝ) :
    NullMeasurableSet (coordinatePlaneEquiv '' liExterior N r) volume := by
  have htri : NullMeasurableSet (coordinatePlaneEquiv '' N.triangle) volume := by
    rw [N.image_triangle_eq_triangleHull]
    exact (N.toUnitNeedle.triangleHull_convex 0).nullMeasurableSet volume
  have hdisk : MeasurableSet (originOpenDisk r) := by
    exact measurableSet_lt
      ((continuous_fst.pow 2).add (continuous_snd.pow 2)).measurable
      measurable_const
  rw [liExterior, Set.image_diff coordinatePlaneEquiv.injective]
  exact htri.diff
    ((coordinatePlaneEquiv.measurableSet_image.mpr hdisk).nullMeasurableSet)

private theorem liExterior_measure_eq_image
    {d : ProjectiveDirection} (N : DirectionNeedle d) (r : ℝ) :
    (volume.prod volume) (liExterior N r) =
      volume (coordinatePlaneEquiv '' liExterior N r) := by
  have hpre : coordinatePlaneEquiv ⁻¹'
      (coordinatePlaneEquiv '' liExterior N r) = liExterior N r := by
    exact Set.preimage_image_eq _ coordinatePlaneEquiv.injective
  calc
    (volume.prod volume) (liExterior N r) =
        (volume.prod volume) (coordinatePlaneEquiv ⁻¹'
          (coordinatePlaneEquiv '' liExterior N r)) := congrArg _ hpre.symm
    _ = volume (coordinatePlaneEquiv '' liExterior N r) :=
      coordinatePlaneEquiv_measurePreserving.measure_preimage
        (liExterior_image_nullMeasurable N r)

private theorem liExterior_image_ne_top
    {d : ProjectiveDirection} (N : DirectionNeedle d) (r : ℝ) :
    volume (coordinatePlaneEquiv '' liExterior N r) ≠ ⊤ := by
  have hle : volume (coordinatePlaneEquiv '' liExterior N r) ≤
      volume (N.toUnitNeedle.triangleHull 0) := by
    rw [← N.image_triangle_eq_triangleHull]
    exact measure_mono (Set.image_mono diff_subset)
  have hfinite : volume (N.toUnitNeedle.triangleHull 0) ≠ ⊤ :=
    ne_of_lt (N.toUnitNeedle.triangleHull_isCompact 0 |>.measure_lt_top)
  exact ne_top_of_le_ne_top hfinite hle

private theorem liLemma23_outer_lower
    {d : ProjectiveDirection} (N : DirectionNeedle d) (r : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1 / 2) (hδ : 0 < |N.height|)
    (hδr : |N.height| < r)
    (hcalc : liF r * Real.arcsin (|N.height| / r) ≤
      liCenteredExteriorArea r |N.height|) :
    ENNReal.ofReal (liF r * Real.arcsin (|N.height| / r)) ≤
      (volume.prod volume).toOuterMeasure (liExterior N r) := by
  let α := if 0 ≤ N.height then N.angle else N.angle + Real.pi
  let c := if 0 ≤ N.height then N.centre else -N.centre
  have htriangle : N.triangle = supportNeedleTriangle α |N.height| c := by
    exact supportNeedleTriangle_abs_height N.angle N.height N.centre
  have harea := li23_area_as_window (α := α) (c := c) hr hδ
  have hmin := li23Window_min r |N.height| c hδ
  have hcenter := li23Window_centered hr hr1 hδ hδr
  have hreal : liF r * Real.arcsin (|N.height| / r) ≤
      volume.real (coordinatePlaneEquiv '' liExterior N r) := by
    rw [liExterior, htriangle, harea]
    rw [hcenter] at hmin
    exact hcalc.trans hmin
  rw [Measure.toOuterMeasure_apply, liExterior_measure_eq_image]
  rw [← ENNReal.ofReal_toReal (liExterior_image_ne_top N r)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Li 2.3 for an arbitrary direction needle, including signed support heights
and the degenerate zero-height case. -/
theorem liLemma23_exterior_area : LiLemma23ExteriorAreaStatement := by
  intro d N r hr0 hr1 hcap hδr
  have hr : 0 < r := lt_of_lt_of_le (by norm_num) hr0
  by_cases hzero : |N.height| = 0
  · simp [hzero]
  · have hδ : 0 < |N.height| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hzero)
    exact liLemma23_outer_lower N r hr hr1 hδ hδr
      (liLemma23_centered_calculus hr0 hr1 hcap)

theorem LiLemma23ExteriorAreaStatement_proof : LiLemma23ExteriorAreaStatement :=
  liLemma23_exterior_area

/-- Strong-parameter Li 2.3.  Every needle of height at most `strongA` pays its
exterior-area contribution at the single radius `strongR₀`; there is no
context-cap premise in this exported interface. -/
theorem liLemma23_strong
    {d : ProjectiveDirection} (N : DirectionNeedle d)
    (hheight : |N.height| ≤ strongA) :
    ENNReal.ofReal
        (liF strongR₀ * Real.arcsin (|N.height| / strongR₀)) ≤
      (volume.prod volume).toOuterMeasure (liExterior N strongR₀) := by
  have hr0 : (3/20 : ℝ) ≤ strongR₀ :=
    strongParameterDomain.r₀_ge_three_twentieths
  have hr1 : strongR₀ ≤ 1/2 := strongParameterDomain.r₀_lt_half.le
  have hr : 0 < strongR₀ := lt_of_lt_of_le (by norm_num) hr0
  have hA : strongA ≤ 2 * strongR₀ / 5 := by
    norm_num [strongA, strongR₀]
  have hδcap : |N.height| ≤ 2 * strongR₀ / 5 := hheight.trans hA
  have hδr : |N.height| < strongR₀ := by
    nlinarith [abs_nonneg N.height]
  by_cases hzero : |N.height| = 0
  · simp [hzero]
  · have hδ : 0 < |N.height| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hzero)
    exact liLemma23_outer_lower N strongR₀ hr hr1 hδ hδr
      (liLemma23_centered_calculus_of_delta_le hr0 hr1 (abs_nonneg _) hδcap)

end

end StarKakeyaLower
