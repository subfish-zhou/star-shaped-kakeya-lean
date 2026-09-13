import StarKakeyaLower.Figure5LocalContact
import StarKakeyaLower.SupportReflection
import StarKakeyaLower.UniversalNeedleAdapter

/-!
# Canonical first-arc data for an arbitrary raw support needle

This file closes the two structural gaps left by the trace decomposition API:

* **orientation** – an arbitrary raw `DirectionNeedle` has a *signed* support
  height.  `DirectionNeedle.orientPositive` replaces it by the equivalent
  presentation with nonnegative height, keeping the projective direction, the
  filled triangle and the pair of base-endpoint norms.
* **totality** – for `0 < r < 1/2` the polar trace of a unit-base support
  triangle is nonempty (one base endpoint has norm at least `1/2`), so the
  optional trace decomposition is always `some`.  Moreover the selected first
  arc has *positive* span exactly when the support height is positive.
-/

open Set Real

namespace StarKakeyaLower

noncomputable section

/-! ## Polar presentation of a support point -/

/-- Every unit vector is `(cos φ, sin φ)`. -/
theorem exists_cos_sin_of_sq_add_sq_eq_one {u v : ℝ} (h : u ^ 2 + v ^ 2 = 1) :
    ∃ φ : ℝ, Real.cos φ = u ∧ Real.sin φ = v := by
  have hu : u ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> nlinarith [sq_nonneg v, sq_nonneg (u - 1), sq_nonneg (u + 1)]
  have hcos : Real.cos (Real.arccos u) = u := Real.cos_arccos hu.1 hu.2
  have hsin : Real.sin (Real.arccos u) = Real.sqrt (1 - u ^ 2) :=
    Real.sin_arccos u
  have hv2 : Real.sqrt (1 - u ^ 2) = |v| := by
    rw [show (1 : ℝ) - u ^ 2 = v ^ 2 by linarith, Real.sqrt_sq_eq_abs]
  rcases le_or_gt 0 v with hv | hv
  · exact ⟨Real.arccos u, hcos, by rw [hsin, hv2, abs_of_nonneg hv]⟩
  · refine ⟨-Real.arccos u, by rw [Real.cos_neg]; exact hcos, ?_⟩
    rw [Real.sin_neg, hsin, hv2, abs_of_neg hv, neg_neg]

/-- A support point is the polar point at radius `√(δ²+x²)` in a direction
obtained from `α` by an explicit angle. -/
theorem exists_supportPoint_eq_polarPoint (α δ x : ℝ)
    (hpos : 0 < δ ^ 2 + x ^ 2) :
    ∃ φ : ℝ, Real.cos φ = x / Real.sqrt (δ ^ 2 + x ^ 2) ∧
      Real.sin φ = δ / Real.sqrt (δ ^ 2 + x ^ 2) ∧
      supportPoint α δ x =
        polarPoint (Real.sqrt (δ ^ 2 + x ^ 2)) (α + φ) := by
  set ρ : ℝ := Real.sqrt (δ ^ 2 + x ^ 2) with hρdef
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 hpos
  have hρsq : ρ ^ 2 = δ ^ 2 + x ^ 2 := Real.sq_sqrt hpos.le
  have hunit : (x / ρ) ^ 2 + (δ / ρ) ^ 2 = 1 := by
    field_simp
    linarith [hρsq]
  obtain ⟨φ, hcos, hsin⟩ := exists_cos_sin_of_sq_add_sq_eq_one hunit
  refine ⟨φ, hcos, hsin, ?_⟩
  have hx : x = ρ * Real.cos φ := by
    rw [hcos]; field_simp
  have hδ : δ = ρ * Real.sin φ := by
    rw [hsin]; field_simp
  ext <;>
    simp [supportPoint, polarPoint, addCoordinatePlane, scaleCoordinatePlane,
      unitDirection, unitNormal, Real.cos_add, Real.sin_add] <;>
    rw [hx, hδ] <;> ring

/-! ## Nonemptiness of the trace below radius one half -/

/-- One of the two base endpoints has tangential coordinate of absolute value
at least one half. -/
private theorem exists_far_base_parameter (c : ℝ) :
    ∃ x : ℝ, x ∈ Icc (c - 1 / 2) (c + 1 / 2) ∧ 1 / 2 ≤ |x| := by
  rcases le_or_gt 0 c with hc | hc
  · exact ⟨c + 1 / 2, ⟨by linarith, le_rfl⟩, by rw [abs_of_nonneg (by linarith)]; linarith⟩
  · exact ⟨c - 1 / 2, ⟨le_rfl, by linarith⟩, by
      rw [abs_of_nonpos (by linarith)]; linarith⟩

/-- For radii below one half the raw polar trace of a unit-base support
triangle is nonempty: the far base endpoint has norm at least `1/2 > r`, so its
radial segment crosses the circle. -/
theorem trianglePolarTrace_nonempty {α δ c r : ℝ}
    (hr0 : 0 < r) (hrhalf : r < 1 / 2) :
    (trianglePolarTrace (supportNeedleTriangle α δ c) r).Nonempty := by
  obtain ⟨x, hx, hxabs⟩ := exists_far_base_parameter c
  have hxsq : 1 / 4 ≤ x ^ 2 := by
    have := sq_abs x
    nlinarith [abs_nonneg x]
  have hpos : 0 < δ ^ 2 + x ^ 2 := by nlinarith [sq_nonneg δ]
  set ρ : ℝ := Real.sqrt (δ ^ 2 + x ^ 2) with hρdef
  have hρsq : ρ ^ 2 = δ ^ 2 + x ^ 2 := Real.sq_sqrt hpos.le
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 hpos
  have hρhalf : 1 / 2 ≤ ρ := by nlinarith [sq_nonneg δ]
  have hrρ : r < ρ := lt_of_lt_of_le hrhalf hρhalf
  obtain ⟨φ, _, _, hpolar⟩ := exists_supportPoint_eq_polarPoint α δ x hpos
  refine ⟨α + φ, ?_⟩
  refine ⟨r / ρ, ⟨(div_pos hr0 hρ0).le, (div_le_one hρ0).2 hrρ.le⟩, x, hx, ?_⟩
  rw [hpolar]
  rw [← hρdef]
  simp only [polarPoint, scaleCoordinatePlane, unitDirection, Prod.mk.injEq]
  constructor <;> field_simp

/-- Quotient form of the nonemptiness statement. -/
theorem polarCircleTrace_nonempty {α δ c r : ℝ}
    (hr0 : 0 < r) (hrhalf : r < 1 / 2) :
    (polarCircleTrace (supportNeedleTriangle α δ c) r).Nonempty := by
  obtain ⟨θ, hθ⟩ := trianglePolarTrace_nonempty (α := α) (δ := δ) (c := c) hr0 hrhalf
  exact ⟨(θ : PolarAngle), θ, hθ, rfl⟩

/-! ## Totality of the optional trace decomposition -/

theorem ClosedTraceDecomposition.toFirstArcData?_isSome_of_nonempty
    {T : Set CoordinatePlane} {r : ℝ} (D : ClosedTraceDecomposition T r)
    (hne : (polarCircleTrace T r).Nonempty) : D.toFirstArcData?.isSome := by
  cases D with
  | empty hcover => exact absurd hcover (Set.nonempty_iff_ne_empty.1 hne)
  | one A hconn hcover => rfl
  | two A B hA hB hd hg hc => rfl

/-- Genuine (non-optional) first-arc data for every admissible support triple
below radius one half. -/
def supportTraceFirstArcData {r α δ c : ℝ} (hr0 : 0 < r) (hrhalf : r < 1 / 2)
    (hδ0 : 0 ≤ δ) (hδr : δ ≤ r) :
    FirstArcData (supportNeedleTriangle α δ c) r :=
  (supportTraceClosedDecomposition (α := α) (c := c) hr0 hδ0 hδr).toFirstArcData?.get
    ((supportTraceClosedDecomposition (α := α) (c := c) hr0 hδ0
      hδr).toFirstArcData?_isSome_of_nonempty
        (polarCircleTrace_nonempty hr0 hrhalf))

theorem supportTraceFirstArcData?_eq_some {r α δ c : ℝ}
    (hr0 : 0 < r) (hrhalf : r < 1 / 2) (hδ0 : 0 ≤ δ) (hδr : δ ≤ r) :
    supportTraceFirstArcData? (α := α) (c := c) hr0 hδ0 hδr =
      some (supportTraceFirstArcData (α := α) (c := c) hr0 hrhalf hδ0 hδr) := by
  rw [supportTraceFirstArcData, supportTraceFirstArcData?]
  exact (Option.some_get _).symm

/-- Consequently the deterministic selector is literally the first arc of the
canonical data. -/
theorem selectedSupportFirstArc?_eq_some {r α δ c : ℝ}
    (hr0 : 0 < r) (hrhalf : r < 1 / 2) (hδ0 : 0 ≤ δ) (hδr : δ ≤ r) :
    selectedSupportFirstArc? r α (δ, c) =
      some (supportTraceFirstArcData (α := α) (c := c) hr0 hrhalf hδ0 hδr).firstArc := by
  rw [selectedSupportFirstArc?, dif_pos hr0, dif_pos hδ0, dif_pos hδr,
    supportTraceFirstArcData?_eq_some hr0 hrhalf hδ0 hδr]
  rfl


/-! ## Orientation normalization of a raw support needle -/

/-- The equivalent presentation of a raw direction needle with nonnegative
support height.  Reversing the orientation of the support line negates both
support coordinates and leaves the filled triangle unchanged. -/
def DirectionNeedle.orientPositive {d : ProjectiveDirection}
    (N : DirectionNeedle d) : DirectionNeedle d :=
  if 0 ≤ N.height then N
  else
    { angle := N.angle + Real.pi
      height := -N.height
      centre := -N.centre
      direction_eq := by
        rw [projectiveDirection_add_pi]; exact N.direction_eq }

@[simp] theorem DirectionNeedle.orientPositive_height_nonneg
    {d : ProjectiveDirection} (N : DirectionNeedle d) :
    0 ≤ N.orientPositive.height := by
  rw [DirectionNeedle.orientPositive]
  split
  · assumption
  · simp only []
    linarith [not_le.1 (by assumption : ¬ 0 ≤ N.height)]

@[simp] theorem DirectionNeedle.orientPositive_abs_height
    {d : ProjectiveDirection} (N : DirectionNeedle d) :
    |N.orientPositive.height| = |N.height| := by
  rw [DirectionNeedle.orientPositive]
  split
  · rfl
  · exact abs_neg _

@[simp] theorem DirectionNeedle.orientPositive_triangle
    {d : ProjectiveDirection} (N : DirectionNeedle d) :
    N.orientPositive.triangle = N.triangle := by
  rw [DirectionNeedle.orientPositive]
  split
  · rfl
  · exact supportNeedleTriangle_add_pi_neg N.angle N.height N.centre

theorem DirectionNeedle.orientPositive_height_eq_abs
    {d : ProjectiveDirection} (N : DirectionNeedle d) :
    N.orientPositive.height = |N.height| := by
  rw [← abs_of_nonneg N.orientPositive_height_nonneg,
    DirectionNeedle.orientPositive_abs_height]

/-! ## A nondegenerate interval inside the principal trace window -/

/-- Reflection `φ ↦ π - φ` exchanges the two base parameters. -/
theorem mem_principalTraceWindow_pi_sub_iff {δ a b k φ : ℝ} :
    (Real.pi - φ) ∈ principalTraceWindow δ (-b) (-a) k ↔
      φ ∈ principalTraceWindow δ a b k := by
  simp only [principalTraceWindow, mem_setOf_eq, Real.sin_pi_sub, Real.cos_pi_sub]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨by linarith, by linarith, h3, by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨by linarith, by linarith, h3, by nlinarith, by nlinarith⟩

/-- Construction of a nondegenerate window interval from a far base endpoint.
The lower endpoint is the polar angle of the base endpoint `b`, whose norm is
at least `1/2 > r`; a small explicit increment stays inside all three defining
inequalities. -/
private theorem principalTraceWindow_interval_of_far_plus
    {δ a b r : ℝ} (hr0 : 0 < r) (hrhalf : r < 1 / 2) (hδ0 : 0 < δ)
    (hb0 : 1 / 2 ≤ b) (hab : a = b - 1) :
    ∃ φ₁ φ₂ : ℝ, φ₁ < φ₂ ∧
      Icc φ₁ φ₂ ⊆ principalTraceWindow δ a b (δ / r) := by
  have hpi := Real.pi_pos
  obtain ⟨ρ, hρ0, hρsq⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ^ 2 = δ ^ 2 + b ^ 2 := by
    refine ⟨Real.sqrt (δ ^ 2 + b ^ 2), Real.sqrt_pos.2 (by nlinarith),
      Real.sq_sqrt (by nlinarith)⟩
  have hbρ : b < ρ := by nlinarith
  have hρhalf : 1 / 2 ≤ ρ := by nlinarith
  have hrρ : r < ρ := lt_of_lt_of_le hrhalf hρhalf
  obtain ⟨φ, hφ0, hφhalf, hcos, hsin⟩ :
      ∃ φ : ℝ, 0 < φ ∧ φ < Real.pi / 2 ∧
        Real.cos φ = b / ρ ∧ Real.sin φ = δ / ρ := by
    have hbρ1 : b / ρ ≤ 1 := (div_le_one hρ0).2 hbρ.le
    have hbρm1 : (-1 : ℝ) ≤ b / ρ := by
      have : 0 < b / ρ := div_pos (by linarith) hρ0
      linarith
    have hcos : Real.cos (Real.arccos (b / ρ)) = b / ρ :=
      Real.cos_arccos hbρm1 hbρ1
    have hsin : Real.sin (Real.arccos (b / ρ)) = δ / ρ := by
      rw [Real.sin_arccos, show (1 : ℝ) - (b / ρ) ^ 2 = (δ / ρ) ^ 2 by
        field_simp; linarith]
      exact Real.sqrt_sq (by positivity)
    have hs0 : 0 < Real.sin (Real.arccos (b / ρ)) := by rw [hsin]; positivity
    have hc0 : 0 < Real.cos (Real.arccos (b / ρ)) := by
      rw [hcos]; exact div_pos (by linarith) hρ0
    refine ⟨Real.arccos (b / ρ), ?_, ?_, hcos, hsin⟩
    · rcases (Real.arccos_nonneg (b / ρ)).lt_or_eq with h | h
      · exact h
      · rw [← h] at hs0; simp at hs0
    · by_contra hcon
      rw [not_lt] at hcon
      exact absurd (Real.cos_nonpos_of_pi_div_two_le_of_le hcon
        (by linarith [Real.arccos_le_pi (b / ρ)])) (by linarith)
  have hδeq : δ = ρ * Real.sin φ := by rw [hsin]; field_simp
  have hbeq : b = ρ * Real.cos φ := by rw [hcos]; field_simp
  obtain ⟨ε, hε0, hεhalf, hεrho, hεgap⟩ :
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi / 2 - φ ∧ ρ * ε ≤ δ / ρ ∧
        δ / ρ + ε ≤ δ / r := by
    refine ⟨min (Real.pi / 2 - φ) (min (δ / ρ ^ 2) (δ * (ρ - r) / (r * ρ))),
      lt_min (by linarith) (lt_min (by positivity) (by
        have : 0 < ρ - r := by linarith
        positivity)), min_le_left _ _, ?_, ?_⟩
    · have h1 : min (Real.pi / 2 - φ) (min (δ / ρ ^ 2) (δ * (ρ - r) / (r * ρ))) ≤
          δ / ρ ^ 2 := (min_le_right _ _).trans (min_le_left _ _)
      have h2 : ρ * (δ / ρ ^ 2) = δ / ρ := by field_simp
      nlinarith
    · have h1 : min (Real.pi / 2 - φ) (min (δ / ρ ^ 2) (δ * (ρ - r) / (r * ρ))) ≤
          δ * (ρ - r) / (r * ρ) := (min_le_right _ _).trans (min_le_right _ _)
      have h2 : δ * (ρ - r) / (r * ρ) = δ / r - δ / ρ := by
        field_simp
      linarith
  refine ⟨φ, φ + ε, by linarith, ?_⟩
  rintro ψ ⟨hlo, hhi⟩
  have hψhalf : ψ ≤ Real.pi / 2 := by linarith
  have hψpos : 0 < ψ := lt_of_lt_of_le hφ0 hlo
  have hsub0 : 0 ≤ ψ - φ := by linarith
  have hsinsub : Real.sin (ψ - φ) ≤ ε := (Real.sin_le hsub0).trans (by linarith)
  have hsinsub0 : 0 ≤ Real.sin (ψ - φ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hsub0 (by linarith)
  have hsinmono : Real.sin φ ≤ Real.sin ψ :=
    figure5_sin_le_sin_of_le' (by linarith) hψhalf hlo
  have hexpand : Real.sin (ψ - φ) =
      Real.sin ψ * Real.cos φ - Real.cos ψ * Real.sin φ := Real.sin_sub ψ φ
  have hupper : δ * Real.cos ψ ≤ b * Real.sin ψ := by
    have hid : ρ * Real.sin (ψ - φ) = b * Real.sin ψ - δ * Real.cos ψ := by
      rw [hexpand]
      linear_combination (-Real.sin ψ) * hbeq + (Real.cos ψ) * hδeq
    nlinarith
  have hlower : a * Real.sin ψ ≤ δ * Real.cos ψ := by
    have hid : a * Real.sin ψ - δ * Real.cos ψ =
        ρ * Real.sin (ψ - φ) - Real.sin ψ := by
      rw [hab, hexpand]
      linear_combination (Real.sin ψ) * hbeq - (Real.cos ψ) * hδeq
    have hbound : ρ * Real.sin (ψ - φ) ≤ δ / ρ := by
      linarith [mul_le_mul_of_nonneg_left hsinsub hρ0.le]
    have hδρ : δ / ρ ≤ Real.sin ψ := by rw [← hsin]; exact hsinmono
    linarith
  have hheight : Real.sin ψ ≤ δ / r := by
    have hstep : Real.sin ψ ≤ Real.sin (φ + ε) :=
      figure5_sin_le_sin_of_le' (by linarith) (by linarith) hhi
    have hdiff : Real.sin (φ + ε) - Real.sin φ ≤ ε := by
      have hform := Real.sin_sub_sin (φ + ε) φ
      rw [show (φ + ε - φ) / 2 = ε / 2 by ring] at hform
      have hs1 : Real.sin (ε / 2) ≤ ε / 2 := Real.sin_le (by linarith)
      have hs0 : 0 ≤ Real.sin (ε / 2) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      have hc1 : Real.cos ((φ + ε + φ) / 2) ≤ 1 := Real.cos_le_one _
      have key : 2 * Real.sin (ε / 2) * Real.cos ((φ + ε + φ) / 2) ≤ ε := by
        nlinarith [mul_nonneg hs0 (sub_nonneg.2 hc1)]
      linarith [hform]
    rw [hsin] at hdiff
    linarith
  exact ⟨hψpos, by linarith, hheight, hlower, hupper⟩

/-- A nondegenerate interval inside the principal window, for every centre. -/
theorem principalTraceWindow_interval
    {δ c r : ℝ} (hr0 : 0 < r) (hrhalf : r < 1 / 2) (hδ0 : 0 < δ) :
    ∃ φ₁ φ₂ : ℝ, φ₁ < φ₂ ∧
      Icc φ₁ φ₂ ⊆ principalTraceWindow δ (c - 1 / 2) (c + 1 / 2) (δ / r) := by
  rcases le_or_gt 0 c with hc | hc
  · exact principalTraceWindow_interval_of_far_plus hr0 hrhalf hδ0
      (by linarith) (by ring)
  · obtain ⟨ψ₁, ψ₂, hlt, hsub⟩ :=
      principalTraceWindow_interval_of_far_plus (δ := δ) (a := -(c + 1 / 2))
        (b := -(c - 1 / 2)) hr0 hrhalf hδ0 (by linarith) (by ring)
    refine ⟨Real.pi - ψ₂, Real.pi - ψ₁, by linarith, ?_⟩
    rintro φ ⟨hlo, hhi⟩
    exact mem_principalTraceWindow_pi_sub_iff.1
      (hsub ⟨by linarith, by linarith⟩)

/-! ## Positivity of the selected span at positive height -/

theorem NormalizedPolarArc.carrier_eq_singleton_of_span_nonpos
    {A : NormalizedPolarArc} (h : A.span ≤ 0) :
    A.carrier = {((A.lo : ℝ) : PolarAngle)} := by
  have heq : A.hi = A.lo := by
    have := A.le_endpoints
    dsimp [NormalizedPolarArc.span] at h
    linarith
  have h2 : ¬ 2 * Real.pi ≤ A.hi - A.lo := by
    rw [heq]; simp only [sub_self]; linarith [Real.pi_pos]
  rw [NormalizedPolarArc.carrier, polarArc, quotientClosedInterval, if_neg h2, heq,
    Set.Icc_self, Set.image_singleton]

theorem FirstArcData.componentZero_span_le_firstArc_span
    {T : Set CoordinatePlane} {r : ℝ} (D : FirstArcData T r) :
    D.componentZero.span ≤ D.firstArc.span := by
  cases h : D.componentOne with
  | none => simp [FirstArcData.firstArc, h]
  | some A =>
      by_cases hle : A.span ≤ D.componentZero.span
      · simp [FirstArcData.firstArc, h, hle]
      · simp only [FirstArcData.firstArc, h, if_neg hle]
        linarith [not_le.1 hle]

theorem FirstArcData.componentOne_span_le_firstArc_span
    {T : Set CoordinatePlane} {r : ℝ} (D : FirstArcData T r)
    {A : NormalizedPolarArc} (h : D.componentOne = some A) :
    A.span ≤ D.firstArc.span := by
  by_cases hle : A.span ≤ D.componentZero.span
  · simp [FirstArcData.firstArc, h, hle]
  · simp [FirstArcData.firstArc, h, hle]

/-- Faithfulness of the half-period chart used by the three exhibited trace
points. -/
private theorem polar_coe_add_inj {α φ ψ : ℝ}
    (hφ : φ ∈ Ioo 0 Real.pi) (hψ : ψ ∈ Ioo 0 Real.pi)
    (h : ((α + φ : ℝ) : PolarAngle) = ((α + ψ : ℝ) : PolarAngle)) : φ = ψ := by
  have hpi := Real.pi_pos
  have := NormalizedPolarArc.polar_coe_injective_on_fullChart (a := α)
    (x := α + φ) (y := α + ψ)
    ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
    ⟨by linarith [hψ.1], by linarith [hψ.2]⟩ h
  linarith

/-- **Positive height gives a positive selected span.**  If the span were zero
both recorded components would be singletons, so the whole trace would have at
most two points; but the window contains a nondegenerate interval. -/
theorem firstArc_span_pos_of_height_pos {α δ c r : ℝ}
    (hr0 : 0 < r) (hrhalf : r < 1 / 2) (hδ0 : 0 < δ) (hδr : δ < r)
    (D : FirstArcData (supportNeedleTriangle α δ c) r) :
    0 < D.firstArc.span := by
  by_contra hcon
  rw [not_lt] at hcon
  -- both components degenerate
  have hzero : D.componentZero.carrier =
      {((D.componentZero.lo : ℝ) : PolarAngle)} :=
    NormalizedPolarArc.carrier_eq_singleton_of_span_nonpos
      (D.componentZero_span_le_firstArc_span.trans hcon)
  obtain ⟨p, q, hsub⟩ :
      ∃ p q : PolarAngle,
        polarCircleTrace (supportNeedleTriangle α δ c) r ⊆ {p, q} := by
    cases h : D.componentOne with
    | none =>
        refine ⟨((D.componentZero.lo : ℝ) : PolarAngle),
          ((D.componentZero.lo : ℝ) : PolarAngle), ?_⟩
        rw [← D.union_components, h]
        simp [hzero]
    | some A =>
        refine ⟨((D.componentZero.lo : ℝ) : PolarAngle),
          ((A.lo : ℝ) : PolarAngle), ?_⟩
        rw [← D.union_components, h]
        have hA : A.carrier = {((A.lo : ℝ) : PolarAngle)} :=
          NormalizedPolarArc.carrier_eq_singleton_of_span_nonpos
            ((D.componentOne_span_le_firstArc_span h).trans hcon)
        rw [hzero]
        simp only [Option.elim, hA]
        intro z hz
        rcases hz with hz | hz
        · exact Or.inl hz
        · exact Or.inr hz
  obtain ⟨φ₁, φ₂, hlt, hwin⟩ := principalTraceWindow_interval (c := c) hr0 hrhalf hδ0
  set m : ℝ := (φ₁ + φ₂) / 2 with hm
  have hmem : ∀ φ : ℝ, φ ∈ Icc φ₁ φ₂ →
      φ ∈ Ioo 0 Real.pi ∧
        ((α + φ : ℝ) : PolarAngle) ∈
          polarCircleTrace (supportNeedleTriangle α δ c) r := by
    intro φ hφ
    have hw := hwin hφ
    have h0 : 0 < φ := hw.1
    have hpiφ : φ < Real.pi := hw.2.1
    refine ⟨⟨h0, hpiφ⟩, ⟨α + φ, ?_, rfl⟩⟩
    refine (mem_trianglePolarTrace_iff_shifted_principalTraceWindow hr0 hδ0 hδr
      (by linarith) (by linarith)).2 ?_
    simpa only [add_sub_cancel_left] using hw
  obtain ⟨hi1, ht1⟩ := hmem φ₁ ⟨le_rfl, hlt.le⟩
  obtain ⟨hi2, ht2⟩ := hmem m ⟨by simp only [hm]; linarith, by simp only [hm]; linarith⟩
  obtain ⟨hi3, ht3⟩ := hmem φ₂ ⟨hlt.le, le_rfl⟩
  have hne12 : ((α + φ₁ : ℝ) : PolarAngle) ≠ ((α + m : ℝ) : PolarAngle) := by
    intro h
    have := polar_coe_add_inj hi1 hi2 h
    simp only [hm] at this; linarith
  have hne13 : ((α + φ₁ : ℝ) : PolarAngle) ≠ ((α + φ₂ : ℝ) : PolarAngle) := by
    intro h
    have := polar_coe_add_inj hi1 hi3 h
    linarith
  have hne23 : ((α + m : ℝ) : PolarAngle) ≠ ((α + φ₂ : ℝ) : PolarAngle) := by
    intro h
    have := polar_coe_add_inj hi2 hi3 h
    simp only [hm] at this; linarith
  have h1 := hsub ht1
  have h2 := hsub ht2
  have h3 := hsub ht3
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2 h3
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    simp_all


/-! ## Canonical-data specializations -/

/-- Positive span of the canonical selected arc at positive height. -/
theorem supportTraceFirstArcData_span_pos {r α δ c : ℝ}
    (hr0 : 0 < r) (hrhalf : r < 1 / 2) (hδ0 : 0 ≤ δ) (hδr : δ ≤ r)
    (hδpos : 0 < δ) (hδlt : δ < r) :
    (supportTraceFirstArcData (α := α) (c := c) hr0 hrhalf hδ0 hδr).firstArc.lo <
      (supportTraceFirstArcData (α := α) (c := c) hr0 hrhalf hδ0 hδr).firstArc.hi := by
  have h := firstArc_span_pos_of_height_pos hr0 hrhalf hδpos hδlt
    (supportTraceFirstArcData (α := α) (c := c) hr0 hrhalf hδ0 hδr)
  dsimp [NormalizedPolarArc.span] at h
  linarith

/-- At zero height the canonical selected arc is the degenerate contact whose
projective centre is the needle direction. -/
theorem supportTraceFirstArcData_zeroHeight {r α δ c : ℝ}
    (hr0 : 0 < r) (hrhalf : r < 1 / 2) (hδ0 : 0 ≤ δ) (hδr : δ ≤ r) (hδ : δ = 0) :
    ((((supportTraceFirstArcData (α := α) (c := c) hr0 hrhalf hδ0 hδr).firstArc.lo +
        (supportTraceFirstArcData (α := α) (c := c) hr0 hrhalf hδ0 hδr).firstArc.hi)
        / 2 : ℝ) : ProjectiveDirection) = (α : ProjectiveDirection) ∧
      ((supportTraceFirstArcData (α := α) (c := c) hr0 hrhalf hδ0 hδr).firstArc.hi -
        (supportTraceFirstArcData (α := α) (c := c) hr0 hrhalf hδ0 hδr).firstArc.lo)
        / 2 = 0 := by
  subst hδ
  exact supportTraceFirstArcData?_zeroHeight_projectiveCenter_radius hr0 _
    (supportTraceFirstArcData?_eq_some hr0 hrhalf hδ0 hδr)

end

end StarKakeyaLower
