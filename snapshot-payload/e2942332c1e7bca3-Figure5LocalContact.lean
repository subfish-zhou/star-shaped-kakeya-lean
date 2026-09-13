import StarKakeyaLower.Figure5EndpointEnvelope

/-!
# Figure 5 local-contact endpoint comparison

This file isolates the part of the endpoint argument which is genuinely local.
There is no compact support graph and no least/greatest direction.  A selected
`FirstArcData` and one changed lift of that selected arc are rotated until each
end of the target chart is an actual endpoint.  The two resulting strict gap
estimates then trap the original projective direction in the open, centred
quotient dilation.
-/

open Set Real

namespace StarKakeyaLower

noncomputable section

/-- The data retained from a positive normalized support.  In particular the
endpoint bounds are physical squared-norm bounds, rather than membership in a
support graph. -/
structure Figure5PositiveNormalizedSupport (r a R₁ : ℝ)
    (q : DirectedSupportParameter) : Prop where
  radius_pos : 0 < r
  height_pos : 0 < q.2.1
  height_le_a : q.2.1 ≤ a
  height_le_radius : q.2.1 ≤ r
  minus_norm : planeNormSq (figure5BaseMinus q) ≤ R₁ ^ 2
  plus_norm : planeNormSq (figure5BasePlus q) ≤ R₁ ^ 2

/-- The support parameter canonically read from a member of a direction needle
family.  The family already stores nonnegative (orientation-normalized) support
height. -/
def DirectionNeedleFamily.supportParameterAt {r : ℝ}
    (F : DirectionNeedleFamily r) (d : ProjectiveDirection) :
    DirectedSupportParameter :=
  ((F.needle d).angle, ((F.needle d).height, (F.needle d).centre))

/-- A selected first arc together with the particular lift used in the target
chart.  This is local data attached to one support, not an extremum statement. -/
structure Figure5SelectedChangedLift
    (r t : ℝ) (q : DirectedSupportParameter)
    (D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r)
    (A : NormalizedPolarArc) : Prop where
  target_nonneg : 0 ≤ t
  target_lt_pi : t < Real.pi
  selected : selectedSupportFirstArc? r q.1 q.2 = some D.firstArc
  changed : ∃ n : ℤ, D.firstArc.changeLift n = A
  in_target : Icc A.lo A.hi ⊆ Icc 0 t

/-- Rotation which moves the upper endpoint of the chosen lift to `t`. -/
def figure5UpperRotation (t : ℝ) (A : NormalizedPolarArc) : ℝ := t - A.hi

/-- Rotation which moves the lower endpoint of the chosen lift to `0`. -/
def figure5LowerRotation (A : NormalizedPolarArc) : ℝ := -A.lo

/-- Orientation-aware analytic lift after upper endpoint normalization.  Arc
rotation still uses `q.1`; this expression alone uses the projective lift
`gamma`. -/
def figure5UpperAnalyticAngle (gamma t : ℝ) (A : NormalizedPolarArc) : ℝ :=
  gamma + t - A.hi

/-- Orientation-aware analytic lift after lower normalization and reflection. -/
def figure5LowerAnalyticAngle (gamma t : ℝ) (A : NormalizedPolarArc) : ℝ :=
  t - (gamma - A.lo)

/-- Replace only the analytic angle of a support parameter. -/
def figure5AnalyticSupport (alpha : ℝ) (q : DirectedSupportParameter) :
    DirectedSupportParameter := (alpha, q.2)

/-- Adding `π` changes an oriented support presentation but not its projective
needle direction. -/
theorem figure5_projectiveDirection_add_pi (alpha : ℝ) :
    ((alpha + Real.pi : ℝ) : ProjectiveDirection) = (alpha : ProjectiveDirection) := by
  rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]

/-- A left-winner analytic lift (an arbitrary full-turn translate) projects to
exactly the stored needle direction. -/
theorem figure5_left_gamma_direction (alpha : ℝ) (n : ℤ) :
    ((alpha + (n : ℝ) * (2 * Real.pi) : ℝ) : ProjectiveDirection) =
      (alpha : ProjectiveDirection) := by
  rw [show alpha + (n : ℝ) * (2 * Real.pi) =
      alpha + ((2 * n : ℤ) : ℝ) * Real.pi by push_cast; ring]
  rw [← zsmul_eq_mul, AddCircle.coe_add, AddCircle.coe_zsmul,
    AddCircle.coe_period, smul_zero, add_zero]

/-- A right winner uses the opposite oriented normal (`alpha + π`), followed by
a full-turn shift.  Its projective direction is nevertheless unchanged. -/
theorem figure5_right_gamma_direction (alpha : ℝ) (n : ℤ) :
    ((alpha + Real.pi + (n : ℝ) * (2 * Real.pi) : ℝ) : ProjectiveDirection) =
      (alpha : ProjectiveDirection) := by
  rw [show alpha + Real.pi + (n : ℝ) * (2 * Real.pi) =
      alpha + ((2 * n + 1 : ℤ) : ℝ) * Real.pi by push_cast; ring]
  rw [← zsmul_eq_mul, AddCircle.coe_add, AddCircle.coe_zsmul,
    AddCircle.coe_period, smul_zero, add_zero]

/-- The upper-rotated support. -/
def figure5UpperSupport (t : ℝ) (A : NormalizedPolarArc)
    (q : DirectedSupportParameter) : DirectedSupportParameter :=
  (q.1 + figure5UpperRotation t A, q.2)

/-- The lower-rotated support. -/
def figure5LowerSupport (A : NormalizedPolarArc)
    (q : DirectedSupportParameter) : DirectedSupportParameter :=
  (q.1 + figure5LowerRotation A, q.2)

/-- Exact selector covariance for the upper local rotation. -/
theorem Figure5SelectedChangedLift.upper_selected
    {r t : ℝ} {q : DirectedSupportParameter}
    {D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r}
    {A : NormalizedPolarArc}
    (H : Figure5SelectedChangedLift r t q D A)
    (hq : Figure5PositiveNormalizedSupport r strongA strongR₁ q) :
    selectedSupportFirstArc? r (figure5UpperSupport t A q).1
        (figure5UpperSupport t A q).2 =
      some (D.firstArc.rotate (figure5UpperRotation t A)) := by
  dsimp [figure5UpperSupport]
  rw [selectedSupportFirstArc?_add_of_pos hq.radius_pos hq.height_pos
    hq.height_le_radius, H.selected]
  rfl

/-- Exact selector covariance for the lower local rotation. -/
theorem Figure5SelectedChangedLift.lower_selected
    {r t : ℝ} {q : DirectedSupportParameter}
    {D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r}
    {A : NormalizedPolarArc}
    (H : Figure5SelectedChangedLift r t q D A)
    (hq : Figure5PositiveNormalizedSupport r strongA strongR₁ q) :
    selectedSupportFirstArc? r (figure5LowerSupport A q).1
        (figure5LowerSupport A q).2 =
      some (D.firstArc.rotate (figure5LowerRotation A)) := by
  dsimp [figure5LowerSupport]
  rw [selectedSupportFirstArc?_add_of_pos hq.radius_pos hq.height_pos
    hq.height_le_radius, H.selected]
  rfl

/-- The upper rotation preserves the selected carrier, keeps it in the target,
and makes the upper endpoint equal to `t`. -/
theorem Figure5SelectedChangedLift.upper_rotated_lift
    {r t : ℝ} {q : DirectedSupportParameter}
    {D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r}
    {A : NormalizedPolarArc}
    (H : Figure5SelectedChangedLift r t q D A) :
    (D.firstArc.rotate (figure5UpperRotation t A)).carrier =
        (A.rotate (figure5UpperRotation t A)).carrier ∧
      Icc (A.rotate (figure5UpperRotation t A)).lo
          (A.rotate (figure5UpperRotation t A)).hi ⊆ Icc 0 t ∧
      (A.rotate (figure5UpperRotation t A)).hi = t := by
  obtain ⟨n, hn⟩ := H.changed
  have hcarrier : D.firstArc.carrier = A.carrier := by
    rw [← hn, NormalizedPolarArc.changeLift_carrier]
  have hlo := (H.in_target ⟨le_rfl, A.le_endpoints⟩).1
  have hhi := (H.in_target ⟨A.le_endpoints, le_rfl⟩).2
  constructor
  · simpa only [NormalizedPolarArc.rotate_carrier, add_comm] using congrArg
      (fun S : Set PolarAngle => (fun z : PolarAngle =>
        z + (figure5UpperRotation t A : PolarAngle)) '' S) hcarrier
  constructor
  · intro x hx
    change A.lo + (t - A.hi) ≤ x ∧ x ≤ A.hi + (t - A.hi) at hx
    change 0 ≤ x ∧ x ≤ t
    constructor <;> linarith [hlo, hhi]
  · simp [figure5UpperRotation, NormalizedPolarArc.rotate]

/-- The lower rotation is the symmetric endpoint normalization. -/
theorem Figure5SelectedChangedLift.lower_rotated_lift
    {r t : ℝ} {q : DirectedSupportParameter}
    {D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r}
    {A : NormalizedPolarArc}
    (H : Figure5SelectedChangedLift r t q D A) :
    (D.firstArc.rotate (figure5LowerRotation A)).carrier =
        (A.rotate (figure5LowerRotation A)).carrier ∧
      Icc (A.rotate (figure5LowerRotation A)).lo
          (A.rotate (figure5LowerRotation A)).hi ⊆ Icc 0 t ∧
      (A.rotate (figure5LowerRotation A)).lo = 0 := by
  obtain ⟨n, hn⟩ := H.changed
  have hcarrier : D.firstArc.carrier = A.carrier := by
    rw [← hn, NormalizedPolarArc.changeLift_carrier]
  have hlo := (H.in_target ⟨le_rfl, A.le_endpoints⟩).1
  have hhi := (H.in_target ⟨A.le_endpoints, le_rfl⟩).2
  constructor
  · simpa only [NormalizedPolarArc.rotate_carrier, add_comm] using congrArg
      (fun S : Set PolarAngle => (fun z : PolarAngle =>
        z + (figure5LowerRotation A : PolarAngle)) '' S) hcarrier
  constructor
  · intro x hx
    change A.lo + (-A.lo) ≤ x ∧ x ≤ A.hi + (-A.lo) at hx
    change 0 ≤ x ∧ x ≤ t
    constructor <;> linarith [hlo, hhi]
  · simp [figure5LowerRotation, NormalizedPolarArc.rotate]

/-- The two proved local endpoint inequalities imply the desired open
projective containment.  No global direction set occurs. -/
theorem figure5_local_contact_pointwise
    {r t gamma : ℝ} {A : NormalizedPolarArc}
    (_ht : 0 ≤ t) (hA : Icc A.lo A.hi ⊆ Icc 0 t)
    (hu : 2 * figure5UpperAnalyticAngle gamma t A - t < strongPaperG r * t)
    (hl : 2 * figure5LowerAnalyticAngle gamma t A - t < strongPaperG r * t) :
    (gamma : ProjectiveDirection) ∈
      quotientCenteredDilate (strongPaperG r) Real.pi (t / 2) (t / 2) := by
  have hloA := (hA ⟨le_rfl, A.le_endpoints⟩).1
  have hhiA := (hA ⟨A.le_endpoints, le_rfl⟩).2
  have hlow : t / 2 - strongPaperG r * (t / 2) < gamma := by
    simp only [figure5LowerAnalyticAngle] at hl
    have hm : strongPaperG r * (t / 2) = strongPaperG r * t / 2 := by ring
    rw [hm]
    linarith
  have hupp : gamma < t / 2 + strongPaperG r * (t / 2) := by
    change 2 * (gamma + t - A.hi) - t < strongPaperG r * t at hu
    have hm : strongPaperG r * (t / 2) = strongPaperG r * t / 2 := by ring
    rw [hm]
    linarith
  by_cases hsat : Real.pi ≤
      (t / 2 + strongPaperG r * (t / 2)) -
        (t / 2 - strongPaperG r * (t / 2))
  · rw [quotientCenteredDilate, quotientInterval_eq_univ_of_le hsat]
    exact mem_univ _
  · rw [quotientCenteredDilate, quotientInterval_of_lt (lt_of_not_ge hsat)]
    exact ⟨gamma, ⟨hlow, hupp⟩, rfl⟩

/-! ### Elementary monotonicity helpers on the positive quarter chart -/

theorem figure5_sin_le_sin_of_le {x y : ℝ} (hx : 0 ≤ x) (hy : y ≤ Real.pi / 2)
    (hxy : x ≤ y) : Real.sin x ≤ Real.sin y := by
  apply Real.strictMonoOn_sin.monotoneOn
  · exact ⟨by linarith [Real.pi_pos], by linarith⟩
  · exact ⟨by linarith [hx, hxy], hy⟩
  · exact hxy

theorem figure5_cos_le_cos_of_le {x y : ℝ} (hx : 0 ≤ x) (hy : y ≤ Real.pi)
    (hxy : x ≤ y) : Real.cos y ≤ Real.cos x := by
  apply Real.strictAntiOn_cos.antitoneOn
  · exact ⟨hx, by linarith⟩
  · exact ⟨by linarith, hy⟩
  · exact hxy

/-! ### Which contact equality holds at each end of a principal piece

The two lemmas below are the entire source of endpoint activity used later.
They are proved by an openness argument on the defining inequalities, so no
active pair is ever accepted as an input. -/

/-- The lower endpoint of a nonempty left piece is `basePlus`-active. -/
theorem principalTraceLeftPiece_lo_basePlus
    {δ a b k lo hi : ℝ} (hδ : 0 < δ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hle : lo ≤ hi)
    (hcover : principalTraceLeftPiece δ a b k = Icc lo hi) :
    δ * Real.cos lo = b * Real.sin lo ∧ lo ∈ Icc 0 (Real.arcsin k) := by
  have hloMem : lo ∈ principalTraceLeftPiece δ a b k :=
    hcover.symm ▸ ⟨le_rfl, hle⟩
  rcases hloMem with ⟨hloI, hloLower, hloUpper⟩
  refine ⟨?_, hloI⟩
  by_contra hne
  have hUpper : δ * Real.cos lo < b * Real.sin lo := lt_of_le_of_ne hloUpper hne
  have hlohalf : lo ≤ Real.pi / 2 := hloI.2.trans (Real.arcsin_le_pi_div_two k)
  have hlo0 : 0 < lo := by
    by_contra hnot
    have heq : lo = 0 := le_antisymm (le_of_not_gt hnot) hloI.1
    rw [heq] at hUpper; simp at hUpper; linarith
  have hopen : IsOpen {x : ℝ | δ * Real.cos x < b * Real.sin x} :=
    isOpen_lt (continuous_const.mul Real.continuous_cos)
      (continuous_const.mul Real.continuous_sin)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen lo hUpper
  let x := lo - min ε lo / 2
  have hmin : 0 < min ε lo := lt_min hε hlo0
  have hxlt : x < lo := by dsimp [x]; linarith
  have hx0 : 0 ≤ x := by
    dsimp [x]; have := min_le_right ε lo; linarith
  have hxhalf : x ≤ Real.pi / 2 := by linarith
  have hxball : x ∈ Metric.ball lo ε := by
    rw [Metric.mem_ball]; simp only [Real.dist_eq, x]
    have hm : min ε lo ≤ ε := min_le_left _ _
    rw [abs_of_nonpos (by linarith)]; linarith
  have hxBasePlus : δ * Real.cos x < b * Real.sin x := hball hxball
  have hsinx : Real.sin x ≤ Real.sin lo := figure5_sin_le_sin_of_le hx0 hlohalf hxlt.le
  have hcosx : Real.cos lo ≤ Real.cos x :=
    figure5_cos_le_cos_of_le hx0 (by linarith [Real.pi_pos]) hxlt.le
  have hsinx0 : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [Real.pi_pos])
  have hcosx0 : 0 ≤ Real.cos x :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hxhalf⟩
  have hxBaseMinus : a * Real.sin x ≤ δ * Real.cos x := by
    rcases lt_or_ge a 0 with ha | ha
    · nlinarith
    · calc a * Real.sin x ≤ a * Real.sin lo := by nlinarith
        _ ≤ δ * Real.cos lo := hloLower
        _ ≤ δ * Real.cos x := by nlinarith
  have hxarcsin : x ≤ Real.arcsin k := by linarith [hloI.2]
  have hxPiece : x ∈ principalTraceLeftPiece δ a b k :=
    ⟨⟨hx0, hxarcsin⟩, hxBaseMinus, hxBasePlus.le⟩
  have hxIcc : x ∈ Icc lo hi := hcover ▸ hxPiece
  linarith [hxIcc.1]

/-- The upper endpoint of a nonempty left piece is `circle`- or
`baseMinus`-active. -/
theorem principalTraceLeftPiece_hi_circleOrBaseMinus
    {δ a b k lo hi : ℝ} (hδ : 0 < δ) (hk0 : 0 ≤ k) (hk1 : k < 1) (hb : 0 < b)
    (hle : lo ≤ hi)
    (hcover : principalTraceLeftPiece δ a b k = Icc lo hi) :
    (Real.sin hi = k ∨ a * Real.sin hi = δ * Real.cos hi) ∧
      hi ∈ Icc 0 (Real.arcsin k) := by
  have hhiMem : hi ∈ principalTraceLeftPiece δ a b k :=
    hcover.symm ▸ ⟨hle, le_rfl⟩
  rcases hhiMem with ⟨hhiI, hhiLower, hhiUpper⟩
  refine ⟨?_, hhiI⟩
  by_contra hn
  push Not at hn
  obtain ⟨hncircle, hnbase⟩ := hn
  have hhihalf : hi ≤ Real.pi / 2 := hhiI.2.trans (Real.arcsin_le_pi_div_two k)
  have hBaseMinus : a * Real.sin hi < δ * Real.cos hi := lt_of_le_of_ne hhiLower hnbase
  have hhiAsin : hi < Real.arcsin k := by
    apply lt_of_le_of_ne hhiI.2
    intro he; apply hncircle; rw [he]; exact Real.sin_arcsin (by linarith) hk1.le
  have hopen : IsOpen {x : ℝ | a * Real.sin x < δ * Real.cos x} :=
    isOpen_lt (continuous_const.mul Real.continuous_sin)
      (continuous_const.mul Real.continuous_cos)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen hi hBaseMinus
  let x := hi + min ε (Real.arcsin k - hi) / 2
  have hmin : 0 < min ε (Real.arcsin k - hi) := lt_min hε (sub_pos.mpr hhiAsin)
  have hxgt : hi < x := by dsimp [x]; linarith
  have hxarc : x ≤ Real.arcsin k := by
    dsimp [x]; have := min_le_right ε (Real.arcsin k - hi); linarith
  have hx0 : 0 ≤ x := le_trans hhiI.1 hxgt.le
  have hxhalf : x ≤ Real.pi / 2 := hxarc.trans (Real.arcsin_le_pi_div_two k)
  have hxball : x ∈ Metric.ball hi ε := by
    rw [Metric.mem_ball]; simp only [Real.dist_eq, x]
    have hm : min ε (Real.arcsin k - hi) ≤ ε := min_le_left _ _
    rw [abs_of_nonneg (by linarith)]; linarith
  have hxBaseMinus : a * Real.sin x < δ * Real.cos x := hball hxball
  have hsinx : Real.sin hi ≤ Real.sin x := figure5_sin_le_sin_of_le hhiI.1 hxhalf hxgt.le
  have hcosx : Real.cos x ≤ Real.cos hi :=
    figure5_cos_le_cos_of_le hhiI.1 (by linarith [Real.pi_pos]) hxgt.le
  have hxBasePlus : δ * Real.cos x ≤ b * Real.sin x := by
    calc δ * Real.cos x ≤ δ * Real.cos hi := by nlinarith
      _ ≤ b * Real.sin hi := hhiUpper
      _ ≤ b * Real.sin x := by nlinarith
  have hxPiece : x ∈ principalTraceLeftPiece δ a b k :=
    ⟨⟨hx0, hxarc⟩, hxBaseMinus.le, hxBasePlus⟩
  have hxIcc : x ∈ Icc lo hi := hcover ▸ hxPiece
  linarith [hxIcc.2]

/-- Reflection `φ = π - ψ` identifies the right piece with a sign-flipped left
piece. -/
theorem mem_principalTraceLeftPiece_neg_iff {δ a b k ψ : ℝ} :
    ψ ∈ principalTraceLeftPiece δ (-b) (-a) k ↔
      (Real.pi - ψ) ∈ principalTraceRightPiece δ a b k := by
  simp only [principalTraceLeftPiece, principalTraceRightPiece, Set.mem_inter_iff,
    Set.mem_Icc, Set.mem_setOf_eq, Real.sin_pi_sub, Real.cos_pi_sub]
  constructor
  · rintro ⟨⟨h0, hk⟩, h1, h2⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h0, hk⟩, h1, h2⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem principalTraceLeftPiece_neg_eq_of_right {δ a b k lo hi : ℝ}
    (hcover : principalTraceRightPiece δ a b k = Icc lo hi) :
    principalTraceLeftPiece δ (-b) (-a) k = Icc (Real.pi - hi) (Real.pi - lo) := by
  ext ψ
  rw [mem_principalTraceLeftPiece_neg_iff, hcover, Set.mem_Icc, Set.mem_Icc]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- The upper endpoint of a nonempty right piece is `baseMinus`-active. -/
theorem principalTraceRightPiece_hi_baseMinus
    {δ a b k lo hi : ℝ} (hδ : 0 < δ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hle : lo ≤ hi)
    (hcover : principalTraceRightPiece δ a b k = Icc lo hi) :
    a * Real.sin hi = δ * Real.cos hi ∧
      hi ∈ Icc (Real.pi - Real.arcsin k) Real.pi := by
  have hleftcover := principalTraceLeftPiece_neg_eq_of_right hcover
  obtain ⟨heq, hmem⟩ :=
    principalTraceLeftPiece_lo_basePlus hδ hk0 hk1 (by linarith : Real.pi - hi ≤ Real.pi - lo)
      hleftcover
  rw [Real.sin_pi_sub, Real.cos_pi_sub] at heq
  refine ⟨by linarith, ?_⟩
  rcases hmem with ⟨h0, h1⟩
  exact ⟨by linarith, by linarith⟩

/-- The lower endpoint of a nonempty right piece is `circle`- or
`basePlus`-active. -/
theorem principalTraceRightPiece_lo_circleOrBasePlus
    {δ a b k lo hi : ℝ} (hδ : 0 < δ) (hk0 : 0 ≤ k) (hk1 : k < 1) (ha : a < 0)
    (hle : lo ≤ hi)
    (hcover : principalTraceRightPiece δ a b k = Icc lo hi) :
    (Real.sin lo = k ∨ δ * Real.cos lo = b * Real.sin lo) ∧
      lo ∈ Icc (Real.pi - Real.arcsin k) Real.pi := by
  have hleftcover := principalTraceLeftPiece_neg_eq_of_right hcover
  obtain ⟨hdisj, hmem⟩ :=
    principalTraceLeftPiece_hi_circleOrBaseMinus hδ hk0 hk1 (by linarith : (0:ℝ) < -a)
      (by linarith : Real.pi - hi ≤ Real.pi - lo) hleftcover
  rw [Real.sin_pi_sub, Real.cos_pi_sub] at hdisj
  refine ⟨?_, ?_⟩
  · rcases hdisj with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rcases hmem with ⟨h0, h1⟩
    exact ⟨by linarith, by linarith⟩

/-! ### Polar coordinates of an active support endpoint -/

/-- On the open quarter chart the `basePlus` inequality is exactly an arctangent
comparison. -/
theorem figure5_arctan_le_iff_base {δ B ψ : ℝ} (hB : 0 < B) (hψ0 : 0 ≤ ψ)
    (hψ : ψ < Real.pi / 2) :
    Real.arctan (δ / B) ≤ ψ ↔ δ * Real.cos ψ ≤ B * Real.sin ψ := by
  have hpi := Real.pi_pos
  have hcos : 0 < Real.cos ψ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hψ⟩
  have hψeq : Real.arctan (Real.tan ψ) = ψ := Real.arctan_tan (by linarith) hψ
  constructor
  · intro h
    have hiff := Real.arctan_le_arctan_iff (x := δ / B) (y := Real.tan ψ)
    rw [hψeq] at hiff
    have h' := hiff.1 h
    rw [Real.tan_eq_sin_div_cos, div_le_div_iff₀ hB hcos] at h'
    linarith
  · intro h
    have h' : δ / B ≤ Real.tan ψ := by
      rw [Real.tan_eq_sin_div_cos, div_le_div_iff₀ hB hcos]
      linarith
    have hiff := Real.arctan_le_arctan_iff (x := δ / B) (y := Real.tan ψ)
    rw [hψeq] at hiff
    exact hiff.2 h'

/-- On the open quarter chart the `basePlus` equality names the angle. -/
theorem figure5_arctan_eq_of_base {δ B ψ : ℝ} (hB : 0 < B) (hψ0 : 0 ≤ ψ)
    (hψ : ψ < Real.pi / 2) (hact : δ * Real.cos ψ = B * Real.sin ψ) :
    Real.arctan (δ / B) = ψ := by
  have hpi := Real.pi_pos
  have hcos : 0 < Real.cos ψ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hψ⟩
  have htan : Real.tan ψ = δ / B := by
    rw [Real.tan_eq_sin_div_cos, div_eq_div_iff hcos.ne' hB.ne']
    linarith
  rw [← htan, Real.arctan_tan (by linarith) hψ]

/-- A support endpoint whose contact equality holds at a positive-sine angle is
exactly the polar point at that angle.  This is the only bridge used to produce
base-ray provenance. -/
theorem figure5_supportPoint_polar {α h x φ : ℝ} (hsin : 0 < Real.sin φ)
    (hactive : h * Real.cos φ = x * Real.sin φ) :
    supportPoint α h x =
      scaleCoordinatePlane (h / Real.sin φ) (unitDirection (α + φ)) := by
  have hne := hsin.ne'
  ext
  · simp only [supportPoint, scaleCoordinatePlane, unitDirection, unitNormal,
      addCoordinatePlane, Real.cos_add]
    rw [div_mul_eq_mul_div, eq_div_iff hne]
    linear_combination (-Real.cos α) * hactive
  · simp only [supportPoint, scaleCoordinatePlane, unitDirection, unitNormal,
      addCoordinatePlane, Real.sin_add]
    rw [div_mul_eq_mul_div, eq_div_iff hne]
    linear_combination (-Real.sin α) * hactive

/-- The squared length of a polar point is the square of its radial parameter. -/
theorem figure5_planeNormSq_polar (ρ θ : ℝ) :
    planeNormSq (scaleCoordinatePlane ρ (unitDirection θ)) = ρ ^ 2 := by
  simp only [planeNormSq, scaleCoordinatePlane, unitDirection]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- Full-turn translates of a polar angle name the same direction. -/
theorem figure5_unitDirection_add_int_mul_two_pi (θ : ℝ) (n : ℤ) :
    unitDirection (θ + (n : ℝ) * (2 * Real.pi)) = unitDirection θ := by
  simp [unitDirection, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-! ### The frozen single-ray estimates -/

/-- Elementary sine identity behind the frozen chord comparison. -/
theorem figure5_sin_shift_identity (t S φ : ℝ) :
    Real.sin (t + φ) * Real.sin S - Real.sin (S + φ) * Real.sin t =
      -(Real.sin φ * Real.sin (t - S)) := by
  rw [Real.sin_add, Real.sin_add, Real.sin_sub]; ring

/-- Both constraints consumed by the frozen base-ray estimate follow from the
single-ray chord identity, the physical endpoint norm bound and the fact that
the selected span does not exceed the target chart. -/
theorem figure5_baseBase_constraints
    {h t φ₁ φ₂ R : ℝ} (hh : 0 < h) (hφ₁ : 0 ≤ φ₁) (hle : φ₁ ≤ φ₂)
    (hφ₂ : φ₂ ≤ Real.pi / 2) (hS : φ₂ - φ₁ ≤ t) (ht : t + φ₁ ≤ Real.pi / 2)
    (hchord : Real.sin φ₁ * Real.sin φ₂ = h * Real.sin (φ₂ - φ₁))
    (hnorm : h ≤ R * Real.sin φ₁) :
    Real.sin (t + φ₁) ≤ R * Real.sin t ∧
      Real.sin (t + φ₁) * Real.sin φ₁ ≤ h * Real.sin t := by
  have hpi := Real.pi_pos
  have ht0 : 0 ≤ t := by linarith
  have hs1 : 0 ≤ Real.sin φ₁ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hφ₁ (by linarith)
  have hs1pos : 0 < Real.sin φ₁ := by
    rcases hs1.lt_or_eq with hlt | heq
    · exact hlt
    · rw [← heq] at hnorm; simp at hnorm; linarith
  have hs2 : Real.sin φ₁ ≤ Real.sin φ₂ := figure5_sin_le_sin_of_le hφ₁ hφ₂ hle
  have hs2pos : 0 < Real.sin φ₂ := lt_of_lt_of_le hs1pos hs2
  have hSnn : 0 ≤ φ₂ - φ₁ := by linarith
  have hsS : 0 ≤ Real.sin (φ₂ - φ₁) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hSnn (by linarith)
  have hsSpos : 0 < Real.sin (φ₂ - φ₁) := by
    rcases hsS.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso; rw [← heq] at hchord; nlinarith
  have hsdiff : 0 ≤ Real.sin (t - (φ₂ - φ₁)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hst : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith)
  have hkey : Real.sin (t + φ₁) * Real.sin (φ₂ - φ₁) ≤ Real.sin φ₂ * Real.sin t := by
    have hid := figure5_sin_shift_identity t (φ₂ - φ₁) φ₁
    have hrw : Real.sin ((φ₂ - φ₁) + φ₁) = Real.sin φ₂ := by ring_nf
    rw [hrw] at hid
    nlinarith
  have hheight : Real.sin (t + φ₁) * Real.sin φ₁ ≤ h * Real.sin t := by
    have hmul : Real.sin (t + φ₁) * Real.sin φ₁ * Real.sin (φ₂ - φ₁) ≤
        h * Real.sin t * Real.sin (φ₂ - φ₁) := by nlinarith
    exact le_of_mul_le_mul_right (by linarith [hmul]) hsSpos
  refine ⟨?_, hheight⟩
  have hchain : Real.sin (t + φ₁) * Real.sin φ₁ ≤ R * Real.sin φ₁ * Real.sin t := by
    nlinarith
  have := le_of_mul_le_mul_right (by nlinarith [hchain] :
    Real.sin (t + φ₁) * Real.sin φ₁ ≤ R * Real.sin t * Real.sin φ₁) hs1pos
  exact this

/-! ### Endpoint activity of the actually selected strict presentation -/

/-- If the shifted left principal presentation is present, both of its actual
endpoints satisfy one of the three defining contact equalities.  The activity
pair is derived by opening the concrete `ClosedIccPresentation`; it is not an
input to this theorem. -/
theorem figure5_leftShiftedPresentation_endpoints_active
    {δ a b k α : ℝ} (hδ : 0 < δ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    {B : NormalizedPolarArc}
    (hB : (((principalTraceClosedPresentations (a := a) (b := b) hδ hk0 hk1).1
      ).toShiftedClosedPolarPresentation α
        (fun _ _ h => principalTraceLeftPiece_icc_span_lt hk1 h)).arc = some B) :
    principalTraceLeftPiece δ a b k = Icc (B.lo - α) (B.hi - α) ∧
      PrincipalTraceEndpointActive δ a b k (B.lo - α) ∧
      PrincipalTraceEndpointActive δ a b k (B.hi - α) := by
  let P := (principalTraceClosedPresentations (a := a) (b := b) hδ hk0 hk1).1
  change (P.toShiftedClosedPolarPresentation α _).arc = some B at hB
  cases hP : P with
  | empty hempty =>
      rw [hP] at hB
      simp [ClosedIccPresentation.toShiftedClosedPolarPresentation] at hB
  | interval lo hi hle hcover =>
      rw [hP] at hB
      have hBeq : B =
          { lo := α + lo, hi := α + hi, le_endpoints := by linarith,
            short := by
              simpa only [add_sub_add_left_eq_sub] using
                principalTraceLeftPiece_icc_span_lt hk1 hcover } := by
        simpa [ClosedIccPresentation.toShiftedClosedPolarPresentation] using hB.symm
      subst B
      simp only [add_sub_cancel_left]
      have hcover' : principalTraceLeftPiece δ a b k = Icc lo hi := by
        simpa [P] using hcover
      exact ⟨hcover', principalTraceLeftPiece_interval_lo_active hδ hk0 hk1 hle hcover',
        principalTraceLeftPiece_interval_hi_active hδ hk0 hk1 hle hcover'⟩

/-- An absent left presentation means the left piece is genuinely empty. -/
theorem figure5_leftShiftedPresentation_empty
    {δ a b k α : ℝ} (hδ : 0 < δ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hB : (((principalTraceClosedPresentations (a := a) (b := b) hδ hk0 hk1).1
      ).toShiftedClosedPolarPresentation α
        (fun _ _ h => principalTraceLeftPiece_icc_span_lt hk1 h)).arc = none) :
    principalTraceLeftPiece δ a b k = ∅ := by
  let P := (principalTraceClosedPresentations (a := a) (b := b) hδ hk0 hk1).1
  change (P.toShiftedClosedPolarPresentation α _).arc = none at hB
  cases hP : P with
  | empty hempty => simpa [P] using hempty
  | interval lo hi hle hcover =>
      rw [hP] at hB
      simp [ClosedIccPresentation.toShiftedClosedPolarPresentation] at hB

/-- Right-hand counterpart of
`figure5_leftShiftedPresentation_endpoints_active`. -/
theorem figure5_rightShiftedPresentation_endpoints_active
    {δ a b k α : ℝ} (hδ : 0 < δ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    {B : NormalizedPolarArc}
    (hB : (((principalTraceClosedPresentations (a := a) (b := b) hδ hk0 hk1).2
      ).toShiftedClosedPolarPresentation α
        (fun _ _ h => principalTraceRightPiece_icc_span_lt hk1 h)).arc = some B) :
    principalTraceRightPiece δ a b k = Icc (B.lo - α) (B.hi - α) ∧
      PrincipalTraceEndpointActive δ a b k (B.lo - α) ∧
      PrincipalTraceEndpointActive δ a b k (B.hi - α) := by
  let P := (principalTraceClosedPresentations (a := a) (b := b) hδ hk0 hk1).2
  change (P.toShiftedClosedPolarPresentation α _).arc = some B at hB
  cases hP : P with
  | empty hempty =>
      rw [hP] at hB
      simp [ClosedIccPresentation.toShiftedClosedPolarPresentation] at hB
  | interval lo hi hle hcover =>
      rw [hP] at hB
      have hBeq : B =
          { lo := α + lo, hi := α + hi, le_endpoints := by linarith,
            short := by
              simpa only [add_sub_add_left_eq_sub] using
                principalTraceRightPiece_icc_span_lt hk1 hcover } := by
        simpa [ClosedIccPresentation.toShiftedClosedPolarPresentation] using hB.symm
      subst B
      simp only [add_sub_cancel_left]
      have hcover' : principalTraceRightPiece δ a b k = Icc lo hi := by
        simpa [P] using hcover
      exact ⟨hcover', principalTraceRightPiece_interval_lo_active hδ hk0 hk1 hle hcover',
        principalTraceRightPiece_interval_hi_active hδ hk0 hk1 hle hcover'⟩

/-- An absent right presentation means the right piece is genuinely empty. -/
theorem figure5_rightShiftedPresentation_empty
    {δ a b k α : ℝ} (hδ : 0 < δ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hB : (((principalTraceClosedPresentations (a := a) (b := b) hδ hk0 hk1).2
      ).toShiftedClosedPolarPresentation α
        (fun _ _ h => principalTraceRightPiece_icc_span_lt hk1 h)).arc = none) :
    principalTraceRightPiece δ a b k = ∅ := by
  let P := (principalTraceClosedPresentations (a := a) (b := b) hδ hk0 hk1).2
  change (P.toShiftedClosedPolarPresentation α _).arc = none at hB
  cases hP : P with
  | empty hempty => simpa [P] using hempty
  | interval lo hi hle hcover =>
      rw [hP] at hB
      simp [ClosedIccPresentation.toShiftedClosedPolarPresentation] at hB

/-- In the strict-height regime the arc named by `Figure5SelectedChangedLift`
is literally one of the two shifted principal presentations, and both of that
presentation's endpoints are active.  Empty/one/two presentation cases and the
component-zero tie rule are discharged by `selectedArcOfOptions?`; no active
pair is accepted from the caller. -/
theorem figure5_selected_strict_presentation_endpoints_active
    {r t : ℝ} {q : DirectedSupportParameter}
    {D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r}
    {A : NormalizedPolarArc}
    (hsupport : Figure5PositiveNormalizedSupport r strongA strongR₁ q)
    (hheight_strict : q.2.1 < r)
    (hselected : Figure5SelectedChangedLift r t q D A) :
    (D.firstArc =
        (principalTraceShiftedClosedPolarPresentations
          (a := q.2.2 - 1 / 2) (b := q.2.2 + 1 / 2) q.1
          hsupport.height_pos
          (div_nonneg hsupport.height_pos.le hsupport.radius_pos.le)
          ((div_lt_one hsupport.radius_pos).2 hheight_strict)).1.arc.getD D.firstArc ∧
      principalTraceLeftPiece q.2.1 (q.2.2 - 1 / 2) (q.2.2 + 1 / 2) (q.2.1 / r) =
        Icc (D.firstArc.lo - q.1) (D.firstArc.hi - q.1) ∧
      ∀ lo hi : ℝ, lo ≤ hi →
        Icc lo hi ⊆ principalTraceRightPiece q.2.1 (q.2.2 - 1 / 2) (q.2.2 + 1 / 2)
          (q.2.1 / r) → hi - lo ≤ D.firstArc.hi - D.firstArc.lo) ∨
    (D.firstArc =
        (principalTraceShiftedClosedPolarPresentations
          (a := q.2.2 - 1 / 2) (b := q.2.2 + 1 / 2) q.1
          hsupport.height_pos
          (div_nonneg hsupport.height_pos.le hsupport.radius_pos.le)
          ((div_lt_one hsupport.radius_pos).2 hheight_strict)).2.arc.getD D.firstArc ∧
      principalTraceRightPiece q.2.1 (q.2.2 - 1 / 2) (q.2.2 + 1 / 2) (q.2.1 / r) =
        Icc (D.firstArc.lo - q.1) (D.firstArc.hi - q.1) ∧
      ∀ lo hi : ℝ, lo ≤ hi →
        Icc lo hi ⊆ principalTraceLeftPiece q.2.1 (q.2.2 - 1 / 2) (q.2.2 + 1 / 2)
          (q.2.1 / r) → hi - lo ≤ D.firstArc.hi - D.firstArc.lo) := by
  let hk0 : 0 ≤ q.2.1 / r := div_nonneg hsupport.height_pos.le hsupport.radius_pos.le
  let hk1 : q.2.1 / r < 1 := (div_lt_one hsupport.radius_pos).2 hheight_strict
  let S := principalTraceShiftedClosedPolarPresentations
    (a := q.2.2 - 1 / 2) (b := q.2.2 + 1 / 2) q.1
    hsupport.height_pos hk0 hk1
  have hraw := hselected.selected
  rw [selectedSupportFirstArc?, dif_pos hsupport.radius_pos,
    dif_pos hsupport.height_pos.le, dif_pos hsupport.height_le_radius,
    supportTraceFirstArcData?, supportTraceClosedDecomposition,
    dif_neg hsupport.height_pos.ne', dif_neg hheight_strict.ne] at hraw
  change (principalTraceClosedDecomposition hsupport.radius_pos hsupport.height_pos
    hheight_strict).toFirstArcData?.map FirstArcData.firstArc = some D.firstArc at hraw
  have hoptions : selectedArcOfOptions? S.1.arc S.2.arc = some D.firstArc := by
    rw [← closedTraceDecomposition_firstArc_eq_selectedArcOfOptions S.1 S.2
      (principalTraceShiftedClosedPolarPresentations_cover hsupport.radius_pos
        hsupport.height_pos hheight_strict)
      (disjoint_principalTraceClosedPresentations hk0 hk1 S.1 S.2)]
    exact hraw
  cases hL : S.1.arc with
  | none =>
      cases hR : S.2.arc with
      | none => simp [hL, hR, selectedArcOfOptions?] at hoptions
      | some R =>
          have hDR : D.firstArc = R := by
            simpa [hL, hR, selectedArcOfOptions?] using hoptions.symm
          right
          have hact := figure5_rightShiftedPresentation_endpoints_active
            hsupport.height_pos hk0 hk1 (by simpa [S] using hR)
          have hempty := figure5_leftShiftedPresentation_empty
            hsupport.height_pos hk0 hk1 (by simpa [S] using hL)
          subst R
          refine ⟨by simp, ?_, ?_⟩
          · norm_num at hact ⊢
            exact hact.1
          · intro lo hi hle hcov
            have hmem : lo ∈ (∅ : Set ℝ) := hempty ▸ hcov (⟨le_rfl, hle⟩ : lo ∈ Icc lo hi)
            simp at hmem
  | some L =>
      cases hR : S.2.arc with
      | none =>
          have hDL : D.firstArc = L := by
            simpa [hL, hR, selectedArcOfOptions?] using hoptions.symm
          left
          have hact := figure5_leftShiftedPresentation_endpoints_active
            hsupport.height_pos hk0 hk1 (by simpa [S] using hL)
          have hempty := figure5_rightShiftedPresentation_empty
            hsupport.height_pos hk0 hk1 (by simpa [S] using hR)
          subst L
          refine ⟨by simp, ?_, ?_⟩
          · norm_num at hact ⊢
            exact hact.1
          · intro lo hi hle hcov
            have hmem : lo ∈ (∅ : Set ℝ) := hempty ▸ hcov (⟨le_rfl, hle⟩ : lo ∈ Icc lo hi)
            simp at hmem
      | some R =>
          have hactL := figure5_leftShiftedPresentation_endpoints_active
            hsupport.height_pos hk0 hk1 (by simpa [S] using hL)
          have hactR := figure5_rightShiftedPresentation_endpoints_active
            hsupport.height_pos hk0 hk1 (by simpa [S] using hR)
          by_cases hwin : R.span ≤ L.span
          · have hDL : D.firstArc = L := by
              simpa [hL, hR, hwin, selectedArcOfOptions?] using hoptions.symm
            left
            subst L
            refine ⟨by simp, ?_, ?_⟩
            · norm_num at hactL ⊢
              exact hactL.1
            · intro lo hi hle hcov
              have hR' : Icc lo hi ⊆ Icc (R.lo - q.1) (R.hi - q.1) := by
                refine hcov.trans ?_
                norm_num at hactR ⊢
                exact hactR.1.le
              have h1 := hR' (⟨le_rfl, hle⟩ : lo ∈ Icc lo hi)
              have h2 := hR' (⟨hle, le_rfl⟩ : hi ∈ Icc lo hi)
              have := hwin
              simp only [NormalizedPolarArc.span] at this
              simp only [Set.mem_Icc] at h1 h2
              linarith [h1.1, h2.2]
          · have hDR : D.firstArc = R := by
              simpa [hL, hR, hwin, selectedArcOfOptions?] using hoptions.symm
            right
            have hwin' : L.span ≤ R.span := le_of_not_ge hwin
            subst R
            refine ⟨by simp, ?_, ?_⟩
            · norm_num at hactR ⊢
              exact hactR.1
            · intro lo hi hle hcov
              have hL' : Icc lo hi ⊆ Icc (L.lo - q.1) (L.hi - q.1) := by
                refine hcov.trans ?_
                norm_num at hactL ⊢
                exact hactL.1.le
              have h1 := hL' (⟨le_rfl, hle⟩ : lo ∈ Icc lo hi)
              have h2 := hL' (⟨hle, le_rfl⟩ : hi ∈ Icc lo hi)
              have := hwin'
              simp only [NormalizedPolarArc.span] at this
              simp only [Set.mem_Icc] at h1 h2
              linarith [h1.1, h2.2]

/-! ### The selected side determines the sign of the needle centre -/

/-- If the actually selected component is the left mixed one, its centre is
nonnegative: otherwise the reflected right piece contains a strictly longer
closed interval, contradicting selection of the longest span. -/
theorem figure5_left_centre_nonneg
    {δ k c φlo φhi : ℝ} (hδ : 0 < δ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hle : φlo ≤ φhi)
    (hcover : principalTraceLeftPiece δ (c - 1 / 2) (c + 1 / 2) k = Icc φlo φhi)
    (hcircle : Real.sin φhi = k)
    (hdom : ∀ lo hi : ℝ, lo ≤ hi →
      Icc lo hi ⊆ principalTraceRightPiece δ (c - 1 / 2) (c + 1 / 2) k →
      hi - lo ≤ φhi - φlo) :
    0 ≤ c := by
  have hpi := Real.pi_pos
  have harc : Real.arcsin k < Real.pi / 2 := Real.arcsin_lt_pi_div_two.2 hk1
  have harc0 : 0 ≤ Real.arcsin k := Real.arcsin_nonneg.2 hk0
  obtain ⟨hplus, hlomem⟩ :=
    principalTraceLeftPiece_lo_basePlus hδ hk0 hk1 hle hcover
  have hhiMem : φhi ∈ principalTraceLeftPiece δ (c - 1 / 2) (c + 1 / 2) k :=
    hcover.symm ▸ ⟨hle, le_rfl⟩
  have hhimem : φhi ∈ Icc 0 (Real.arcsin k) := hhiMem.1
  have hlo0 : 0 ≤ φlo := hlomem.1
  have hlo1 : φlo ≤ Real.arcsin k := hlomem.2
  have hhi0 : 0 ≤ φhi := hhimem.1
  have hhi1 : φhi ≤ Real.arcsin k := hhimem.2
  have hlolt : φlo < Real.pi / 2 := lt_of_le_of_lt hlo1 harc
  have hcoslo : 0 < Real.cos φlo :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hlolt⟩
  have hsinlo : 0 ≤ Real.sin φlo :=
    Real.sin_nonneg_of_nonneg_of_le_pi hlo0 (by linarith)
  have hsinpos : 0 < Real.sin φlo := by
    rcases hsinlo.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      rw [← heq, mul_zero] at hplus
      nlinarith [mul_pos hδ hcoslo]
  have hb : 0 < c + 1 / 2 := by
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith [mul_pos hδ hcoslo, mul_nonneg (neg_nonneg.2 hcon) hsinpos.le]
  have hφhi_eq : φhi = Real.arcsin k := by
    have hs := Real.arcsin_sin (x := φhi) (by linarith) (by linarith)
    rw [hcircle] at hs
    exact hs.symm
  by_contra hc
  rw [not_le] at hc
  have hB : 0 < 1 / 2 - c := by linarith
  have hφlo_eq : Real.arctan (δ / (c + 1 / 2)) = φlo :=
    figure5_arctan_eq_of_base hb hlo0 hlolt hplus
  have hfrac : δ / (1 / 2 - c) < δ / (c + 1 / 2) :=
    div_lt_div_of_pos_left hδ hb (by linarith)
  have hψlt : Real.arctan (δ / (1 / 2 - c)) < φlo := by
    rw [← hφlo_eq]
    exact Real.arctan_strictMono hfrac
  have hψ0 : 0 ≤ Real.arctan (δ / (1 / 2 - c)) :=
    Real.arctan_nonneg.2 (by positivity)
  have hsub : Icc (Real.pi - Real.arcsin k)
      (Real.pi - Real.arctan (δ / (1 / 2 - c))) ⊆
      principalTraceRightPiece δ (c - 1 / 2) (c + 1 / 2) k := by
    intro x hx
    have hx1 : Real.pi - x ≤ Real.arcsin k := by linarith [hx.1]
    have hx2 : Real.arctan (δ / (1 / 2 - c)) ≤ Real.pi - x := by linarith [hx.2]
    have hxlt : Real.pi - x < Real.pi / 2 := lt_of_le_of_lt hx1 harc
    have hx0 : 0 ≤ Real.pi - x := le_trans hψ0 hx2
    have hcosx : 0 < Real.cos (Real.pi - x) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, hxlt⟩
    have hsinx : 0 ≤ Real.sin (Real.pi - x) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith)
    have hupper : δ * Real.cos (Real.pi - x) ≤
        (1 / 2 - c) * Real.sin (Real.pi - x) :=
      (figure5_arctan_le_iff_base hB hx0 hxlt).1 hx2
    have hmem : (Real.pi - x) ∈
        principalTraceLeftPiece δ (-(c + 1 / 2)) (-(c - 1 / 2)) k := by
      refine ⟨⟨hx0, hx1⟩, ?_, ?_⟩
      · nlinarith
      · linarith
    have hfinal := mem_principalTraceLeftPiece_neg_iff.1 hmem
    simpa using hfinal
  have hlelo : Real.pi - Real.arcsin k ≤
      Real.pi - Real.arctan (δ / (1 / 2 - c)) := by linarith
  have hdom' := hdom _ _ hlelo hsub
  linarith

/-- The mirror statement for a selected right mixed component. -/
theorem figure5_right_centre_nonpos
    {δ k c φlo φhi : ℝ} (hδ : 0 < δ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hle : φlo ≤ φhi)
    (hcover : principalTraceRightPiece δ (c - 1 / 2) (c + 1 / 2) k = Icc φlo φhi)
    (hcircle : Real.sin φlo = k)
    (hdom : ∀ lo hi : ℝ, lo ≤ hi →
      Icc lo hi ⊆ principalTraceLeftPiece δ (c - 1 / 2) (c + 1 / 2) k →
      hi - lo ≤ φhi - φlo) :
    c ≤ 0 := by
  have hcover' : principalTraceLeftPiece δ (-c - 1 / 2) (-c + 1 / 2) k =
      Icc (Real.pi - φhi) (Real.pi - φlo) := by
    rw [show -c - 1 / 2 = -(c + 1 / 2) by ring, show -c + 1 / 2 = -(c - 1 / 2) by ring]
    exact principalTraceLeftPiece_neg_eq_of_right hcover
  have hcircle' : Real.sin (Real.pi - φlo) = k := by
    rw [Real.sin_pi_sub]; exact hcircle
  have hdom' : ∀ lo hi : ℝ, lo ≤ hi →
      Icc lo hi ⊆ principalTraceRightPiece δ (-c - 1 / 2) (-c + 1 / 2) k →
      hi - lo ≤ (Real.pi - φlo) - (Real.pi - φhi) := by
    intro lo hi hlehi hs
    have hs' : Icc (Real.pi - hi) (Real.pi - lo) ⊆
        principalTraceLeftPiece δ (c - 1 / 2) (c + 1 / 2) k := by
      intro y hy
      have hy' : Real.pi - y ∈ Icc lo hi := ⟨by linarith [hy.2], by linarith [hy.1]⟩
      have hthis := hs hy'
      rw [show c - 1 / 2 = -(-c + 1 / 2) by ring,
        show c + 1 / 2 = -(-c - 1 / 2) by ring]
      exact mem_principalTraceLeftPiece_neg_iff.2 hthis
    have := hdom _ _ (by linarith : Real.pi - hi ≤ Real.pi - lo) hs'
    linarith
  have := figure5_left_centre_nonneg (c := -c) hδ hk0 hk1
    (by linarith : Real.pi - φhi ≤ Real.pi - φlo) hcover' hcircle' hdom'
  linarith

/-- Source-free geometric classification of one normalized selected endpoint.
`mixed` is the new selected-longest closure: it stores the actual selected span,
not a preassembled height cutoff.  `baseBase` is the only constructor carrying
the two constraints used by the frozen single-ray estimate. -/
inductive Figure5SelectedGapGeometry (r t δ₀ α : ℝ)
    (q : DirectedSupportParameter) (A : NormalizedPolarArc) : Prop where
  | nearHalf
      (hr : r ∈ Icc strongA strongR₀)
      (ht0 : 0 < t) (hhalf : α ≤ t) :
      Figure5SelectedGapGeometry r t δ₀ α q A
  | height
      (hr : r ∈ Icc strongA strongR₀)
      (hδ0 : 0 < δ₀) (hδr : δ₀ < r)
      (ht : strongEndpointPhi r δ₀ ≤ t)
      (alpha_chart : α ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
      (height_cutoff : Real.sin α ≤ δ₀ / r) :
      Figure5SelectedGapGeometry r t δ₀ α q A
  | mixed
      (hr : r ∈ Icc strongA strongR₀)
      (hδ0 : 0 < δ₀) (hδr : δ₀ < r)
      (ht : t = strongEndpointPhi r δ₀)
      (height_lt_radius : q.2.1 < r)
      (x effectiveBase : ℝ) (base_ge_half : 1 / 2 ≤ effectiveBase)
      (base_angle : x = Real.arctan (q.2.1 / effectiveBase))
      (selected_span : A.span = Real.arcsin (q.2.1 / r) - x)
      (alpha_chart : α ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
      (side_sin : Real.sin α ≤ q.2.1 / r) :
      Figure5SelectedGapGeometry r t δ₀ α q A
  | baseBase
      (hr : r ∈ Icc strongA strongR₀)
      (ht0 : 0 < t)
      (htop : t < Real.pi / 2 - Real.arctan (2 * r))
      (hhalf : t / 2 ≤ α)
      (halpha : α ∈ Icc 0 (Real.pi / 2))
      (hsint : 0 ≤ Real.sin t)
      (radius_constraint : Real.sin α ≤ strongR₁ * Real.sin t)
      (height_constraint : Real.sin α * Real.sin (α - t) ≤
        strongA * Real.sin t)
      (raw : Figure5BaseRayRawProvenance t q) :
      Figure5SelectedGapGeometry r t δ₀ α q A

/-- Endpoint activity plus selected-longest span comparison automatically
produces the analytic source sum.  No source is retained by the caller. -/
theorem Figure5SelectedGapGeometry.toGapSource
    {r t δ₀ α : ℝ} {q : DirectedSupportParameter} {A : NormalizedPolarArc}
    (G : Figure5SelectedGapGeometry r t δ₀ α q A)
    (hheight : 0 < q.2.1) (hheightA : q.2.1 ≤ strongA)
    (hselected : Icc A.lo A.hi ⊆ Icc 0 t) :
    Figure5UpperGapSource r t δ₀ α q := by
  cases G with
  | nearHalf hr ht0 hhalf =>
      exact .nearHalf hr ht0 hhalf
  | height hr hδ0 hδr ht hchart hcut =>
      exact .heightCutoff hr hδ0 hδr ht hchart hcut
  | mixed hr hδ0 hδr ht hhr x effectiveBase hbase hx hspan hchart hside =>
      have hr0 : 0 < r := strongParameterDomain.a_pos.trans_le hr.1
      have hrhalf : r < 1 / 2 := hr.2.trans_lt
        strongParameterDomain.r₀_lt_half
      have hspanUpper : A.span ≤ t := by
        have hlo := (hselected ⟨le_rfl, A.le_endpoints⟩).1
        have hhi := (hselected ⟨A.le_endpoints, le_rfl⟩).2
        dsimp [NormalizedPolarArc.span]
        linarith
      have hlower : strongEndpointPhi r q.2.1 ≤ A.span :=
        strongEndpointPhi_le_of_mixedSpan hheight.le hbase hx hspan
      have hheight' : q.2.1 ≤ δ₀ := by
        apply strongEndpointPhi_le_of_le hr0 hrhalf ⟨hheight.le, hhr⟩
          ⟨hδ0.le, hδr⟩
        rw [← ht]
        exact hlower.trans hspanUpper
      have hratio : q.2.1 / r ≤ δ₀ / r :=
        (div_le_div_iff_of_pos_right hr0).2 hheight'
      exact .heightCutoff hr hδ0 hδr ht.ge hchart (hside.trans hratio)
  | baseBase hr ht0 htop hhalf halpha hsint hR hh raw =>
      exact .baseRayCutoff hr ht0 htop hhalf halpha hsint hR hh raw

/-- The reflected changed lift used by the lower normalization. -/
def figure5ReflectedLowerArc (t : ℝ) (A : NormalizedPolarArc) : NormalizedPolarArc :=
  (A.rotate (figure5LowerRotation A)).reverse.rotate t

/-- Reflection sends the lower-normalized selected interval back into `[0,t]`. -/
theorem Figure5SelectedChangedLift.reflected_lower_lift
    {r t : ℝ} {q : DirectedSupportParameter}
    {D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r}
    {A : NormalizedPolarArc}
    (H : Figure5SelectedChangedLift r t q D A) :
    Icc (figure5ReflectedLowerArc t A).lo
      (figure5ReflectedLowerArc t A).hi ⊆ Icc 0 t := by
  have hlow := H.lower_rotated_lift.2.1
  intro x hx
  have hlo : 0 ≤ (A.rotate (figure5LowerRotation A)).lo :=
    (hlow ⟨le_rfl, (A.rotate (figure5LowerRotation A)).le_endpoints⟩).1
  have hhi : (A.rotate (figure5LowerRotation A)).hi ≤ t :=
    (hlow ⟨(A.rotate (figure5LowerRotation A)).le_endpoints, le_rfl⟩).2
  change -(A.hi + figure5LowerRotation A) + t ≤ x ∧
    x ≤ -(A.lo + figure5LowerRotation A) + t at hx
  simp only [figure5LowerRotation, NormalizedPolarArc.rotate_lo,
    NormalizedPolarArc.rotate_hi] at hlo hhi hx
  change 0 ≤ x ∧ x ≤ t
  constructor <;> linarith [A.le_endpoints]

/-- A local certificate for one chosen direction.  It records only a normalized
support, its selected arc/lift, and the two endpoint classifications after the
explicit normalizations above. -/
structure Figure5LocalContactCertificate (r t : ℝ)
    (d : ProjectiveDirection) where
  q : DirectedSupportParameter
  D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r
  A : NormalizedPolarArc
  gamma : ℝ
  support : Figure5PositiveNormalizedSupport r strongA strongR₁ q
  selectedLift : Figure5SelectedChangedLift r t q D A
  gamma_direction : (gamma : ProjectiveDirection) = d
  upper_gap : 2 * figure5UpperAnalyticAngle gamma t A - t < strongPaperG r * t
  lower_gap : 2 * figure5LowerAnalyticAngle gamma t A - t < strongPaperG r * t

/-- Target-height relation for the actual selected component, expressed using
an orientation-aware analytic lift.  Both endpoints are read in the honest
rotated support charts, so that the base-ray provenance stored by the base
branch is a genuine statement about the physical needle endpoints. -/
structure Figure5ActualSelectedTargetRelation
    (r t δ₀ gamma : ℝ) (q : DirectedSupportParameter)
    (D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r)
    (A : NormalizedPolarArc) : Prop where
  target_eq : t = strongEndpointPhi r δ₀
  upper : Figure5SelectedGapGeometry r t δ₀
    (figure5UpperAnalyticAngle gamma t A)
    (figure5UpperSupport t A q)
    (A.rotate (figure5UpperRotation t A))
  lower : Figure5SelectedGapGeometry r t δ₀
    (figure5LowerAnalyticAngle gamma t A)
    (figure5LowerSupport A q)
    (figure5ReflectedLowerArc t A)

/-! ### The two branch constructors used by the internal assembly -/

/-- Monotonicity of `sin` on the full closed quarter-turn chart. -/
theorem figure5_sin_le_sin_of_le' {x y : ℝ} (hx : -(Real.pi / 2) ≤ x)
    (hy : y ≤ Real.pi / 2) (hxy : x ≤ y) : Real.sin x ≤ Real.sin y := by
  apply Real.strictMonoOn_sin.monotoneOn
  · exact ⟨hx, by linarith⟩
  · exact ⟨by linarith, hy⟩
  · exact hxy

/-- The endpoint on the near side of the target chart never exceeds the target
height circle.  This is the branch used by both easy endpoints; it needs only
that the analytic lift does not exceed the far end of the target chart. -/
theorem figure5_easy_gapGeometry
    {r t δ₀ α : ℝ} {qq : DirectedSupportParameter} {AA : NormalizedPolarArc}
    (hr : r ∈ Icc strongA strongR₀)
    (ht0 : 0 < t) (hup : α ≤ t) :
    Figure5SelectedGapGeometry r t δ₀ α qq AA :=
  .nearHalf hr ht0 hup

/-- The mixed hard endpoint.  The selected-longest span forces the physical
height below the target height, hence the analytic lift stays below the target
height circle.  The comparison height `δ₀` is only required to be an admissible
height for the radius (`0 < δ₀ < r`); no cap by `strongA` is used. -/
theorem figure5_hard_mixed_gapGeometry
    {r t δ₀ h base spanA α : ℝ} {qq : DirectedSupportParameter}
    {AA : NormalizedPolarArc}
    (hr : r ∈ Icc strongA strongR₀)
    (hδ0 : 0 < δ₀) (hδr : δ₀ < r)
    (ht : t = strongEndpointPhi r δ₀) (ht0 : 0 ≤ t) (hrpos : 0 < r)
    (hh0 : 0 < h) (hhr : h < r) (hbase : 1 / 2 ≤ base)
    (hspan : spanA = Real.arcsin (h / r) - Real.arctan (h / base))
    (hspant : spanA ≤ t) (hα : α = t + Real.arctan (h / base)) :
    Figure5SelectedGapGeometry r t δ₀ α qq AA := by
  have hrhalf : r < 1 / 2 := hr.2.trans_lt strongParameterDomain.r₀_lt_half
  have hlower : strongEndpointPhi r h ≤ spanA :=
    strongEndpointPhi_le_of_mixedSpan hh0.le hbase rfl hspan
  have hheight : h ≤ δ₀ := by
    apply strongEndpointPhi_le_of_le hrpos hrhalf ⟨hh0.le, hhr⟩ ⟨hδ0.le, hδr⟩
    rw [← ht]
    exact hlower.trans hspant
  have hbase0 : (0 : ℝ) < base := by linarith
  have hquot : h / base ≤ 2 * δ₀ := by
    rw [div_le_iff₀ hbase0]
    nlinarith
  have hatan : Real.arctan (h / base) ≤ Real.arctan (2 * δ₀) :=
    Real.arctan_mono hquot
  have hatan0 : 0 ≤ Real.arctan (h / base) :=
    Real.arctan_nonneg.2 (by positivity)
  have harg0 : (0 : ℝ) < δ₀ / r := div_pos hδ0 hrpos
  have harg1 : δ₀ / r < 1 := (div_lt_one hrpos).2 hδr
  have hαle : α ≤ Real.arcsin (δ₀ / r) := by
    rw [hα, ht, strongEndpointPhi]
    linarith
  have harcle : Real.arcsin (δ₀ / r) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hα0 : 0 ≤ α := by rw [hα]; linarith
  have hpi := Real.pi_pos
  refine .height hr hδ0 hδr ht.ge ⟨by linarith, by linarith⟩ ?_
  have hsin : Real.sin α ≤ Real.sin (Real.arcsin (δ₀ / r)) :=
    figure5_sin_le_sin_of_le' (by linarith) harcle hαle
  rwa [Real.sin_arcsin (by linarith) harg1.le] at hsin

/-- Assemble the raw polar provenance of the two physical base endpoints from
their contact equalities and the chosen chart shift. -/
def figure5_baseRay_provenance
    {t θp θm φp φm : ℝ} {qq : DirectedSupportParameter} (m : ℤ)
    (hh : 0 < qq.2.1)
    (hsp : 0 < Real.sin φp) (hsm : 0 < Real.sin φm)
    (hap : qq.2.1 * Real.cos φp = (qq.2.2 + 1 / 2) * Real.sin φp)
    (ham : qq.2.1 * Real.cos φm = (qq.2.2 - 1 / 2) * Real.sin φm)
    (hθp : qq.1 + φp = θp + (m : ℝ) * (2 * Real.pi))
    (hθm : qq.1 + φm = θm + (m : ℝ) * (2 * Real.pi))
    (hpmem : θp ∈ Icc 0 t) (hmmem : θm ∈ Icc 0 t) :
    Figure5BaseRayRawProvenance t qq where
  thetaPlus := θp
  thetaMinus := θm
  rhoPlus := qq.2.1 / Real.sin φp
  rhoMinus := qq.2.1 / Real.sin φm
  thetaPlus_mem := hpmem
  thetaMinus_mem := hmmem
  rhoPlus_nonneg := div_nonneg hh.le hsp.le
  rhoMinus_nonneg := div_nonneg hh.le hsm.le
  plus_polar := by
    rw [figure5BasePlus, figure5_supportPoint_polar hsp hap, hθp,
      figure5_unitDirection_add_int_mul_two_pi]
  minus_polar := by
    rw [figure5BaseMinus, figure5_supportPoint_polar hsm ham, hθm,
      figure5_unitDirection_add_int_mul_two_pi]

/-- The base-base hard endpoint.  Both constraints consumed by the frozen
single-ray estimate come from the chord identity and the physical endpoint
norm bound. -/
theorem figure5_hard_baseBase_gapGeometry
    {r t δ₀ ψ₁ ψ₂ : ℝ} {qq : DirectedSupportParameter} {AA : NormalizedPolarArc}
    (hr : r ∈ Icc strongA strongR₀)
    (ht0 : 0 < t) (htop : t < Real.pi / 2 - Real.arctan (2 * r))
    (hsint : 0 ≤ Real.sin t)
    (hh0 : 0 < qq.2.1) (hhA : qq.2.1 ≤ strongA)
    (hψ₁ : 0 ≤ ψ₁) (hle : ψ₁ ≤ ψ₂) (hψ₂ : ψ₂ ≤ Real.pi / 2)
    (hS : ψ₂ - ψ₁ ≤ t) (htψ : t + ψ₁ ≤ Real.pi / 2)
    (hchord : Real.sin ψ₁ * Real.sin ψ₂ = qq.2.1 * Real.sin (ψ₂ - ψ₁))
    (hnorm : qq.2.1 ≤ strongR₁ * Real.sin ψ₁)
    (hraw : Figure5BaseRayRawProvenance t qq) :
    Figure5SelectedGapGeometry r t δ₀ (t + ψ₁) qq AA := by
  obtain ⟨hR, hH⟩ :=
    figure5_baseBase_constraints hh0 hψ₁ hle hψ₂ hS htψ hchord hnorm
  refine .baseBase hr ht0 htop (by linarith) ⟨by linarith, htψ⟩ hsint hR ?_ hraw
  have hrw : Real.sin (t + ψ₁) * Real.sin (t + ψ₁ - t) =
      Real.sin (t + ψ₁) * Real.sin ψ₁ := by ring_nf
  rw [hrw]
  nlinarith

/-- The physical endpoint norm bound in polar form. -/
theorem figure5_height_le_radius_mul_sin
    {R h x φ : ℝ} {P : CoordinatePlane} (hR : 0 < R) (hh : 0 < h)
    (hs : 0 < Real.sin φ)
    (hP : P = scaleCoordinatePlane (h / Real.sin φ) (unitDirection x))
    (hnorm : planeNormSq P ≤ R ^ 2) :
    h ≤ R * Real.sin φ := by
  rw [hP, figure5_planeNormSq_polar] at hnorm
  have hρ : h / Real.sin φ ≤ R := by nlinarith [div_nonneg hh.le hs.le]
  rw [div_le_iff₀ hs] at hρ
  linarith

set_option maxHeartbeats 1600000 in
/-- Open the actual selector and its two active endpoints.  The analytic lift is
chosen only after the selector side is known: a left component uses `q.angle`
modulo `2π`, while a right component uses the opposite oriented normal
`q.angle + π` modulo `2π`.  Every branch object is built here; no geometry,
relation or activity datum is accepted as an input. -/
theorem figure5ActualSelectedTargetRelation_of_principal
    {r t δ₀ : ℝ} {q : DirectedSupportParameter}
    {D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r}
    {A : NormalizedPolarArc}
    (hsupport : Figure5PositiveNormalizedSupport r strongA strongR₁ q)
    (hstrict : q.2.1 < r)
    (hselected : Figure5SelectedChangedLift r t q D A)
    (hr : r ∈ Icc strongA strongR₀)
    (hδ0 : 0 < δ₀) (hδr : δ₀ < r)
    (ht : t = strongEndpointPhi r δ₀)
    (ht0 : 0 < t) (htop : t < Real.pi / 2 - Real.arctan (2 * r))
    (hsint : 0 ≤ Real.sin t) :
    ∃ gamma : ℝ, (gamma : ProjectiveDirection) = (q.1 : ProjectiveDirection) ∧
      Figure5ActualSelectedTargetRelation r t δ₀ gamma q D A := by
  classical
  have hpi := Real.pi_pos
  have hrpos : 0 < r := hsupport.radius_pos
  have hh0 : 0 < q.2.1 := hsupport.height_pos
  have hhA : q.2.1 ≤ strongA := hsupport.height_le_a
  have hhr : q.2.1 ≤ r := hsupport.height_le_radius
  have hR₁ : 0 < strongR₁ := by
    have h1 := strong_r₁_gt_rational_lower
    have h2 : (0 : ℝ) < strongR₁Lower := by norm_num [strongR₁Lower]
    linarith
  have hk0 : 0 ≤ q.2.1 / r := div_nonneg hh0.le hrpos.le
  have hk1 : q.2.1 / r < 1 := (div_lt_one hrpos).2 hstrict
  have harck : Real.arcsin (q.2.1 / r) < Real.pi / 2 :=
    Real.arcsin_lt_pi_div_two.2 hk1
  have harck0 : 0 ≤ Real.arcsin (q.2.1 / r) := Real.arcsin_nonneg.2 hk0
  have hatan2r : 0 ≤ Real.arctan (2 * r) := Real.arctan_nonneg.2 (by linarith)
  have htpi : t < Real.pi / 2 := by linarith
  obtain ⟨n, hn⟩ := hselected.changed
  have hAlo : A.lo = D.firstArc.lo + (n : ℝ) * (2 * Real.pi) := by
    rw [← hn]; rfl
  have hAhi : A.hi = D.firstArc.hi + (n : ℝ) * (2 * Real.pi) := by
    rw [← hn]; rfl
  have hAlo0 : 0 ≤ A.lo := (hselected.in_target ⟨le_rfl, A.le_endpoints⟩).1
  have hAhit : A.hi ≤ t := (hselected.in_target ⟨A.le_endpoints, le_rfl⟩).2
  have hspanA : A.span = (D.firstArc.hi - q.1) - (D.firstArc.lo - q.1) := by
    simp only [NormalizedPolarArc.span, hAlo, hAhi]; ring
  have hSt : (D.firstArc.hi - q.1) - (D.firstArc.lo - q.1) ≤ t := by
    have : A.hi - A.lo ≤ t := by linarith
    rw [hAlo, hAhi] at this; linarith
  have hφle : D.firstArc.lo - q.1 ≤ D.firstArc.hi - q.1 := by
    have := A.le_endpoints; rw [hAlo, hAhi] at this; linarith
  -- the chord identity of the two physical endpoints, in the `q` chart
  have hchordBase : ∀ φp φm : ℝ, 0 < Real.sin φp → 0 < Real.sin φm →
      q.2.1 * Real.cos φp = (q.2.2 + 1 / 2) * Real.sin φp →
      q.2.1 * Real.cos φm = (q.2.2 - 1 / 2) * Real.sin φm →
      Real.sin φp * Real.sin φm = q.2.1 * Real.sin (φm - φp) := by
    intro φp φm hsp hsm hap ham
    have hplus : figure5BasePlus q =
        scaleCoordinatePlane (q.2.1 / Real.sin φp) (unitDirection (q.1 + φp)) := by
      rw [figure5BasePlus, figure5_supportPoint_polar hsp hap]
    have hminus : figure5BaseMinus q =
        scaleCoordinatePlane (q.2.1 / Real.sin φm) (unitDirection (q.1 + φm)) := by
      rw [figure5BaseMinus, figure5_supportPoint_polar hsm ham]
    have hid := figure5_single_ray_chord_identity hplus hminus
    rw [show q.1 - (q.1 + φp) = -φp by ring, show q.1 - (q.1 + φm) = -φm by ring,
      show q.1 + φm - (q.1 + φp) = φm - φp by ring, Real.sin_neg, Real.sin_neg] at hid
    linarith [hid]
  rcases figure5_selected_strict_presentation_endpoints_active hsupport hstrict
      hselected with hleft | hright
  · -- the left strict presentation was selected
    obtain ⟨-, hcover, hdom⟩ := hleft
    obtain ⟨hplus, hm1⟩ :=
      principalTraceLeftPiece_lo_basePlus hh0 hk0 hk1 hφle hcover
    have hlo0 : 0 ≤ D.firstArc.lo - q.1 := hm1.1
    have hlo1 : D.firstArc.lo - q.1 ≤ Real.arcsin (q.2.1 / r) := hm1.2
    have hlolt : D.firstArc.lo - q.1 < Real.pi / 2 := lt_of_le_of_lt hlo1 harck
    have hcoslo : 0 < Real.cos (D.firstArc.lo - q.1) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, hlolt⟩
    have hsinlo0 : 0 ≤ Real.sin (D.firstArc.lo - q.1) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hlo0 (by linarith)
    have hsinlo : 0 < Real.sin (D.firstArc.lo - q.1) := by
      rcases hsinlo0.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; rw [← heq, mul_zero] at hplus; nlinarith [mul_pos hh0 hcoslo]
    have hb : 0 < q.2.2 + 1 / 2 := by
      by_contra hcon
      rw [not_lt] at hcon
      nlinarith [mul_pos hh0 hcoslo, mul_nonneg (neg_nonneg.2 hcon) hsinlo.le]
    obtain ⟨hdisj, hm2⟩ :=
      principalTraceLeftPiece_hi_circleOrBaseMinus hh0 hk0 hk1 hb hφle hcover
    have hhi0 : 0 ≤ D.firstArc.hi - q.1 := hm2.1
    have hhi1 : D.firstArc.hi - q.1 ≤ Real.arcsin (q.2.1 / r) := hm2.2
    have hhilt : D.firstArc.hi - q.1 < Real.pi / 2 := lt_of_le_of_lt hhi1 harck
    refine ⟨q.1 + (n : ℝ) * (2 * Real.pi),
      figure5_left_gamma_direction q.1 n, ht, ?_, ?_⟩
    · -- upper endpoint: the analytic lift is `t - (hi - q.angle)`
      have hup : figure5UpperAnalyticAngle (q.1 + (n : ℝ) * (2 * Real.pi)) t A =
          t - (D.firstArc.hi - q.1) := by
        simp only [figure5UpperAnalyticAngle, hAhi]; ring
      rw [hup]
      exact figure5_easy_gapGeometry hr ht0 (by linarith)
    · -- lower endpoint: the analytic lift is `t + (lo - q.angle)`
      have hlow : figure5LowerAnalyticAngle (q.1 + (n : ℝ) * (2 * Real.pi)) t A =
          t + (D.firstArc.lo - q.1) := by
        simp only [figure5LowerAnalyticAngle, hAlo]; ring
      rw [hlow]
      by_cases hhalf : t + (D.firstArc.lo - q.1) ≤ t / 2
      · exact .nearHalf hr ht0 (by linarith [hhalf, ht0])
      rcases hdisj with hcircle | hbminus
      · -- selected mixed component: the centre sign is forced by selection
        have hc : 0 ≤ q.2.2 := by
          refine figure5_left_centre_nonneg (c := q.2.2) hh0 hk0 hk1 hφle hcover
            hcircle ?_
          intro lo hi hle hs
          have := hdom lo hi hle hs
          linarith
        have hhiEq : D.firstArc.hi - q.1 = Real.arcsin (q.2.1 / r) := by
          have hs := Real.arcsin_sin (x := D.firstArc.hi - q.1) (by linarith)
            (by linarith)
          rw [hcircle] at hs
          exact hs.symm
        have hloEq : Real.arctan (q.2.1 / (q.2.2 + 1 / 2)) = D.firstArc.lo - q.1 :=
          figure5_arctan_eq_of_base hb hlo0 hlolt hplus
        refine figure5_hard_mixed_gapGeometry (h := q.2.1) (base := q.2.2 + 1 / 2)
          (spanA := A.span) hr hδ0 hδr ht ht0.le hrpos hh0 hstrict (by linarith)
          ?_ ?_ ?_
        · rw [hspanA, hhiEq, hloEq]
        · rw [hspanA]; exact hSt
        · rw [hloEq]
      · -- base-base component: both endpoints are needle-end tangencies
        have hsinhi0 : 0 ≤ Real.sin (D.firstArc.hi - q.1) :=
          Real.sin_nonneg_of_nonneg_of_le_pi hhi0 (by linarith)
        have hcoshi : 0 < Real.cos (D.firstArc.hi - q.1) :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith, hhilt⟩
        have hsinhi : 0 < Real.sin (D.firstArc.hi - q.1) := by
          rcases hsinhi0.lt_or_eq with hlt | heq
          · exact hlt
          · exfalso; rw [← heq, mul_zero] at hbminus
            nlinarith [mul_pos hh0 hcoshi]
        have ha : 0 < q.2.2 - 1 / 2 := by
          by_contra hcon
          rw [not_lt] at hcon
          nlinarith [mul_pos hh0 hcoshi, mul_nonneg (neg_nonneg.2 hcon) hsinhi.le]
        have hloEq : Real.arctan (q.2.1 / (q.2.2 + 1 / 2)) = D.firstArc.lo - q.1 :=
          figure5_arctan_eq_of_base hb hlo0 hlolt hplus
        have hlosmall : D.firstArc.lo - q.1 < Real.arctan (2 * r) := by
          rw [← hloEq]
          refine Real.arctan_strictMono ?_
          have hquot : q.2.1 / (q.2.2 + 1 / 2) ≤ q.2.1 := by
            rw [div_le_iff₀ hb]
            nlinarith [mul_pos hh0 ha]
          linarith
        have hchord := hchordBase _ _ hsinlo hsinhi hplus (by linarith)
        have hplusPolar : figure5BasePlus q = scaleCoordinatePlane
            (q.2.1 / Real.sin (D.firstArc.lo - q.1))
            (unitDirection (q.1 + (D.firstArc.lo - q.1))) := by
          rw [figure5BasePlus, figure5_supportPoint_polar hsinlo hplus]
        have hnorm : q.2.1 ≤ strongR₁ * Real.sin (D.firstArc.lo - q.1) :=
          figure5_height_le_radius_mul_sin hR₁ hh0 hsinlo hplusPolar hsupport.plus_norm
        have hraw : Figure5BaseRayRawProvenance t (figure5LowerSupport A q) := by
          refine figure5_baseRay_provenance (θp := 0)
            (θm := (D.firstArc.hi - q.1) - (D.firstArc.lo - q.1))
            (φp := D.firstArc.lo - q.1) (φm := D.firstArc.hi - q.1) (-n)
            hh0 hsinlo hsinhi hplus
            (by simp only [figure5LowerSupport]; linarith) ?_ ?_ ⟨le_rfl, ht0.le⟩
            ⟨by linarith, hSt⟩
          · simp only [figure5LowerSupport, figure5LowerRotation, hAlo]
            push_cast; ring
          · simp only [figure5LowerSupport, figure5LowerRotation, hAlo]
            push_cast; ring
        exact figure5_hard_baseBase_gapGeometry (ψ₂ := D.firstArc.hi - q.1)
          hr ht0 htop hsint hh0 hhA hlo0 hφle (by linarith) hSt (by linarith)
          hchord hnorm hraw
  · -- the right strict presentation was selected
    obtain ⟨-, hcover, hdom⟩ := hright
    obtain ⟨hminus, hm2⟩ :=
      principalTraceRightPiece_hi_baseMinus hh0 hk0 hk1 hφle hcover
    have hhi0 : Real.pi - Real.arcsin (q.2.1 / r) ≤ D.firstArc.hi - q.1 := hm2.1
    have hhi1 : D.firstArc.hi - q.1 ≤ Real.pi := hm2.2
    have hcoshi : Real.cos (D.firstArc.hi - q.1) < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
    have hsinhi0 : 0 ≤ Real.sin (D.firstArc.hi - q.1) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) hhi1
    have hsinhi : 0 < Real.sin (D.firstArc.hi - q.1) := by
      rcases hsinhi0.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; rw [← heq, mul_zero] at hminus; nlinarith
    have ha : q.2.2 - 1 / 2 < 0 := by
      by_contra hcon
      rw [not_lt] at hcon
      nlinarith [mul_nonneg hcon hsinhi.le]
    obtain ⟨hdisj, hm1⟩ :=
      principalTraceRightPiece_lo_circleOrBasePlus hh0 hk0 hk1 ha hφle hcover
    have hlo0 : Real.pi - Real.arcsin (q.2.1 / r) ≤ D.firstArc.lo - q.1 := hm1.1
    have hlo1 : D.firstArc.lo - q.1 ≤ Real.pi := hm1.2
    have hsinlo0 : 0 ≤ Real.sin (D.firstArc.lo - q.1) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) hlo1
    refine ⟨q.1 + Real.pi + (n : ℝ) * (2 * Real.pi),
      figure5_right_gamma_direction q.1 n, ht, ?_, ?_⟩
    · -- upper endpoint: the analytic lift is `t + (π - (hi - q.angle))`
      have hup : figure5UpperAnalyticAngle
          (q.1 + Real.pi + (n : ℝ) * (2 * Real.pi)) t A =
          t + (Real.pi - (D.firstArc.hi - q.1)) := by
        simp only [figure5UpperAnalyticAngle, hAhi]; ring
      rw [hup]
      by_cases hhalf : t + (Real.pi - (D.firstArc.hi - q.1)) ≤ t / 2
      · exact .nearHalf hr ht0 (by linarith [hhalf, ht0])
      -- reflected quarter-chart angles
      have hψ₁0 : 0 ≤ Real.pi - (D.firstArc.hi - q.1) := by linarith
      have hψ₁le : Real.pi - (D.firstArc.hi - q.1) ≤ Real.arcsin (q.2.1 / r) := by
        linarith
      have hψ₁lt : Real.pi - (D.firstArc.hi - q.1) < Real.pi / 2 := by linarith
      have hcosψ₁ : 0 < Real.cos (Real.pi - (D.firstArc.hi - q.1)) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith, hψ₁lt⟩
      have hsinψ₁ : Real.sin (Real.pi - (D.firstArc.hi - q.1)) =
          Real.sin (D.firstArc.hi - q.1) := Real.sin_pi_sub _
      have hactψ₁ : q.2.1 * Real.cos (Real.pi - (D.firstArc.hi - q.1)) =
          (1 / 2 - q.2.2) * Real.sin (Real.pi - (D.firstArc.hi - q.1)) := by
        rw [Real.cos_pi_sub, hsinψ₁]; linarith
      rcases hdisj with hcircle | hbplus
      · -- selected mixed component on the right side
        have hc : q.2.2 ≤ 0 := by
          refine figure5_right_centre_nonpos (c := q.2.2) hh0 hk0 hk1 hφle hcover
            hcircle ?_
          intro lo hi hle hs
          have := hdom lo hi hle hs
          linarith
        have hloEq : Real.pi - (D.firstArc.lo - q.1) = Real.arcsin (q.2.1 / r) := by
          have hs := Real.arcsin_sin (x := Real.pi - (D.firstArc.lo - q.1))
            (by linarith) (by linarith)
          rw [Real.sin_pi_sub, hcircle] at hs
          exact hs.symm
        have hhiEq : Real.arctan (q.2.1 / (1 / 2 - q.2.2)) =
            Real.pi - (D.firstArc.hi - q.1) :=
          figure5_arctan_eq_of_base (by linarith) hψ₁0 hψ₁lt hactψ₁
        refine figure5_hard_mixed_gapGeometry (h := q.2.1) (base := 1 / 2 - q.2.2)
          (spanA := A.span) hr hδ0 hδr ht ht0.le hrpos hh0 hstrict (by linarith)
          ?_ ?_ ?_
        · rw [hspanA, hhiEq, ← hloEq]; ring
        · rw [hspanA]; exact hSt
        · rw [hhiEq]
      · -- base-base component on the right side
        have hcoslo : Real.cos (D.firstArc.lo - q.1) < 0 :=
          Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
        have hsinlo : 0 < Real.sin (D.firstArc.lo - q.1) := by
          rcases hsinlo0.lt_or_eq with hlt | heq
          · exact hlt
          · exfalso; rw [← heq, mul_zero] at hbplus; nlinarith
        have hbneg : q.2.2 + 1 / 2 < 0 := by
          by_contra hcon
          rw [not_lt] at hcon
          nlinarith [mul_nonneg hcon hsinlo.le]
        have hψ₂0 : 0 ≤ Real.pi - (D.firstArc.lo - q.1) := by linarith
        have hψ₂lt : Real.pi - (D.firstArc.lo - q.1) < Real.pi / 2 := by linarith
        have hcosψ₂ : 0 < Real.cos (Real.pi - (D.firstArc.lo - q.1)) :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith, hψ₂lt⟩
        have hsinψ₂ : Real.sin (Real.pi - (D.firstArc.lo - q.1)) =
            Real.sin (D.firstArc.lo - q.1) := Real.sin_pi_sub _
        have hactψ₂ : q.2.1 * Real.cos (Real.pi - (D.firstArc.lo - q.1)) =
            (-q.2.2 - 1 / 2) * Real.sin (Real.pi - (D.firstArc.lo - q.1)) := by
          rw [Real.cos_pi_sub, hsinψ₂]; linarith
        have hhiEq : Real.arctan (q.2.1 / (1 / 2 - q.2.2)) =
            Real.pi - (D.firstArc.hi - q.1) :=
          figure5_arctan_eq_of_base (by linarith) hψ₁0 hψ₁lt hactψ₁
        have hψ₁small : Real.pi - (D.firstArc.hi - q.1) < Real.arctan (2 * r) := by
          rw [← hhiEq]
          refine Real.arctan_strictMono ?_
          have hquot : q.2.1 / (1 / 2 - q.2.2) ≤ q.2.1 := by
            rw [div_le_iff₀ (by linarith)]
            nlinarith [mul_pos hh0 (show (0:ℝ) < -q.2.2 - 1 / 2 by linarith)]
          linarith
        have hchord0 := hchordBase _ _ hsinlo hsinhi hbplus (by linarith)
        have hchord : Real.sin (Real.pi - (D.firstArc.hi - q.1)) *
            Real.sin (Real.pi - (D.firstArc.lo - q.1)) =
            q.2.1 * Real.sin ((Real.pi - (D.firstArc.lo - q.1)) -
              (Real.pi - (D.firstArc.hi - q.1))) := by
          rw [hsinψ₁, hsinψ₂,
            show (Real.pi - (D.firstArc.lo - q.1)) -
              (Real.pi - (D.firstArc.hi - q.1)) =
              (D.firstArc.hi - q.1) - (D.firstArc.lo - q.1) by ring]
          linarith
        have hminusPolar : figure5BaseMinus q = scaleCoordinatePlane
            (q.2.1 / Real.sin (D.firstArc.hi - q.1))
            (unitDirection (q.1 + (D.firstArc.hi - q.1))) := by
          rw [figure5BaseMinus, figure5_supportPoint_polar hsinhi
            (by linarith : q.2.1 * Real.cos (D.firstArc.hi - q.1) =
              (q.2.2 - 1 / 2) * Real.sin (D.firstArc.hi - q.1))]
        have hnorm : q.2.1 ≤ strongR₁ *
            Real.sin (Real.pi - (D.firstArc.hi - q.1)) := by
          rw [hsinψ₁]
          exact figure5_height_le_radius_mul_sin hR₁ hh0 hsinhi hminusPolar
            hsupport.minus_norm
        have hraw : Figure5BaseRayRawProvenance t (figure5UpperSupport t A q) := by
          refine figure5_baseRay_provenance
            (θp := t - ((D.firstArc.hi - q.1) - (D.firstArc.lo - q.1)))
            (θm := t)
            (φp := D.firstArc.lo - q.1) (φm := D.firstArc.hi - q.1) (-n)
            hh0 hsinlo hsinhi hbplus
            (by simp only [figure5UpperSupport]; linarith) ?_ ?_
            ⟨by linarith, by linarith⟩ ⟨ht0.le, le_rfl⟩
          · simp only [figure5UpperSupport, figure5UpperRotation, hAhi]
            push_cast; ring
          · simp only [figure5UpperSupport, figure5UpperRotation, hAhi]
            push_cast; ring
        exact figure5_hard_baseBase_gapGeometry
          (ψ₂ := Real.pi - (D.firstArc.lo - q.1))
          hr ht0 htop hsint hh0 hhA hψ₁0 (by linarith) (by linarith)
          (by linarith) (by linarith) hchord hnorm hraw
    · -- lower endpoint: the analytic lift is `t - (π - (lo - q.angle))`
      have hlow : figure5LowerAnalyticAngle
          (q.1 + Real.pi + (n : ℝ) * (2 * Real.pi)) t A =
          t - (Real.pi - (D.firstArc.lo - q.1)) := by
        simp only [figure5LowerAnalyticAngle, hAlo]; ring
      rw [hlow]
      refine figure5_easy_gapGeometry hr ht0 ?_
      have : 0 ≤ Real.pi - (D.firstArc.lo - q.1) := by linarith
      linarith

noncomputable def figure5LocalContactCertificate_of_actualSelected
    {r t δ₀ : ℝ} {q : DirectedSupportParameter}
    {D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r}
    {A : NormalizedPolarArc}
    (hsupport : Figure5PositiveNormalizedSupport r strongA strongR₁ q)
    (hselected : Figure5SelectedChangedLift r t q D A)
    (hstrict : q.2.1 < r)
    (hr : r ∈ Icc strongA strongR₀)
    (hδ0 : 0 < δ₀) (hδr : δ₀ < r)
    (ht : t = strongEndpointPhi r δ₀)
    (ht0 : 0 < t) (htop : t < Real.pi / 2 - Real.arctan (2 * r))
    (hsint : 0 ≤ Real.sin t) :
    Figure5LocalContactCertificate r t (q.1 : ProjectiveDirection) := by
  let hex := figure5ActualSelectedTargetRelation_of_principal hsupport hstrict
    hselected hr hδ0 hδr ht ht0 htop hsint
  let gamma : ℝ := Classical.choose hex
  have hs := Classical.choose_spec hex
  have huLift := hselected.upper_rotated_lift.2.1
  have hlLift := hselected.reflected_lower_lift
  have hu := hs.2.upper.toGapSource
    (by simpa [figure5UpperSupport] using hsupport.height_pos)
    (by simpa [figure5UpperSupport] using hsupport.height_le_a) huLift
  have hl := hs.2.lower.toGapSource
    (by simpa [figure5LowerSupport] using hsupport.height_pos)
    (by simpa [figure5LowerSupport] using hsupport.height_le_a) hlLift
  exact
    { q := q
      D := D
      A := A
      gamma := gamma
      support := hsupport
      selectedLift := hselected
      gamma_direction := hs.1
      upper_gap := hu.gap_lt
      lower_gap := hl.gap_lt }

end

end StarKakeyaLower
