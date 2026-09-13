import StarKakeyaLower.UniversalFirstArc

/-!
# The universal Case-I endpoint closure

This file proves the pointwise first-arc endpoint containment for the raw
support family attached to an arbitrary `StarShapedKakeya` set, on the paper's
inner-radius direction class `B = A_in_radius R₁`.

Nothing here is an assumption about the set: the support family, its
orientation normalization, its first-arc trace data, the target normalization
and the comparison height `δ₀` are all constructed.
-/

open Set MeasureTheory Real

namespace StarKakeyaLower

noncomputable section

/-! ## Quotient-interval helpers -/

/-- Translation covariance of the saturated open centred dilation. -/
theorem mem_quotientCenteredDilate_add {p : ℝ} [Fact (0 < p)]
    {g x rad β γ : ℝ}
    (h : ((γ : ℝ) : AddCircle p) ∈ quotientCenteredDilate g p x rad) :
    ((β + γ : ℝ) : AddCircle p) ∈
      quotientCenteredDilate g p (β + x) rad := by
  by_cases hsat : p ≤ (x + g * rad) - (x - g * rad)
  · rw [quotientCenteredDilate, quotientInterval_eq_univ_of_le (by linarith)]
    exact mem_univ _
  · rw [quotientCenteredDilate, quotientInterval_of_lt (by linarith)] at h
    obtain ⟨u, hu, hueq⟩ := h
    rw [quotientCenteredDilate, quotientInterval_of_lt (by linarith)]
    have hu' : ((u : ℝ) : AddCircle p) = ((γ : ℝ) : AddCircle p) := hueq
    refine ⟨β + u, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
    show ((β + u : ℝ) : AddCircle p) = ((β + γ : ℝ) : AddCircle p)
    rw [AddCircle.coe_add, AddCircle.coe_add, hu']

/-- A closed lifted direction interval sits strictly inside its own centred
dilation whenever the dilation factor exceeds one. -/
theorem directionInterval_subset_centeredDilate {g lo hi : ℝ}
    (hlt : lo < hi) (hg : 1 < g) :
    directionInterval lo hi ⊆
      quotientCenteredDilate g Real.pi ((lo + hi) / 2) ((hi - lo) / 2) := by
  have hrad : 0 < (hi - lo) / 2 := by linarith
  by_cases hsat : Real.pi ≤
      ((lo + hi) / 2 + g * ((hi - lo) / 2)) - ((lo + hi) / 2 - g * ((hi - lo) / 2))
  · rw [quotientCenteredDilate, quotientInterval_eq_univ_of_le hsat]
    exact subset_univ _
  · have htarget := lt_of_not_ge hsat
    have hsource : hi - lo < Real.pi := by nlinarith
    rw [directionInterval, quotientClosedInterval, if_neg (not_le.mpr hsource),
      quotientCenteredDilate, quotientInterval_of_lt htarget]
    apply image_mono
    intro y hy
    constructor <;> nlinarith [hy.1, hy.2]

/-! ## The positively oriented universal support family -/

variable {E : Set Plane}

/-- The universal raw support needle, normalized to nonnegative height. -/
def universalPositiveNeedle (K : StarShapedKakeya E) (d : ProjectiveDirection) :
    DirectionNeedle d := (universalDirectionNeedle K d).orientPositive

@[simp] theorem universalPositiveNeedle_triangle (K : StarShapedKakeya E)
    (d : ProjectiveDirection) :
    (universalPositiveNeedle K d).triangle =
      (universalDirectionNeedle K d).triangle :=
  DirectionNeedle.orientPositive_triangle _

@[simp] theorem universalPositiveNeedle_height_nonneg (K : StarShapedKakeya E)
    (d : ProjectiveDirection) : 0 ≤ (universalPositiveNeedle K d).height :=
  DirectionNeedle.orientPositive_height_nonneg _

theorem universalPositiveNeedle_abs_height (K : StarShapedKakeya E)
    (d : ProjectiveDirection) :
    |(universalPositiveNeedle K d).height| =
      (K.needleFamily d).height K.center := by
  rw [universalPositiveNeedle, DirectionNeedle.orientPositive_abs_height]
  exact universalDirectionNeedle_abs_height K d

theorem universalPositiveNeedle_height_lt_of_no_high {K : StarShapedKakeya E}
    {a : ℝ}
    (hhigh : ¬ ∃ theta : Direction,
      a ≤ (K.needleFamily theta).height K.center) (d : ProjectiveDirection) :
    (universalPositiveNeedle K d).height < a := by
  have h : |(universalPositiveNeedle K d).height| < a := by
    rw [universalPositiveNeedle_abs_height]
    exact lt_of_not_ge (fun hd => hhigh ⟨d, hd⟩)
  exact (le_abs_self _).trans_lt h

theorem universalPositiveNeedle_height_le_of_no_high {K : StarShapedKakeya E}
    {a : ℝ}
    (hhigh : ¬ ∃ theta : Direction,
      a ≤ (K.needleFamily theta).height K.center) :
    ∀ d, |(universalPositiveNeedle K d).height| ≤ a := by
  intro d
  rw [universalPositiveNeedle_abs_height]
  exact (lt_of_not_ge (fun hd => hhigh ⟨d, hd⟩)).le

theorem universalPositiveTriangleUnion_subset (K : StarShapedKakeya E) :
    directionTriangleUnion (universalPositiveNeedle K) Set.univ ⊆
      centeredCoordinate K '' E := by
  intro z hz
  simp only [directionTriangleUnion, mem_iUnion] at hz
  obtain ⟨⟨d, _hd⟩, hz⟩ := hz
  rw [universalPositiveNeedle_triangle] at hz
  exact universalDirectionTriangleUnion_subset K
    (triangle_subset_directionTriangleUnion_univ (universalDirectionNeedle K) d hz)

/-! ## Radius containment of the inner class -/

theorem planeNormSq_planeCoordinateEquiv (y : Plane) :
    planeNormSq (planeCoordinateEquiv y) = ‖y‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [planeNormSq, Fin.sum_univ_two]

/-- The inner-radius class controls the raw coordinate triangle. -/
theorem universalPositiveNeedle_triangle_subset_disk (K : StarShapedKakeya E)
    {d : ProjectiveDirection} (hd : d ∈ K.A_in_radius strongR₁) :
    (universalPositiveNeedle K d).triangle ⊆ originClosedDisk strongR₁ := by
  rw [universalPositiveNeedle_triangle,
    universalDirectionNeedle_triangle_eq_centeredCoordinate_image]
  rintro _ ⟨x, hx, rfl⟩
  have hball : x ∈ Metric.closedBall K.center strongR₁ := hd hx
  have hnorm : ‖x - K.center‖ ≤ strongR₁ := by
    rw [← dist_eq_norm]; exact hball
  have hR : 0 ≤ strongR₁ := (norm_nonneg _).trans hnorm
  change planeNormSq (planeCoordinateEquiv (x - K.center)) ≤ strongR₁ ^ 2
  rw [planeNormSq_planeCoordinateEquiv]
  nlinarith [norm_nonneg (x - K.center)]


/-! ## Canonical first-arc data for the universal family -/

theorem strongRadius_pos {r : ℝ} (hr : r ∈ Icc strongA strongR₀) : 0 < r :=
  strongParameterDomain.a_pos.trans_le hr.1

theorem strongRadius_lt_half {r : ℝ} (hr : r ∈ Icc strongA strongR₀) : r < 1 / 2 :=
  hr.2.trans_lt strongParameterDomain.r₀_lt_half

/-- The canonical trace decomposition attached to every direction at every
radius of the Case-I range.  Totality is the theorem
`supportTraceFirstArcData`, not an assumption. -/
def universalArcData (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) (d : ProjectiveDirection) :
    FirstArcData (universalPositiveNeedle K d).triangle r :=
  supportTraceFirstArcData (α := (universalPositiveNeedle K d).angle)
    (c := (universalPositiveNeedle K d).centre)
    (strongRadius_pos hr) (strongRadius_lt_half hr)
    (universalPositiveNeedle_height_nonneg K d)
    ((universalPositiveNeedle_height_lt_of_no_high hhigh d).le.trans hr.1)

/-- The universal first-arc family at one radius. -/
def universalFamily (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) : DirectionNeedleFamily r :=
  directionNeedleFamilyOfRaw (universalPositiveNeedle K) (universalArcData K hhigh hr)

theorem universalFamily_needle (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) (d : ProjectiveDirection) :
    (universalFamily K hhigh hr).needle d = universalPositiveNeedle K d := rfl

/-- The selected first arc of the universal family is literally the output of
the deterministic support-trace selector. -/
theorem universalFamily_selected (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) (d : ProjectiveDirection) :
    selectedSupportFirstArc? r (universalPositiveNeedle K d).angle
        ((universalPositiveNeedle K d).height, (universalPositiveNeedle K d).centre) =
      some ((universalFamily K hhigh hr).firstArc d) := by
  have harc : (universalFamily K hhigh hr).firstArc d =
      (supportTraceFirstArcData (α := (universalPositiveNeedle K d).angle)
        (c := (universalPositiveNeedle K d).centre)
        (strongRadius_pos hr) (strongRadius_lt_half hr)
        (universalPositiveNeedle_height_nonneg K d)
        ((universalPositiveNeedle_height_lt_of_no_high hhigh d).le.trans hr.1)).firstArc :=
    rfl
  rw [harc]
  exact selectedSupportFirstArc?_eq_some _ _ _ _

/-- Zero support height forces the degenerate selected arc, whose projective
centre is the needle direction itself. -/
theorem universalFamily_zeroHeight (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) {d : ProjectiveDirection}
    (hδ : (universalPositiveNeedle K d).height = 0) :
    (((universalFamily K hhigh hr).firstCenter d : ℝ) : ProjectiveDirection) = d ∧
      (universalFamily K hhigh hr).firstRadius d = 0 := by
  obtain ⟨hcentre, hradius⟩ := supportTraceFirstArcData_zeroHeight
    (α := (universalPositiveNeedle K d).angle)
    (c := (universalPositiveNeedle K d).centre)
    (strongRadius_pos hr) (strongRadius_lt_half hr)
    (universalPositiveNeedle_height_nonneg K d)
    ((universalPositiveNeedle_height_lt_of_no_high hhigh d).le.trans hr.1) hδ
  have hc : ((((universalFamily K hhigh hr).firstArc d).lo +
      ((universalFamily K hhigh hr).firstArc d).hi) / 2 : ℝ) =
      ((universalFamily K hhigh hr).firstCenter d : ℝ) := rfl
  have hcentre' :
      (((universalFamily K hhigh hr).firstCenter d : ℝ) : ProjectiveDirection) =
        ((universalPositiveNeedle K d).angle : ProjectiveDirection) := by
    rw [← hc]; exact hcentre
  have hradius' : (universalFamily K hhigh hr).firstRadius d = 0 := hradius
  exact ⟨hcentre'.trans (universalPositiveNeedle K d).direction_eq, hradius'⟩

/-- Positive support height forces a nondegenerate selected arc. -/
theorem universalFamily_firstRadius_pos (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) {d : ProjectiveDirection}
    (hδ : 0 < (universalPositiveNeedle K d).height) :
    0 < (universalFamily K hhigh hr).firstRadius d := by
  have h := supportTraceFirstArcData_span_pos
    (α := (universalPositiveNeedle K d).angle)
    (c := (universalPositiveNeedle K d).centre)
    (strongRadius_pos hr) (strongRadius_lt_half hr)
    (universalPositiveNeedle_height_nonneg K d)
    ((universalPositiveNeedle_height_lt_of_no_high hhigh d).le.trans hr.1)
    hδ ((universalPositiveNeedle_height_lt_of_no_high hhigh d).trans_le hr.1)
  have h' : ((universalFamily K hhigh hr).firstArc d).lo <
      ((universalFamily K hhigh hr).firstArc d).hi := h
  have hrad : (universalFamily K hhigh hr).firstRadius d =
      (((universalFamily K hhigh hr).firstArc d).hi -
        ((universalFamily K hhigh hr).firstArc d).lo) / 2 := rfl
  rw [hrad]
  linarith

/-- Contrapositive dichotomy: the selected span vanishes exactly at zero
height. -/
theorem universalFamily_height_eq_zero_of_firstRadius_eq_zero
    (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) {d : ProjectiveDirection}
    (h : (universalFamily K hhigh hr).firstRadius d = 0) :
    (universalPositiveNeedle K d).height = 0 := by
  rcases (universalPositiveNeedle_height_nonneg K d).eq_or_lt with hz | hpos
  · exact hz.symm
  · exact absurd h (universalFamily_firstRadius_pos K hhigh hr hpos).ne'


/-! ## Degenerate selected arcs -/

theorem NormalizedPolarArc.hi_eq_lo_of_carrier_subset_singleton
    {A : NormalizedPolarArc} {q : PolarAngle} (h : A.carrier ⊆ {q}) :
    A.hi = A.lo := by
  have hpi := Real.pi_pos
  have hlo := h A.endpoints_mem_carrier.1
  have hhi := h A.endpoints_mem_carrier.2
  rw [Set.mem_singleton_iff] at hlo hhi
  have hcoe : ((A.hi : ℝ) : PolarAngle) = ((A.lo : ℝ) : PolarAngle) :=
    hhi.trans hlo.symm
  exact NormalizedPolarArc.polar_coe_injective_on_fullChart (a := A.lo)
    ⟨A.le_endpoints, by linarith [A.short]⟩ ⟨le_rfl, by linarith⟩ hcoe

/-! ## The positive-height Figure 5 member -/

set_option maxHeartbeats 1600000 in
/-- A positive-height member of the inner class whose selected arc lies in the
target of `d₀` is trapped in the open centred dilation of that target.  The
target is normalized to `[0,t]` by an explicit *rotation of the support angle*;
the comparison height `δ₀` is produced from `t` by the range theorem for
`strongEndpointPhi`. -/
theorem universalFamily_positiveMember_mem_dilate
    (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) {d₀ d : ProjectiveDirection}
    (hdB : d ∈ K.A_in_radius strongR₁)
    (hdJ : d ∈ (universalFamily K hhigh hr).JGamma
      ((universalFamily K hhigh hr).firstArcTarget d₀))
    (hd₀pos : ((universalFamily K hhigh hr).firstArc d₀).lo <
      ((universalFamily K hhigh hr).firstArc d₀).hi)
    (hδd : 0 < (universalPositiveNeedle K d).height)
    (hsat : ¬ Real.pi ≤ strongPaperG r *
      (((universalFamily K hhigh hr).firstArc d₀).hi -
        ((universalFamily K hhigh hr).firstArc d₀).lo)) :
    d ∈ quotientCenteredDilate (strongPaperG r) Real.pi
      ((universalFamily K hhigh hr).firstCenter d₀)
      ((universalFamily K hhigh hr).firstRadius d₀) := by
  classical
  have hpi := Real.pi_pos
  have hr0 : 0 < r := strongRadius_pos hr
  have hrhalf : r < 1 / 2 := strongRadius_lt_half hr
  set F := universalFamily K hhigh hr with hF
  set lo₀ : ℝ := (F.firstArc d₀).lo with hlo₀
  set hi₀ : ℝ := (F.firstArc d₀).hi with hhi₀
  set t : ℝ := hi₀ - lo₀ with hts
  have ht0 : 0 < t := by simp only [hts]; linarith
  have htπ : t < Real.pi := by simp only [hts]; exact (F.firstArc d₀).short
  have htop : t < Real.pi / 2 - Real.arctan (2 * r) :=
    strongEndpointTarget_lt_top_of_not_saturated hr0 hsat
  have hsint : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0.le htπ.le
  obtain ⟨δ₀, hδ₀0, hδ₀r, hδ₀eq⟩ := exists_strongEndpointPhi_eq hr0 ht0 htop
  -- the rotated support of `d`
  set N := universalPositiveNeedle K d with hN
  set α : ℝ := N.angle with hα
  set δ : ℝ := N.height with hδ
  set c : ℝ := N.centre with hc
  have hδA : δ ≤ strongA := (universalPositiveNeedle_height_lt_of_no_high hhigh d).le
  have hδr : δ < r := (universalPositiveNeedle_height_lt_of_no_high hhigh d).trans_le hr.1
  set β : ℝ := -lo₀ with hβ
  set q : DirectedSupportParameter := (α + β, (δ, c)) with hq
  set D' := supportTraceFirstArcData (α := α + β) (c := c) hr0 hrhalf hδd.le hδr.le
    with hD'
  have hselD' : selectedSupportFirstArc? r q.1 q.2 = some D'.firstArc :=
    selectedSupportFirstArc?_eq_some _ _ _ _
  -- covariance of the selector identifies the rotated arc
  have hrot : D'.firstArc = (F.firstArc d).rotate β := by
    have h1 : selectedSupportFirstArc? r (α + β) (δ, c) =
        (selectedSupportFirstArc? r α (δ, c)).map (NormalizedPolarArc.rotate β) :=
      selectedSupportFirstArc?_add_of_pos hr0 hδd hδr.le
    rw [universalFamily_selected K hhigh hr d] at h1
    have h2 : selectedSupportFirstArc? r (α + β) (δ, c) = some D'.firstArc := hselD'
    rw [h2] at h1
    exact Option.some.inj h1
  -- the rotated arc lands in the normalized target
  have htargetEq : ((F.firstArc d₀).rotate β).carrier = polarArc 0 t := by
    have : ((F.firstArc d₀).rotate β).carrier = polarArc (lo₀ + β) (hi₀ + β) := rfl
    rw [this]
    congr 1 <;> simp only [hβ, hts] <;> ring
  have hcarrier : D'.firstArc.carrier ⊆ polarArc 0 t := by
    rw [hrot, NormalizedPolarArc.rotate_carrier, ← htargetEq,
      NormalizedPolarArc.rotate_carrier]
    exact Set.image_mono hdJ
  obtain ⟨n, hcarrn, hsubn, -, -⟩ :=
    D'.firstArc.exists_changeLift_subset_targetChart ht0.le htπ hcarrier
  set A : NormalizedPolarArc := D'.firstArc.changeLift n with hA
  -- the physical support data
  have hnorms := supportNeedle_baseEndpoints_mem_triangle α δ c
  have htri : N.triangle ⊆ originClosedDisk strongR₁ :=
    universalPositiveNeedle_triangle_subset_disk K hdB
  have hminus : planeNormSq (figure5BaseMinus q) ≤ strongR₁ ^ 2 := by
    have hmem : supportPoint α δ (c - 1 / 2) ∈ N.triangle := hnorms.1
    have := htri hmem
    change planeNormSq (supportPoint α δ (c - 1 / 2)) ≤ strongR₁ ^ 2 at this
    rw [figure5BaseMinus, planeNormSq_supportPoint]
    rw [planeNormSq_supportPoint] at this
    exact this
  have hplus : planeNormSq (figure5BasePlus q) ≤ strongR₁ ^ 2 := by
    have hmem : supportPoint α δ (c + 1 / 2) ∈ N.triangle := hnorms.2
    have := htri hmem
    change planeNormSq (supportPoint α δ (c + 1 / 2)) ≤ strongR₁ ^ 2 at this
    rw [figure5BasePlus, planeNormSq_supportPoint]
    rw [planeNormSq_supportPoint] at this
    exact this
  have hsupport : Figure5PositiveNormalizedSupport r strongA strongR₁ q :=
    { radius_pos := hr0
      height_pos := hδd
      height_le_a := hδA
      height_le_radius := hδr.le
      minus_norm := hminus
      plus_norm := hplus }
  have hselected : Figure5SelectedChangedLift r t q D' A :=
    { target_nonneg := ht0.le
      target_lt_pi := htπ
      selected := hselD'
      changed := ⟨n, rfl⟩
      in_target := hsubn }
  have hcert := figure5LocalContactCertificate_of_actualSelected hsupport hselected
    hδr hr hδ₀0 hδ₀r hδ₀eq.symm ht0 htop hsint
  have hmem := figure5_local_contact_pointwise ht0.le
    hcert.selectedLift.in_target hcert.upper_gap hcert.lower_gap
  have hshift := mem_quotientCenteredDilate_add (β := lo₀) hmem
  have hd : ((lo₀ + hcert.gamma : ℝ) : ProjectiveDirection) = d := by
    have hg := hcert.gamma_direction
    rw [AddCircle.coe_add, hg, ← AddCircle.coe_add]
    have : lo₀ + q.1 = α := by simp only [hq, hβ]; ring
    rw [this]
    exact N.direction_eq
  rw [hd] at hshift
  have hcentre : lo₀ + t / 2 = F.firstCenter d₀ := by
    simp only [DirectionNeedleFamily.firstCenter, hts, ← hlo₀, ← hhi₀]
    ring
  have hradius : t / 2 = F.firstRadius d₀ := by
    simp only [DirectionNeedleFamily.firstRadius, hts, ← hlo₀, ← hhi₀]
  rw [hcentre, hradius] at hshift
  exact hshift


/-! ## The zero-height member -/

/-- A zero-height member of `JΓ` is the projective class of an actual point of
the target lift. -/
theorem universalFamily_zeroMember_mem_directionInterval
    (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) {d₀ d : ProjectiveDirection}
    (hdJ : d ∈ (universalFamily K hhigh hr).JGamma
      ((universalFamily K hhigh hr).firstArcTarget d₀))
    (hδd : (universalPositiveNeedle K d).height = 0) :
    d ∈ directionInterval ((universalFamily K hhigh hr).firstArc d₀).lo
      ((universalFamily K hhigh hr).firstArc d₀).hi := by
  have hpi := Real.pi_pos
  set F := universalFamily K hhigh hr with hF
  obtain ⟨hcentre, hradius⟩ := universalFamily_zeroHeight K hhigh hr hδd
  have hdeg : (F.firstArc d).hi = (F.firstArc d).lo := by
    have : ((F.firstArc d).hi - (F.firstArc d).lo) / 2 = 0 := hradius
    linarith
  have hcen : (F.firstCenter d : ℝ) = (F.firstArc d).lo := by
    have : (F.firstCenter d : ℝ) =
        ((F.firstArc d).lo + (F.firstArc d).hi) / 2 := rfl
    rw [this, hdeg]; ring
  have hdlo : (((F.firstArc d).lo : ℝ) : ProjectiveDirection) = d := by
    rw [← hcen]; exact hcentre
  -- the lifted endpoint of `d` lies in the target chart
  have hshort₀ : (F.firstArc d₀).hi - (F.firstArc d₀).lo < Real.pi :=
    (F.firstArc d₀).short
  have hmem : (((F.firstArc d).lo : ℝ) : PolarAngle) ∈
      polarArc (F.firstArc d₀).lo (F.firstArc d₀).hi :=
    hdJ (F.firstArc d).endpoints_mem_carrier.1
  rw [polarArc, quotientClosedInterval,
    if_neg (not_le.mpr (by linarith : (F.firstArc d₀).hi - (F.firstArc d₀).lo <
      2 * Real.pi))] at hmem
  obtain ⟨x, hx, hxeq⟩ := hmem
  have hxproj : ((x : ℝ) : ProjectiveDirection) = d := by
    have := congrArg polarToProjective hxeq
    rw [polarToProjective_coe, polarToProjective_coe] at this
    exact this.trans hdlo
  rw [directionInterval, quotientClosedInterval, if_neg (not_le.mpr hshort₀)]
  exact ⟨x, hx, hxproj⟩

/-! ## The pointwise hybrid containment on the inner-radius class -/

theorem universal_hybrid_containment (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) :
    FirstArcPointwiseHybridCriticalContainment (universalFamily K hhigh hr)
      (K.A_in_radius strongR₁) (strongPaperG r) := by
  have hpi := Real.pi_pos
  have hr0 : 0 < r := strongRadius_pos hr
  have hrhalf : r < 1 / 2 := strongRadius_lt_half hr
  have hg1 : 1 < strongPaperG r := one_lt_strongPaperG hr0 hrhalf
  set F := universalFamily K hhigh hr with hF
  apply firstArcPointwiseHybridCriticalContainment_of_branches
  · -- zero span at `d₀`
    intro d₀ hd₀ hrad0 d hd
    have hdeg : (F.firstArc d₀).hi = (F.firstArc d₀).lo := by
      have : ((F.firstArc d₀).hi - (F.firstArc d₀).lo) / 2 = 0 := hrad0
      linarith
    have hcen : (F.firstCenter d₀ : ℝ) = (F.firstArc d₀).lo := by
      have : (F.firstCenter d₀ : ℝ) =
          ((F.firstArc d₀).lo + (F.firstArc d₀).hi) / 2 := rfl
      rw [this, hdeg]; ring
    have hδd : (universalPositiveNeedle K d).height = 0 := by
      by_contra hne
      have hpos : 0 < (universalPositiveNeedle K d).height :=
        lt_of_le_of_ne (universalPositiveNeedle_height_nonneg K d) (Ne.symm hne)
      have hradpos := universalFamily_firstRadius_pos K hhigh hr hpos
      -- the selected arc of `d` is inside the degenerate target
      have hsub : (F.firstArc d).carrier ⊆
          {(((F.firstArc d₀).lo : ℝ) : PolarAngle)} := by
        have htgt : F.firstArcTarget d₀ =
            {(((F.firstArc d₀).lo : ℝ) : PolarAngle)} := by
          have := NormalizedPolarArc.carrier_eq_singleton_of_span_nonpos
            (A := F.firstArc d₀) (by
              dsimp [NormalizedPolarArc.span]; linarith)
          exact this
        rw [← htgt]; exact hd.2
      have := NormalizedPolarArc.hi_eq_lo_of_carrier_subset_singleton hsub
      have hz : F.firstRadius d = 0 := by
        have : F.firstRadius d = ((F.firstArc d).hi - (F.firstArc d).lo) / 2 := rfl
        rw [this, ‹(F.firstArc d).hi = (F.firstArc d).lo›]; ring
      exact absurd hz hradpos.ne'
    have hint := universalFamily_zeroMember_mem_directionInterval K hhigh hr hd.2 hδd
    rw [directionInterval, quotientClosedInterval, hdeg,
      if_neg (not_le.mpr (by linarith : (F.firstArc d₀).lo - (F.firstArc d₀).lo <
        Real.pi))] at hint
    obtain ⟨y, hy, hyeq⟩ := hint
    rw [Set.Icc_self, Set.mem_singleton_iff] at hy
    subst hy
    rw [Set.mem_singleton_iff, ← hyeq, hcen]
  · -- positive span at `d₀`
    intro d₀ hd₀ hradpos d hd
    have hlt : (F.firstArc d₀).lo < (F.firstArc d₀).hi := by
      have : F.firstRadius d₀ =
        ((F.firstArc d₀).hi - (F.firstArc d₀).lo) / 2 := rfl
      rw [this] at hradpos; linarith
    have hcentre : ((F.firstArc d₀).lo + (F.firstArc d₀).hi) / 2 =
        F.firstCenter d₀ := rfl
    have hradius : ((F.firstArc d₀).hi - (F.firstArc d₀).lo) / 2 =
        F.firstRadius d₀ := rfl
    by_cases hsat : Real.pi ≤ strongPaperG r *
        ((F.firstArc d₀).hi - (F.firstArc d₀).lo)
    · rw [quotientCenteredDilate, quotientInterval_eq_univ_of_le (by
        rw [← hradius]; nlinarith)]
      exact mem_univ _
    · by_cases hδd : (universalPositiveNeedle K d).height = 0
      · have hint := universalFamily_zeroMember_mem_directionInterval K hhigh hr
          hd.2 hδd
        have := directionInterval_subset_centeredDilate hlt hg1 hint
        rwa [hcentre, hradius] at this
      · have hpos : 0 < (universalPositiveNeedle K d).height :=
          lt_of_le_of_ne (universalPositiveNeedle_height_nonneg K d) (Ne.symm hδd)
        exact universalFamily_positiveMember_mem_dilate K hhigh hr hd.1 hd.2 hlt
          hpos hsat

end

end StarKakeyaLower
