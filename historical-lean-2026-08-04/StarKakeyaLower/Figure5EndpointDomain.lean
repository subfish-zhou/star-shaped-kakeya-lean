import Mathlib

/-!
# The parameter-neutral endpoint domain and its analytic package

This module is CLEAN: its import closure is `Mathlib` only, so nothing here can
depend on a frozen witness tuple.  It carries two kinds of material.

* The **parameter-free scalar layer** of the Figure-5 endpoint argument: the
  first-contact angle `strongEndpointPhi`, the interior and large-angle endpoint
  ratios, and the elementary estimates they satisfy.  Despite their historical
  `strong` prefixes these declarations never mention a parameter tuple — they
  were moved here verbatim from `CaseIEndpointAnalytic`,
  `CaseIEndpointR1Analytic` and `Figure5EndpointEnvelope` so that the generic
  endpoint geometry does not have to import a frozen kernel.  The old modules
  import this one, so every previously available name still resolves.

* The **parameter interface** of milestone M6.  `Figure5EndpointDomain` is the
  clean tuple `(a, r₀, R₁, g)` the endpoint geometry actually consumes, and
  `Figure5EndpointAnalyticPackage` is the exact list of analytic gates that the
  geometry cannot prove for itself.  Deliberately absent from both: any `rλ`,
  any mass split, any integral and any numeral.  A new parameter tuple enters
  the endpoint machinery only through these two structures.
-/

open Set Real

namespace StarKakeyaLower

noncomputable section

/-! ## Parameter-free endpoint ratios -/

/-- Interior endpoint ratio in Li's Case I. -/
def strongInteriorRatio (r : ℝ) : ℝ := (1 + 2 * r) / (1 - 2 * r)

/-- Large-angle endpoint ratio. -/
def strongLargeAngleRatio (r : ℝ) : ℝ :=
  Real.pi / (Real.pi / 2 - Real.arctan (2 * r))

theorem strongInteriorRatio_pos {r : ℝ} (hr0 : 0 ≤ r) (hrhalf : r < 1 / 2) :
    0 < strongInteriorRatio r := by
  rw [strongInteriorRatio]
  apply div_pos <;> linarith

theorem one_lt_strongInteriorRatio {r : ℝ} (hr0 : 0 < r) (hrhalf : r < 1 / 2) :
    1 < strongInteriorRatio r := by
  rw [strongInteriorRatio]
  have hden : 0 < 1 - 2 * r := by linarith
  rw [lt_div_iff₀ hden]
  linarith

theorem strongLargeAngleRatio_pos {r : ℝ} : 0 < strongLargeAngleRatio r := by
  rw [strongLargeAngleRatio]
  exact div_pos Real.pi_pos (by linarith [Real.arctan_lt_pi_div_two (2 * r)])

/-! ## Elementary scalar estimates -/

/-- Strict `arctan x < x` for positive `x`.  Shared by the endpoint estimates. -/
theorem arctan_lt_self_of_pos {x : ℝ} (hx : 0 < x) :
    Real.arctan x < x := by
  have hy0 : 0 < Real.arctan x := Real.arctan_pos.mpr hx
  have hyhalf : Real.arctan x < Real.pi / 2 := Real.arctan_lt_pi_div_two x
  have h := Real.lt_tan hy0 hyhalf
  rwa [Real.tan_arctan] at h

/-- Strict `x < arcsin x` on `(0,1)`. -/
theorem self_lt_arcsin_of_pos_of_lt_one {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) : x < Real.arcsin x := by
  apply (Real.lt_arcsin_iff_sin_lt' ?_).2
  · exact Real.sin_lt hx0
  · constructor <;> linarith [Real.pi_gt_d20]

/-- Positive isosceles contact gives the strict interior estimate. -/
theorem interior_contact_strict_gap
    {r δ t αmax : ℝ} (hr0 : 0 < r) (hrhalf : r < 1 / 2)
    (hδ0 : 0 < δ) (hδr : δ < r)
    (hu : αmax = Real.arcsin (δ / r))
    (ht : t = Real.arcsin (δ / r) - Real.arctan (2 * δ)) :
    2 * αmax - t < strongInteriorRatio r * t := by
  have hx0 : 0 < δ / r := div_pos hδ0 hr0
  have hx1 : δ / r < 1 := (div_lt_one hr0).2 hδr
  have ha : δ / r < Real.arcsin (δ / r) :=
    self_lt_arcsin_of_pos_of_lt_one hx0 hx1
  have hat : Real.arctan (2 * δ) < 2 * δ :=
    arctan_lt_self_of_pos (by positivity)
  have hB : Real.arctan (2 * δ) < 2 * r * Real.arcsin (δ / r) := by
    have hm := mul_lt_mul_of_pos_left ha (show 0 < 2 * r by positivity)
    have heq : 2 * r * (δ / r) = 2 * δ := by field_simp
    rw [heq] at hm
    linarith
  have hden : 0 < 1 - 2 * r := by linarith
  rw [strongInteriorRatio, div_mul_eq_mul_div, lt_div_iff₀ hden, hu, ht]
  nlinarith

/-! ## The first-contact angle -/

/-- The first-contact angle used in the analytic form of Li's Lemma 3.2. -/
def strongEndpointPhi (r δ₀ : ℝ) : ℝ :=
  Real.arcsin (δ₀ / r) - Real.arctan (2 * δ₀)

/-- The derivative computation on the *full* admissible height interval `[0,r)`.
This is the version needed when the target span is not bounded by
`strongEndpointPhi r a`: the comparison height `δ₀` is then only known to lie
below the radius. -/
theorem strongEndpointPhi_strictMonoOn_radius {r : ℝ}
    (hr0 : 0 < r) (hrhalf : r < 1 / 2) :
    StrictMonoOn (strongEndpointPhi r) (Set.Ico 0 r) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ico 0 r)
      ((Real.continuous_arcsin.comp (continuous_id.div_const r)).sub
        (Real.continuous_arctan.comp (continuous_const.mul continuous_id))).continuousOn
  · intro x hx
    rw [interior_Ico] at hx
    have hxr : x / r ∈ Set.Ioo (-1 : ℝ) 1 := by
      constructor
      · have : 0 < x / r := div_pos hx.1 hr0
        linarith
      · exact (div_lt_one hr0).2 hx.2
    have ha := (Real.hasDerivAt_arcsin (ne_of_gt hxr.1) (ne_of_lt hxr.2)).comp x
      (hasDerivAt_id x |>.div_const r)
    have ht := (hasDerivAt_id x).const_mul (2 : ℝ) |>.arctan
    convert (ha.sub ht).hasDerivWithinAt using 1
  · intro x hx
    rw [interior_Ico] at hx
    have hx0 : 0 < x := hx.1
    have hxrlt : x / r < 1 := (div_lt_one hr0).2 hx.2
    have hxr0 : 0 ≤ x / r := div_nonneg hx0.le hr0.le
    have hrad0 : 0 < 1 - (x / r) ^ 2 := by nlinarith
    have hsqrt0 : 0 < Real.sqrt (1 - (x / r) ^ 2) := Real.sqrt_pos.2 hrad0
    have hsqrt_le : Real.sqrt (1 - (x / r) ^ 2) ≤ 1 := by
      rw [Real.sqrt_le_one]
      nlinarith [sq_nonneg (x / r)]
    have hden : r * Real.sqrt (1 - (x / r) ^ 2) < 1 / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hsqrt_le hr0.le]
    have hfirst : 2 < 1 / Real.sqrt (1 - (x / r) ^ 2) * (1 / r) := by
      calc
        2 < 1 / (r * Real.sqrt (1 - (x / r) ^ 2)) :=
          (lt_div_iff₀ (mul_pos hr0 hsqrt0)).2 (by nlinarith)
        _ = 1 / Real.sqrt (1 - (x / r) ^ 2) * (1 / r) := by field_simp
    have hsecond : 1 / (1 + (2 * x) ^ 2) * 2 ≤ 2 := by
      have hd : 1 ≤ 1 + (2 * x) ^ 2 := by nlinarith [sq_nonneg (2 * x)]
      have hp : 0 < 1 + (2 * x) ^ 2 := by nlinarith [sq_nonneg (2 * x)]
      have := (div_le_one hp).2 hd
      nlinarith
    simp only [id_eq, mul_one]
    change 0 < 1 / √(1 - (x / r) ^ 2) * (1 / r) -
      1 / (1 + (2 * x) ^ 2) * 2
    linarith

@[simp] theorem strongEndpointPhi_zero (r : ℝ) : strongEndpointPhi r 0 = 0 := by
  simp [strongEndpointPhi]

theorem strongEndpointPhi_self {r : ℝ} (hr0 : 0 < r) :
    strongEndpointPhi r r = Real.pi / 2 - Real.arctan (2 * r) := by
  rw [strongEndpointPhi, div_self hr0.ne', Real.arcsin_one]

theorem continuous_strongEndpointPhi (r : ℝ) :
    Continuous (strongEndpointPhi r) :=
  (Real.continuous_arcsin.comp (continuous_id.div_const r)).sub
    (Real.continuous_arctan.comp (continuous_const.mul continuous_id))

/-- **Range of the first-contact angle.**  Every target span strictly between
zero and the saturation threshold `π/2 - arctan (2r)` is attained by a unique
admissible comparison height `δ₀ ∈ (0,r)`.  This is what replaces a
caller-provided `δ₀` witness. -/
theorem exists_strongEndpointPhi_eq {r t : ℝ} (hr0 : 0 < r)
    (ht0 : 0 < t) (httop : t < Real.pi / 2 - Real.arctan (2 * r)) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < r ∧ strongEndpointPhi r δ₀ = t := by
  have hmem : t ∈ Set.Ioo (strongEndpointPhi r 0) (strongEndpointPhi r r) := by
    rw [strongEndpointPhi_zero, strongEndpointPhi_self hr0]
    exact ⟨ht0, httop⟩
  obtain ⟨δ₀, hδ₀, hval⟩ :=
    intermediate_value_Ioo hr0.le (continuous_strongEndpointPhi r).continuousOn hmem
  exact ⟨δ₀, hδ₀.1, hδ₀.2, hval⟩

/-- Strict monotonicity on `[0,r)` converts the selected-span sandwich into
`h ≤ δ₀` without any reference to a height cap. -/
theorem strongEndpointPhi_le_of_le {r h δ₀ : ℝ} (hr0 : 0 < r) (hrhalf : r < 1 / 2)
    (hh : h ∈ Set.Ico 0 r) (hδ : δ₀ ∈ Set.Ico 0 r)
    (hle : strongEndpointPhi r h ≤ strongEndpointPhi r δ₀) : h ≤ δ₀ :=
  ((strongEndpointPhi_strictMonoOn_radius hr0 hrhalf).le_iff_le hh hδ).1 hle

/-- A selected mixed span with effective base at least `1/2` dominates the
canonical Figure-5 first-contact span. -/
theorem strongEndpointPhi_le_of_mixedSpan
    {r h x effectiveBase selectedSpan : ℝ}
    (hh : 0 ≤ h) (hbase : 1 / 2 ≤ effectiveBase)
    (hx : x = Real.arctan (h / effectiveBase))
    (hspan : selectedSpan = Real.arcsin (h / r) - x) :
    strongEndpointPhi r h ≤ selectedSpan := by
  have hbase0 : 0 < effectiveBase := by linarith
  have hquot : h / effectiveBase ≤ 2 * h := by
    rw [div_le_iff₀ hbase0]
    nlinarith
  have hatan := Real.arctan_mono hquot
  rw [hspan, hx, strongEndpointPhi]
  linarith

/-! ## The clean endpoint parameter domain

The endpoint geometry consumes exactly four parameters: the height cap `a`, the
outer radius `r₀` of the Case-I radial interval, the inner-class radius `R₁`,
and the dilation factor `g`.  There is deliberately **no** `rλ` field: the
frozen radius is an artefact of one particular choice of `g`, and belongs to the
analytic package that certifies `g`, not to the geometric interface.
-/

/-- The clean parameter tuple of the Figure-5 endpoint machinery. -/
structure Figure5EndpointDomain where
  /-- The Case-I support-height cap. -/
  a : ℝ
  /-- The outer radius of the Case-I radial interval `[a, r₀]`. -/
  r0 : ℝ
  /-- The radius defining the inner direction class `A_in_radius R₁`. -/
  R1 : ℝ
  /-- The radial dilation factor of the endpoint containment. -/
  g : ℝ → ℝ
  a_pos : 0 < a
  a_le_r0 : a ≤ r0
  r0_lt_half : r0 < 1 / 2
  R1_pos : 0 < R1

namespace Figure5EndpointDomain

variable (P : Figure5EndpointDomain)

/-- The Case-I radial interval of the domain. -/
def radialInterval : Set ℝ := Icc P.a P.r0

theorem mem_radialInterval_iff {r : ℝ} :
    r ∈ P.radialInterval ↔ r ∈ Icc P.a P.r0 := Iff.rfl

variable {P}

theorem radius_pos {r : ℝ} (hr : r ∈ Icc P.a P.r0) : 0 < r :=
  P.a_pos.trans_le hr.1

theorem radius_lt_half {r : ℝ} (hr : r ∈ Icc P.a P.r0) : r < 1 / 2 :=
  hr.2.trans_lt P.r0_lt_half

theorem radius_nonneg {r : ℝ} (hr : r ∈ Icc P.a P.r0) : 0 ≤ r :=
  (radius_pos hr).le

theorem a_lt_half : P.a < 1 / 2 :=
  P.a_le_r0.trans_lt P.r0_lt_half

theorem a_mem : P.a ∈ Icc P.a P.r0 := ⟨le_rfl, P.a_le_r0⟩

end Figure5EndpointDomain

/-! ## The analytic package

These are exactly the analytic facts the endpoint geometry cannot prove for
itself.  Every other step of the Figure-5 argument is either pure geometry or
one of the parameter-free scalar estimates above.

* `one_lt_g` is what turns the trivial "far side of the target chart" endpoint
  estimate into a *strict* gap.  It is derivable from `interior_le_g` (see
  `Figure5EndpointAnalyticPackage.of_dominations`), and is kept as a field so
  that a tuple may certify it directly.
* `interior_le_g` and `largeAngle_le_g` are the two branch dominations that the
  geometry actually consumes: the first for the interior/height-cutoff endpoint,
  the second to know that a non-saturated target span lies inside the base-ray
  chart.
* `base_ray_gap` is the single load-bearing tuple-specific theorem.  Its
  hypotheses are exactly the data the base-base geometric branch produces, and
  its conclusion is already stated against `P.g`, so no frozen ratio leaks into
  the geometric API.  It is the analogue of `base_ray_frozen_analytic` composed
  with `strongFrozenRatio_le_paperG`.
-/

/-- The load-bearing analytic gates of the Figure-5 endpoint closure. -/
structure Figure5EndpointAnalyticPackage (P : Figure5EndpointDomain) : Prop where
  one_lt_g : ∀ {r : ℝ}, r ∈ Icc P.a P.r0 → 1 < P.g r
  interior_le_g : ∀ {r : ℝ}, r ∈ Icc P.a P.r0 → strongInteriorRatio r ≤ P.g r
  largeAngle_le_g : ∀ {r : ℝ}, r ∈ Icc P.a P.r0 → strongLargeAngleRatio r ≤ P.g r
  base_ray_gap : ∀ {r t α : ℝ}, r ∈ Icc P.a P.r0 → 0 < t →
    t < Real.pi / 2 - Real.arctan (2 * r) → t / 2 ≤ α → α ≤ Real.pi / 2 →
    0 ≤ Real.sin t → Real.sin α ≤ P.R1 * Real.sin t →
    Real.sin α * Real.sin (α - t) ≤ P.a * Real.sin t →
    2 * α - t < P.g r * t

namespace Figure5EndpointAnalyticPackage

variable {P : Figure5EndpointDomain}

/-- Smart constructor: `one_lt_g` never has to be certified separately, because
the interior ratio already exceeds one on the whole radial interval. -/
theorem of_dominations
    (hint : ∀ {r : ℝ}, r ∈ Icc P.a P.r0 → strongInteriorRatio r ≤ P.g r)
    (hlarge : ∀ {r : ℝ}, r ∈ Icc P.a P.r0 → strongLargeAngleRatio r ≤ P.g r)
    (hbase : ∀ {r t α : ℝ}, r ∈ Icc P.a P.r0 → 0 < t →
      t < Real.pi / 2 - Real.arctan (2 * r) → t / 2 ≤ α → α ≤ Real.pi / 2 →
      0 ≤ Real.sin t → Real.sin α ≤ P.R1 * Real.sin t →
      Real.sin α * Real.sin (α - t) ≤ P.a * Real.sin t →
      2 * α - t < P.g r * t) :
    Figure5EndpointAnalyticPackage P where
  one_lt_g := fun hr =>
    (one_lt_strongInteriorRatio (Figure5EndpointDomain.radius_pos hr)
      (Figure5EndpointDomain.radius_lt_half hr)).trans_le (hint hr)
  interior_le_g := hint
  largeAngle_le_g := hlarge
  base_ray_gap := hbase

theorem one_le_g (HP : Figure5EndpointAnalyticPackage P) {r : ℝ}
    (hr : r ∈ Icc P.a P.r0) : 1 ≤ P.g r := (HP.one_lt_g hr).le

theorem g_pos (HP : Figure5EndpointAnalyticPackage P) {r : ℝ}
    (hr : r ∈ Icc P.a P.r0) : 0 < P.g r :=
  lt_trans zero_lt_one (HP.one_lt_g hr)

/-- Below saturation the target span is automatically inside the base-ray
chart.  This is the exact complement of the large-angle branch, and the only
place `largeAngle_le_g` is used. -/
theorem target_lt_top_of_not_saturated (HP : Figure5EndpointAnalyticPackage P)
    {r t : ℝ} (hr : r ∈ Icc P.a P.r0) (hsat : ¬ Real.pi ≤ P.g r * t) :
    t < Real.pi / 2 - Real.arctan (2 * r) := by
  have hden : 0 < Real.pi / 2 - Real.arctan (2 * r) := by
    linarith [Real.arctan_lt_pi_div_two (2 * r)]
  by_contra hge
  rw [not_lt] at hge
  apply hsat
  have hlarge : strongLargeAngleRatio r ≤ P.g r := HP.largeAngle_le_g hr
  have hpos : 0 < strongLargeAngleRatio r := strongLargeAngleRatio_pos
  calc
    Real.pi = strongLargeAngleRatio r * (Real.pi / 2 - Real.arctan (2 * r)) := by
      rw [strongLargeAngleRatio, div_mul_cancel₀]
      exact hden.ne'
    _ ≤ strongLargeAngleRatio r * t := mul_le_mul_of_nonneg_left hge hpos.le
    _ ≤ P.g r * t := mul_le_mul_of_nonneg_right hlarge (hden.trans_le hge).le

end Figure5EndpointAnalyticPackage

end

end StarKakeyaLower
