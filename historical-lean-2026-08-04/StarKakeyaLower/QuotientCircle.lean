import StarKakeyaLower.CircleDilation
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.MeasureTheory.Group.AddCircle

/-!
# Saturated quotient-circle intervals and the proper common-lift adapter

This file deliberately uses a **saturated** circle-interval convention.  An
interval of nominal length at least the positive period is `Set.univ`; below
that threshold it is the image of the corresponding open real interval.  In
particular, the equality case is not represented by the image of an open
interval of length one period (which would miss one point).

The adapter includes the cut-free Haar measure formula, integral-period
compatible recentering, a unified proper/saturated single-owner transition,
the countable component extraction after a common cut, and the final
unconditional arbitrary-family theorem.
-/

open Set MeasureTheory

namespace StarKakeyaLower

noncomputable section

/--
The saturated quotient image of `(a,b)`.  At nominal length `b-a ≥ p` it is the
whole positive-period circle; below that threshold it is the ordinary quotient
image of the open interval.
-/
def quotientInterval (p a b : ℝ) [Fact (0 < p)] : Set (AddCircle p) :=
  if p ≤ b - a then Set.univ
  else (fun t : ℝ => (t : AddCircle p)) '' Ioo a b

/-- A centered saturated open arc, without choosing a cut. -/
def quotientCenteredArc (p x r : ℝ) [Fact (0 < p)] : Set (AddCircle p) :=
  quotientInterval p (x - r) (x + r)

/-- Same-center dilation of a saturated quotient-centered arc. -/
def quotientCenteredDilate (c p x r : ℝ) [Fact (0 < p)] : Set (AddCircle p) :=
  quotientInterval p (x - c * r) (x + c * r)

/-- Zero-safe centered arc.  Positive radii retain the open quotient arc used
by the component argument, while radius zero records its actual centre rather
than the empty open interval. -/
def quotientHybridCenteredArc (p x r : ℝ) [Fact (0 < p)] : Set (AddCircle p) :=
  if r = 0 then {(x : AddCircle p)} else quotientCenteredArc p x r

/-- Zero-safe same-centre dilation.  A zero-radius arc remains its singleton;
all nonzero radii use the saturated open dilation. -/
def quotientHybridCenteredDilate (c p x r : ℝ) [Fact (0 < p)] :
    Set (AddCircle p) :=
  if r = 0 then {(x : AddCircle p)} else quotientCenteredDilate c p x r

/-- Saturated dilation of a lifted owner component, followed by quotienting. -/
def quotientComponentDilate (c p a b : ℝ) [Fact (0 < p)] : Set (AddCircle p) :=
  quotientInterval p ((a + b) / 2 - c * (b - a) / 2)
    ((a + b) / 2 + c * (b - a) / 2)

/-- Below the saturation threshold, `quotientInterval` is the quotient image. -/
theorem quotientInterval_of_lt
    {p a b : ℝ} [Fact (0 < p)] (h : b - a < p) :
    quotientInterval p a b = (fun t : ℝ => (t : AddCircle p)) '' Ioo a b := by
  simp [quotientInterval, not_le.mpr h]

/-- At or above the saturation threshold, `quotientInterval` is the whole circle. -/
theorem quotientInterval_eq_univ_of_le
    {p a b : ℝ} [Fact (0 < p)] (h : p ≤ b - a) :
    quotientInterval p a b = Set.univ := by
  simp [quotientInterval, h]

/-- Regression theorem: nominal length exactly one period is saturated. -/
theorem quotientInterval_eq_univ_of_length_eq
    {p a b : ℝ} [Fact (0 < p)] (h : b - a = p) :
    quotientInterval p a b = Set.univ :=
  quotientInterval_eq_univ_of_le h.ge

/-- Regression theorem: a strictly super-period interval is saturated. -/
theorem quotientInterval_eq_univ_of_length_gt
    {p a b : ℝ} [Fact (0 < p)] (h : p < b - a) :
    quotientInterval p a b = Set.univ :=
  quotientInterval_eq_univ_of_le h.le

/-- The centered API is definitionally connected to the base interval API. -/
theorem quotientCenteredArc_eq_quotientInterval
    (p x r : ℝ) [Fact (0 < p)] :
    quotientCenteredArc p x r = quotientInterval p (x - r) (x + r) := rfl

/-- A component dilation whose nominal length reaches the period is saturated. -/
theorem quotientComponentDilate_eq_univ
    {c p a b : ℝ} [Fact (0 < p)] (hsat : p ≤ c * (b - a)) :
    quotientComponentDilate c p a b = Set.univ := by
  apply quotientInterval_eq_univ_of_le
  nlinarith

/-- A centered arc is contained in its same-center dilation. -/
theorem quotientCenteredArc_subset_quotientCenteredDilate
    {c p x r : ℝ} [Fact (0 < p)] (hc : 1 ≤ c) (hr : 0 ≤ r) :
    quotientCenteredArc p x r ⊆ quotientCenteredDilate c p x r := by
  by_cases hsat : p ≤ (x + c * r) - (x - c * r)
  · have hsat' : p ≤ (x + c * r) - (x - c * r) := hsat
    rw [quotientCenteredDilate, quotientInterval_eq_univ_of_le hsat']
    exact subset_univ _
  · have htarget : (x + c * r) - (x - c * r) < p := lt_of_not_ge hsat
    have hsource : (x + r) - (x - r) < p := by nlinarith
    rw [quotientCenteredArc, quotientCenteredDilate,
      quotientInterval_of_lt hsource, quotientInterval_of_lt htarget]
    apply image_mono
    apply Ioo_subset_Ioo <;> nlinarith

/--
Proper/common-lift adapter.  The dilated source arc is assumed below one
period, so it is genuinely the quotient image of its chosen real lift.  The
owner may itself dilate past the threshold; that case is handled by the
saturated definition rather than by pretending a wrapped component has a
single lift.
-/
theorem quotientCenteredDilate_subset_quotientComponentDilate_of_lt
    {c p x r a b : ℝ} [Fact (0 < p)]
    (hc : 1 ≤ c) (hr : 0 ≤ r)
    (hproper : (x + c * r) - (x - c * r) < p)
    (howner : centeredInterval x r ⊆ Ioo a b) :
    quotientCenteredDilate c p x r ⊆ quotientComponentDilate c p a b := by
  have hline := centeredDilate_subset_componentDilate hc hr howner
  by_cases hsat : p ≤
      ((a + b) / 2 + c * (b - a) / 2) -
        ((a + b) / 2 - c * (b - a) / 2)
  · rw [quotientComponentDilate, quotientInterval_eq_univ_of_le hsat]
    exact subset_univ _
  · rw [quotientCenteredDilate, quotientInterval_of_lt hproper]
    rw [quotientComponentDilate,
      quotientInterval_of_lt (lt_of_not_ge hsat)]
    exact image_mono hline

/--
Saturated-owner adapter.  If the dilated owner has nominal length at least one
period, it is the whole circle, so every dilated centered arc is contained in
it.  This is the explicit replacement for the former wrapped-owner comment.
-/
theorem quotientCenteredDilate_subset_quotientComponentDilate_of_saturated
    {c p x r a b : ℝ} [Fact (0 < p)]
    (hsat : p ≤ c * (b - a)) :
    quotientCenteredDilate c p x r ⊆ quotientComponentDilate c p a b := by
  rw [quotientComponentDilate_eq_univ hsat]
  exact subset_univ _

/--
Exact cut/lift lemma for a proper (unsaturated) interval.  Besides fitting in a
fundamental domain, the nominal interval length must be below the period; then
`AddCircle.equivIco` recovers exactly the corresponding subtype interval.
-/
theorem equivIco_image_quotientInterval
    {p cut a b : ℝ} [Fact (0 < p)]
    (hproper : b - a < p)
    (hcut : Ioo a b ⊆ Ico cut (cut + p)) :
    AddCircle.equivIco p cut '' quotientInterval p a b =
      {z : Ico cut (cut + p) | (z : ℝ) ∈ Ioo a b} := by
  rw [quotientInterval_of_lt hproper]
  ext z
  constructor
  · rintro ⟨q, ⟨y, hy, rfl⟩, hq⟩
    have heq : AddCircle.equivIco p cut (y : AddCircle p) =
        (⟨y, hcut hy⟩ : Ico cut (cut + p)) :=
      AddCircle.equivIco_coe_eq (hcut hy)
    rw [heq] at hq
    simpa [← hq] using hy
  · intro hz
    have hy : (z : ℝ) ∈ Ioo a b := hz
    refine ⟨((z : ℝ) : AddCircle p), ⟨(z : ℝ), hy, rfl⟩, ?_⟩
    exact AddCircle.equivIco_coe_eq (hcut hy)

/-- Quotienting commutes with an arbitrary union of lifted sets. -/
theorem quotient_image_iUnion {ι : Type*} (p : ℝ) [Fact (0 < p)] (s : ι → Set ℝ) :
    (fun t : ℝ => (t : AddCircle p)) '' (⋃ i, s i) =
      ⋃ i, (fun t : ℝ => (t : AddCircle p)) '' s i := by
  exact image_iUnion

/-- A proper nonempty quotient interval is the metric ball with the same
midpoint and half-length.  This statement is cut-free: the source interval may
cross any preselected fundamental-domain boundary. -/
theorem quotientInterval_eq_ball
    {p a b : ℝ} [Fact (0 < p)] (hproper : b - a < p) :
    quotientInterval p a b =
      Metric.ball (↑((a + b) / 2) : AddCircle p) ((b - a) / 2) := by
  rw [quotientInterval_of_lt hproper]
  ext q
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm, ← QuotientAddGroup.mk_sub]
    have habs : |y - (a + b) / 2| ≤ |p| / 2 := by
      rw [abs_le, abs_of_pos (Fact.out : 0 < p)]
      constructor <;> linarith [hy.1, hy.2]
    rw [(AddCircle.norm_coe_eq_abs_iff (p := p)
      (Fact.out : 0 < p).ne').2 habs, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  · intro hq
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [Metric.mem_ball, dist_eq_norm, ← QuotientAddGroup.mk_sub,
      AddCircle.norm_eq] at hq
    let z : ℝ := y - (a + b) / 2 -
      (round (p⁻¹ * (y - (a + b) / 2)) : ℝ) * p
    refine ⟨(a + b) / 2 + z, ?_, ?_⟩
    · rw [mem_Ioo]
      dsimp [z] at hq ⊢
      rw [abs_lt] at hq
      constructor <;> linarith [hq.1, hq.2]
    · change (↑((a + b) / 2 + z) : AddCircle p) = (y : AddCircle p)
      simp only [z, AddCircle.coe_add, AddCircle.coe_sub]
      rw [← zsmul_eq_mul, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero,
        sub_zero, add_sub_cancel]

/-- Every saturated quotient interval is open.  In the proper nonempty branch it
is a metric ball; backwards and degenerate intervals are empty. -/
theorem isOpen_quotientInterval
    (p a b : ℝ) [Fact (0 < p)] : IsOpen (quotientInterval p a b) := by
  by_cases hsat : p ≤ b - a
  · rw [quotientInterval_eq_univ_of_le hsat]
    exact isOpen_univ
  · have hproper : b - a < p := lt_of_not_ge hsat
    by_cases hab : a < b
    · rw [quotientInterval_eq_ball hproper]
      exact Metric.isOpen_ball
    · rw [quotientInterval_of_lt hproper]
      simp [Ioo_eq_empty hab]

/-- Every saturated quotient interval is Borel measurable, including empty,
proper wrapped, exactly-period, and super-period cases. -/
theorem measurableSet_quotientInterval
    (p a b : ℝ) [Fact (0 < p)] : MeasurableSet (quotientInterval p a b) := by
  by_cases hsat : p ≤ b - a
  · rw [quotientInterval_eq_univ_of_le hsat]
    exact MeasurableSet.univ
  · have hproper : b - a < p := lt_of_not_ge hsat
    by_cases hab : a < b
    · rw [quotientInterval_eq_ball hproper]
      exact measurableSet_ball
    · rw [quotientInterval_of_lt hproper]
      simp [Ioo_eq_empty hab]

/-- Haar length of a saturated quotient interval.  The `min` records the
proper/full-circle split and `ofReal` also handles empty backwards intervals. -/
theorem volume_quotientInterval
    (p a b : ℝ) [Fact (0 < p)] :
    volume (quotientInterval p a b) = ENNReal.ofReal (min p (b - a)) := by
  by_cases hsat : p ≤ b - a
  · rw [quotientInterval_eq_univ_of_le hsat, AddCircle.measure_univ, min_eq_left hsat]
  · have hproper : b - a < p := lt_of_not_ge hsat
    by_cases hab : a < b
    · rw [quotientInterval_eq_ball hproper]
      rw [measure_congr AddCircle.closedBall_ae_eq_ball.symm,
        AddCircle.volume_closedBall]
      congr 2
      ring
    · rw [quotientInterval_of_lt hproper]
      simp [Ioo_eq_empty hab, min_eq_right hproper.le,
        ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr (not_lt.mp hab))]

/-- Translating both endpoints by an integral number of periods does not change
an interval on the quotient circle, in either the proper or saturated branch. -/
theorem quotientInterval_add_int_mul_period
    (p a b : ℝ) [Fact (0 < p)] (n : ℤ) :
    quotientInterval p (a + (n : ℝ) * p) (b + (n : ℝ) * p) =
      quotientInterval p a b := by
  by_cases hsat : p ≤ b - a
  · rw [quotientInterval_eq_univ_of_le hsat]
    apply quotientInterval_eq_univ_of_le
    linarith
  · have hproper : b - a < p := lt_of_not_ge hsat
    rw [quotientInterval_of_lt hproper]
    rw [quotientInterval_of_lt (by linarith :
      (b + (n : ℝ) * p) - (a + (n : ℝ) * p) < p)]
    ext q
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y - (n : ℝ) * p, ?_, ?_⟩
      · constructor <;> linarith [hy.1, hy.2]
      · change (↑(y - (n : ℝ) * p) : AddCircle p) = (y : AddCircle p)
        rw [AddCircle.coe_sub, ← zsmul_eq_mul, AddCircle.coe_zsmul,
          AddCircle.coe_period, smul_zero, sub_zero]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y + (n : ℝ) * p, ?_, ?_⟩
      · constructor <;> linarith [hy.1, hy.2]
      · change (↑(y + (n : ℝ) * p) : AddCircle p) = (y : AddCircle p)
        rw [AddCircle.coe_add, ← zsmul_eq_mul, AddCircle.coe_zsmul,
          AddCircle.coe_period, smul_zero, add_zero]

/-- Integral-period recentering preserves both a base arc and its dilation. -/
theorem quotientCenteredArc_add_int_mul_period
    (p x r : ℝ) [Fact (0 < p)] (n : ℤ) :
    quotientCenteredArc p (x + (n : ℝ) * p) r = quotientCenteredArc p x r := by
  rw [quotientCenteredArc, quotientCenteredArc]
  convert quotientInterval_add_int_mul_period p (x - r) (x + r) n using 1 <;> ring

/-- Dilated version of `quotientCenteredArc_add_int_mul_period`. -/
theorem quotientCenteredDilate_add_int_mul_period
    (c p x r : ℝ) [Fact (0 < p)] (n : ℤ) :
    quotientCenteredDilate c p (x + (n : ℝ) * p) r =
      quotientCenteredDilate c p x r := by
  rw [quotientCenteredDilate, quotientCenteredDilate]
  convert quotientInterval_add_int_mul_period p (x - c * r) (x + c * r) n using 1 <;> ring

/-- Unified single-owner transition.  If the dilated source saturates, owner
containment forces the dilated owner to saturate as well; otherwise the proper
common-lift theorem applies.  No wrapped or equality boundary is discarded. -/
theorem quotientCenteredDilate_subset_quotientComponentDilate
    {c p x r a b : ℝ} [Fact (0 < p)]
    (hc : 1 ≤ c) (hr : 0 ≤ r)
    (howner : centeredInterval x r ⊆ Ioo a b) :
    quotientCenteredDilate c p x r ⊆ quotientComponentDilate c p a b := by
  rcases hr.eq_or_lt with rfl | hrpos
  · rw [quotientCenteredDilate, quotientInterval_of_lt
      (by have hp : 0 < p := Fact.out; simpa using hp)]
    simp
  · by_cases hproper : (x + c * r) - (x - c * r) < p
    · exact quotientCenteredDilate_subset_quotientComponentDilate_of_lt
        hc hrpos.le hproper howner
    · have hend : a ≤ x - r ∧ x + r ≤ b :=
        (Ioo_subset_Ioo_iff (by linarith : x - r < x + r)).mp howner
      apply quotientCenteredDilate_subset_quotientComponentDilate_of_saturated
      have hsource : p ≤ (x + c * r) - (x - c * r) := le_of_not_gt hproper
      nlinarith

/-- Exact Haar length of a saturated component dilation. -/
theorem volume_quotientComponentDilate
    (c p a b : ℝ) [Fact (0 < p)] :
    volume (quotientComponentDilate c p a b) =
      ENNReal.ofReal (min p (c * (b - a))) := by
  rw [quotientComponentDilate, volume_quotientInterval]
  congr 2
  ring

/-- A proper component grows by at most the same-center factor, including the
transition where its dilation first becomes the full circle. -/
theorem volume_quotientComponentDilate_le
    {c p a b : ℝ} [Fact (0 < p)]
    (hc : 1 ≤ c) (hproper : b - a ≤ p) :
    volume (quotientComponentDilate c p a b) ≤
      ENNReal.ofReal c * volume (quotientInterval p a b) := by
  rw [volume_quotientComponentDilate, volume_quotientInterval,
    min_eq_right hproper]
  rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ c)]
  exact ENNReal.ofReal_le_ofReal (min_le_right _ _)

/-- Proper-component branch of the arbitrary-family quotient-circle adapter.
The source family `ι` is completely arbitrary; only the disjoint open-component
index `κ` is countable.  The explicit `hcomponents` and compatible-lift
`howner` hypotheses are the decomposition interface produced below by the
common-cut extraction, rather than a finiteness assumption on the arc family. -/
theorem volume_iUnion_quotientCenteredDilate_le_of_components
    {ι κ : Type*} [Countable κ]
    (c p : ℝ) [Fact (0 < p)] (hc : 1 ≤ c)
    (x r : ι → ℝ) (a b : κ → ℝ) (owner : ι → κ)
    (hr : ∀ i, 0 ≤ r i)
    (hproper : ∀ j, b j - a j ≤ p)
    (howner : ∀ i, centeredInterval (x i) (r i) ⊆
      Ioo (a (owner i)) (b (owner i)))
    (hdisjoint : _root_.Pairwise (fun i j =>
      Disjoint (quotientInterval p (a i) (b i))
        (quotientInterval p (a j) (b j))))
    (hcomponents : (⋃ i, quotientCenteredArc p (x i) (r i)) =
      ⋃ j, quotientInterval p (a j) (b j)) :
    volume (⋃ i, quotientCenteredDilate c p (x i) (r i)) ≤
      ENNReal.ofReal c *
        volume (⋃ i, quotientCenteredArc p (x i) (r i)) := by
  apply measure_iUnion_le_mul_of_disjoint_components
      volume (ENNReal.ofReal c)
      (fun i => quotientCenteredArc p (x i) (r i))
      (fun i => quotientCenteredDilate c p (x i) (r i))
      (fun j => quotientInterval p (a j) (b j))
      (fun j => quotientComponentDilate c p (a j) (b j)) owner
  · intro i
    exact quotientCenteredDilate_subset_quotientComponentDilate
      hc (hr i) (howner i)
  · exact hdisjoint
  · exact fun j => measurableSet_quotientInterval p (a j) (b j)
  · intro j
    exact volume_quotientComponentDilate_le hc (hproper j)
  · exact hcomponents

/-- Compatible-lift form of the proper-component adapter.  Each original centre
may be shifted by its own integral period before assigning an owner component;
the quotient base arc and quotient dilation are unchanged. -/
theorem volume_iUnion_quotientCenteredDilate_le_of_components_with_shifts
    {ι κ : Type*} [Countable κ]
    (c p : ℝ) [Fact (0 < p)] (hc : 1 ≤ c)
    (x r : ι → ℝ) (a b : κ → ℝ) (owner : ι → κ) (shift : ι → ℤ)
    (hr : ∀ i, 0 ≤ r i)
    (hproper : ∀ j, b j - a j ≤ p)
    (howner : ∀ i,
      centeredInterval (x i + (shift i : ℝ) * p) (r i) ⊆
        Ioo (a (owner i)) (b (owner i)))
    (hdisjoint : _root_.Pairwise (fun i j =>
      Disjoint (quotientInterval p (a i) (b i))
        (quotientInterval p (a j) (b j))))
    (hcomponents : (⋃ i, quotientCenteredArc p (x i) (r i)) =
      ⋃ j, quotientInterval p (a j) (b j)) :
    volume (⋃ i, quotientCenteredDilate c p (x i) (r i)) ≤
      ENNReal.ofReal c *
        volume (⋃ i, quotientCenteredArc p (x i) (r i)) := by
  have hcomponents' :
      (⋃ i, quotientCenteredArc p (x i + (shift i : ℝ) * p) (r i)) =
        ⋃ j, quotientInterval p (a j) (b j) := by
    simpa only [quotientCenteredArc_add_int_mul_period] using hcomponents
  have h := volume_iUnion_quotientCenteredDilate_le_of_components
    c p hc (fun i => x i + (shift i : ℝ) * p) r a b owner hr hproper
    howner hdisjoint hcomponents'
  simpa only [quotientCenteredArc_add_int_mul_period,
    quotientCenteredDilate_add_int_mul_period] using h

/-- A common omitted cut selects an integral translate of every nonempty arc
inside one open fundamental interval.  The zero-radius case is empty and needs
no distinguished translate.  Endpoint contact is allowed: the open interval
still lies in the common open fundamental interval. -/
theorem exists_shift_centeredInterval_subset_Ioo
    {p cut x r : ℝ} [Fact (0 < p)] (hr : 0 ≤ r)
    (havoid : (cut : AddCircle p) ∉ quotientCenteredArc p x r) :
    ∃ n : ℤ, centeredInterval (x + (n : ℝ) * p) r ⊆ Ioo cut (cut + p) := by
  rcases hr.eq_or_lt with rfl | hrpos
  · exact ⟨0, by simp [centeredInterval]⟩
  obtain ⟨n, hn, -⟩ := existsUnique_add_zsmul_mem_Ico (Fact.out : 0 < p) x cut
  refine ⟨n, ?_⟩
  have hn' : x + (n : ℝ) * p ∈ Ico cut (cut + p) := by
    simpa [zsmul_eq_mul] using hn
  have hproper : (x + r) - (x - r) < p := by
    by_contra h
    have hs : p ≤ (x + r) - (x - r) := le_of_not_gt h
    rw [quotientCenteredArc, quotientInterval_eq_univ_of_le hs] at havoid
    exact havoid (Set.mem_univ _)
  have hleft : cut ≤ x + (n : ℝ) * p - r := by
    by_contra h
    have hmem : cut ∈ centeredInterval (x + (n : ℝ) * p) r := by
      exact ⟨lt_of_not_ge h, by linarith [hn'.1, hrpos]⟩
    apply havoid
    rw [← quotientCenteredArc_add_int_mul_period p x r n]
    rw [quotientCenteredArc, quotientInterval_of_lt (by simpa using hproper)]
    exact ⟨cut, hmem, rfl⟩
  have hright : x + (n : ℝ) * p + r ≤ cut + p := by
    by_contra h
    have hmem : cut + p ∈ centeredInterval (x + (n : ℝ) * p) r := by
      exact ⟨by linarith [hn'.2], lt_of_not_ge h⟩
    apply havoid
    rw [← quotientCenteredArc_add_int_mul_period p x r n]
    rw [quotientCenteredArc, quotientInterval_of_lt (by simpa using hproper)]
    refine ⟨cut + p, hmem, ?_⟩
    change (↑(cut + p) : AddCircle p) = (cut : AddCircle p)
    rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]
  intro y hy
  exact ⟨hleft.trans_lt hy.1, hy.2.trans_le hright⟩

/-- The image of an open fundamental interval omits exactly its cut point. -/
theorem quotient_image_fundamental_Ioo
    (p cut : ℝ) [Fact (0 < p)] :
    (fun t : ℝ => (t : AddCircle p)) '' Ioo cut (cut + p) =
      ({(cut : AddCircle p)} : Set (AddCircle p))ᶜ := by
  ext q
  constructor
  · rintro ⟨y, hy, rfl⟩ h
    have hyIco : y ∈ Ico cut (cut + p) := ⟨hy.1.le, hy.2⟩
    have hcIco : cut ∈ Ico cut (cut + p) :=
      ⟨le_rfl, by linarith [Fact.out (p := 0 < p)]⟩
    exact hy.1.ne' ((AddCircle.coe_eq_coe_iff_of_mem_Ico hyIco hcIco).mp h)
  · intro hq
    let y : ℝ := AddCircle.equivIco p cut q
    have hy : y ∈ Ico cut (cut + p) := (AddCircle.equivIco p cut q).property
    have hcy : cut < y := by
      apply lt_of_le_of_ne hy.1
      intro heq
      apply hq
      rw [Set.mem_singleton_iff]
      rw [← AddCircle.coe_equivIco (p := p) (a := cut) (y := q)]
      exact congrArg (fun z : ℝ => (z : AddCircle p)) heq.symm
    exact ⟨y, ⟨hcy, hy.2⟩, AddCircle.coe_equivIco⟩

/-- A nonempty open interval contained in `U` belongs to one of its ordered
connected components. -/
theorem exists_openComponent_superset_Ioo
    {U : Set ℝ} {a b : ℝ} (hab : a < b) (hsub : Ioo a b ⊆ U) :
    ∃ j : OpenComponentIndex U, Ioo a b ⊆ openComponent U j := by
  let z : U := ⟨(a + b) / 2, hsub (by constructor <;> linarith)⟩
  have hj : U.ordConnectedProj z ∈ U.ordConnectedSection := Set.mem_range_self z
  let j : OpenComponentIndex U := ⟨U.ordConnectedProj z, hj⟩
  refine ⟨j, ?_⟩
  intro y hy
  change y ∈ U.ordConnectedComponent (j : ℝ)
  rw [Set.mem_ordConnectedComponent]
  have hzcomp : (z : ℝ) ∈ U.ordConnectedComponent (j : ℝ) :=
    Set.mem_ordConnectedComponent_ordConnectedProj U z
  rw [Set.mem_ordConnectedComponent, uIcc_comm] at hzcomp
  have hzI : (z : ℝ) ∈ Ioo a b := by
    dsimp [z]
    constructor <;> linarith
  rw [uIcc_comm]
  exact (uIcc_subset_uIcc_union_uIcc
    (a := y) (b := (z : ℝ)) (c := (j : ℝ))).trans
      (union_subset
        (Set.ordConnected_Ioo.uIcc_subset hy hzI |>.trans hsub)
        hzcomp)

/-- Common-cut proper branch, including an empty dummy owner for zero-radius
arcs.  The exceptional one-component fundamental interval is separated because
its quotient is a punctured full circle while `quotientInterval` deliberately
saturates at exact period. -/
theorem volume_iUnion_quotientCenteredDilate_le_of_common_cut
    {ι : Type*} (c p cut : ℝ) [Fact (0 < p)] (hc : 1 ≤ c)
    (x r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (shift : ι → ℤ)
    (hshift : ∀ i, centeredInterval (x i + (shift i : ℝ) * p) (r i) ⊆
      Ioo cut (cut + p))
    (hnotfull : (⋃ i, centeredInterval (x i + (shift i : ℝ) * p) (r i)) ≠
      Ioo cut (cut + p)) :
    volume (⋃ i, quotientCenteredDilate c p (x i) (r i)) ≤
      ENNReal.ofReal c * volume (⋃ i, quotientCenteredArc p (x i) (r i)) := by
  let W : Set ℝ := ⋃ i, centeredInterval (x i + (shift i : ℝ) * p) (r i)
  have hWo : IsOpen W := isOpen_iUnion fun i => isOpen_Ioo
  have hWsub : W ⊆ Ioo cut (cut + p) := iUnion_subset hshift
  let K := OpenComponentIndex W
  let a : Option K → ℝ := fun j => match j with
    | none => cut
    | some j => sInf (openComponent W j)
  let b : Option K → ℝ := fun j => match j with
    | none => cut
    | some j => sSup (openComponent W j)
  have hcomponent (j : K) :
      openComponent W j = Ioo (a (some j)) (b (some j)) := by
    apply openComponent_eq_Ioo_csInf_csSup hWo
    · exact bddBelow_def.mpr ⟨cut, fun y hy => (hWsub hy).1.le⟩
    · exact bddAbove_def.mpr ⟨cut + p, fun y hy => (hWsub hy).2.le⟩
  have hab (j : K) : a (some j) < b (some j) := by
    obtain ⟨y, hy⟩ := openComponent_nonempty j
    rw [hcomponent j] at hy
    exact hy.1.trans hy.2
  have hproper : ∀ j : Option K, b j - a j ≤ p := by
    rintro (_ | j)
    · simp [a, b, (Fact.out : 0 < p).le]
    · have hlow : cut ≤ a (some j) := by
        apply le_csInf (openComponent_nonempty j)
        intro y hy
        exact (hWsub (openComponent_subset j hy)).1.le
      have hupp : b (some j) ≤ cut + p := by
        apply csSup_le (openComponent_nonempty j)
        intro y hy
        exact (hWsub (openComponent_subset j hy)).2.le
      linarith
  have hproper_strict (j : K) : b (some j) - a (some j) < p := by
    refine lt_of_le_of_ne (hproper (some j)) ?_
    intro heq
    have hae : a (some j) = cut := by
      have hlow : cut ≤ a (some j) := by
        apply le_csInf (openComponent_nonempty j)
        intro y hy
        exact (hWsub (openComponent_subset j hy)).1.le
      have hupp : b (some j) ≤ cut + p := by
        apply csSup_le (openComponent_nonempty j)
        intro y hy
        exact (hWsub (openComponent_subset j hy)).2.le
      have : b (some j) - a (some j) = p := heq
      have ha_le : a (some j) ≤ cut := by linarith
      exact le_antisymm ha_le hlow
    have hbe : b (some j) = cut + p := by linarith [heq, hae]
    apply hnotfull
    apply Set.Subset.antisymm hWsub
    have hcompfull : openComponent W j = Ioo cut (cut + p) := by
      rw [hcomponent j, hae, hbe]
    rw [← hcompfull]
    exact openComponent_subset j
  let owner : ι → Option K := fun i =>
    if h : 0 < r i then
      some (Classical.choose (exists_openComponent_superset_Ioo
        (by linarith)
        (show centeredInterval (x i + (shift i : ℝ) * p) (r i) ⊆ W from
          subset_iUnion (fun k => centeredInterval
            (x k + (shift k : ℝ) * p) (r k)) i)))
    else none
  have howner : ∀ i, centeredInterval (x i + (shift i : ℝ) * p) (r i) ⊆
      Ioo (a (owner i)) (b (owner i)) := by
    intro i
    by_cases hi : 0 < r i
    · rw [show owner i = some (Classical.choose
          (exists_openComponent_superset_Ioo
            (by linarith)
            (show centeredInterval (x i + (shift i : ℝ) * p) (r i) ⊆ W from
              subset_iUnion (fun k => centeredInterval
                (x k + (shift k : ℝ) * p) (r k)) i))) by simp [owner, hi]]
      rw [← hcomponent]
      exact Classical.choose_spec (exists_openComponent_superset_Ioo
        (by linarith)
        (show centeredInterval (x i + (shift i : ℝ) * p) (r i) ⊆ W from
          subset_iUnion (fun k => centeredInterval
            (x k + (shift k : ℝ) * p) (r k)) i))
    · have hir : r i = 0 := le_antisymm (le_of_not_gt hi) (hr i)
      simp [owner, hi, hir, centeredInterval]
  have hdisjoint : _root_.Pairwise (fun i j : Option K =>
      Disjoint (quotientInterval p (a i) (b i))
        (quotientInterval p (a j) (b j))) := by
    intro i j hij
    rcases i with _ | i
    · rw [quotientInterval_of_lt (by simp [a, b, Fact.out (p := 0 < p)])]
      simp [a, b]
    rcases j with _ | j
    · change Disjoint (quotientInterval p (a (some i)) (b (some i)))
        (quotientInterval p cut cut)
      rw [quotientInterval_of_lt (p := p) (a := cut) (b := cut)
        (by simpa using (Fact.out : 0 < p))]
      simp
    have hijK : i ≠ j := by
      intro h
      exact hij (by simpa [h])
    have hd : Disjoint (openComponent W i) (openComponent W j) :=
      pairwise_disjoint_openComponent W hijK
    rw [hcomponent i, hcomponent j] at hd
    rw [quotientInterval_of_lt (hproper_strict i),
      quotientInterval_of_lt (hproper_strict j)]
    rw [Set.disjoint_left] at hd ⊢
    rintro q ⟨yi, hyi, rfl⟩ ⟨yj, hyj, heq⟩
    have hyi' : yi ∈ openComponent W i := by rw [hcomponent i]; exact hyi
    have hyj' : yj ∈ openComponent W j := by rw [hcomponent j]; exact hyj
    have hii : yi ∈ Ico cut (cut + p) := Ioo_subset_Ico_self
      (hWsub (openComponent_subset i hyi'))
    have hij' : yj ∈ Ico cut (cut + p) := Ioo_subset_Ico_self
      (hWsub (openComponent_subset j hyj'))
    have hyjieq : yj = yi :=
      (AddCircle.coe_eq_coe_iff_of_mem_Ico hij' hii).mp heq
    subst yj
    exact hd hyi hyj
  have harcproper (i : ι) : (x i + r i) - (x i - r i) < p := by
    rcases (hr i).eq_or_lt with hri | hri
    · simp [← hri, Fact.out (p := 0 < p)]
    · have hend : cut ≤ x i + (shift i : ℝ) * p - r i ∧
          x i + (shift i : ℝ) * p + r i ≤ cut + p :=
        (Ioo_subset_Ioo_iff (by linarith)).mp (hshift i)
      have hle : (x i + r i) - (x i - r i) ≤ p := by linarith
      refine lt_of_le_of_ne hle ?_
      intro heq
      apply hnotfull
      apply Set.Subset.antisymm hWsub
      have he : centeredInterval (x i + (shift i : ℝ) * p) (r i) =
          Ioo cut (cut + p) := by
        ext y
        simp only [centeredInterval, mem_Ioo]
        constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
      rw [← he]
      exact subset_iUnion (fun k => centeredInterval
        (x k + (shift k : ℝ) * p) (r k)) i
  have hcomponents : (⋃ i, quotientCenteredArc p (x i) (r i)) =
      ⋃ j : Option K, quotientInterval p (a j) (b j) := by
    have hbase : (⋃ i, quotientCenteredArc p (x i) (r i)) =
        (fun t : ℝ => (t : AddCircle p)) '' W := by
      rw [show W = ⋃ i, centeredInterval
        (x i + (shift i : ℝ) * p) (r i) from rfl, image_iUnion]
      apply iUnion_congr
      intro i
      calc
        quotientCenteredArc p (x i) (r i) =
            quotientCenteredArc p (x i + (shift i : ℝ) * p) (r i) :=
          (quotientCenteredArc_add_int_mul_period p (x i) (r i) (shift i)).symm
        _ = (fun t : ℝ => (t : AddCircle p)) ''
            centeredInterval (x i + (shift i : ℝ) * p) (r i) := by
          rw [quotientCenteredArc, quotientInterval_of_lt (by
            simpa using harcproper i)]
          rfl
    rw [hbase]
    ext q
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← iUnion_openComponent W] at hy
      rw [mem_iUnion] at hy ⊢
      obtain ⟨j, hj⟩ := hy
      refine ⟨some j, ?_⟩
      rw [quotientInterval_of_lt (hproper_strict j)]
      exact ⟨y, hcomponent j ▸ hj, rfl⟩
    · intro hq
      rw [mem_iUnion] at hq
      obtain ⟨j, hj⟩ := hq
      rcases j with _ | j
      · rw [quotientInterval_of_lt (by simp [a, b, Fact.out (p := 0 < p)])] at hj
        simp [a, b] at hj
      · rw [quotientInterval_of_lt (hproper_strict j)] at hj
        obtain ⟨y, hy, rfl⟩ := hj
        exact ⟨y, openComponent_subset j (by rw [hcomponent j]; exact hy), rfl⟩
  letI : Countable K := countable_openComponentIndex W hWo
  exact volume_iUnion_quotientCenteredDilate_le_of_components_with_shifts
    c p hc x r a b owner shift hr hproper howner hdisjoint hcomponents

/-- Full-circle branch for an arbitrary arc family.  Since every base arc lies
in its dilation, a base union equal to the whole circle forces the dilated union
to be the whole circle as well. -/
theorem volume_iUnion_quotientCenteredDilate_le_of_eq_univ
    {ι : Type*} (c p : ℝ) [Fact (0 < p)] (hc : 1 ≤ c)
    (x r : ι → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hfull : (⋃ i, quotientCenteredArc p (x i) (r i)) = Set.univ) :
    volume (⋃ i, quotientCenteredDilate c p (x i) (r i)) ≤
      ENNReal.ofReal c *
        volume (⋃ i, quotientCenteredArc p (x i) (r i)) := by
  have hcover : (⋃ i, quotientCenteredArc p (x i) (r i)) ⊆
      ⋃ i, quotientCenteredDilate c p (x i) (r i) := by
    intro q hq
    rw [mem_iUnion] at hq ⊢
    obtain ⟨i, hi⟩ := hq
    exact ⟨i, quotientCenteredArc_subset_quotientCenteredDilate hc (hr i) hi⟩
  have hdilated : (⋃ i, quotientCenteredDilate c p (x i) (r i)) = Set.univ :=
    Set.eq_univ_of_univ_subset (hfull ▸ hcover)
  rw [hdilated, hfull, AddCircle.measure_univ]
  calc
    ENNReal.ofReal p = 1 * ENNReal.ofReal p := by simp
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal p :=
      mul_le_mul_right' (by simpa using ENNReal.ofReal_le_ofReal hc) _

/-- Unconditional quotient-circle dilation theorem for an arbitrary family of
centered arcs.  The proof splits the base union into the full circle and a
proper union.  In the proper case an omitted point supplies a common cut; the
only exact-period lift is the punctured-circle case and is handled directly by
its full Haar measure. -/
theorem volume_iUnion_quotientCenteredDilate_le
    {ι : Type*} (c p : ℝ) [Fact (0 < p)] (hc : 1 ≤ c)
    (x r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) :
    volume (⋃ i, quotientCenteredDilate c p (x i) (r i)) ≤
      ENNReal.ofReal c *
        volume (⋃ i, quotientCenteredArc p (x i) (r i)) := by
  let U : Set (AddCircle p) := ⋃ i, quotientCenteredArc p (x i) (r i)
  by_cases hfull : U = Set.univ
  · exact volume_iUnion_quotientCenteredDilate_le_of_eq_univ
      c p hc x r hr hfull
  obtain ⟨q, hq⟩ : ∃ q : AddCircle p, q ∉ U := by
    by_contra h
    push_neg at h
    exact hfull (Set.eq_univ_iff_forall.mpr h)
  obtain ⟨cut, rfl⟩ := QuotientAddGroup.mk_surjective q
  have havoid (i : ι) :
      (cut : AddCircle p) ∉ quotientCenteredArc p (x i) (r i) := by
    intro hi
    exact hq (Set.mem_iUnion_of_mem i hi)
  choose shift hshift using fun i =>
    exists_shift_centeredInterval_subset_Ioo (hr i) (havoid i)
  let W : Set ℝ := ⋃ i,
    centeredInterval (x i + (shift i : ℝ) * p) (r i)
  by_cases hWF : W = Ioo cut (cut + p)
  · have harcproper (i : ι) : (x i + r i) - (x i - r i) < p := by
      by_contra hn
      have hs : p ≤ (x i + r i) - (x i - r i) := le_of_not_gt hn
      apply havoid i
      rw [quotientCenteredArc, quotientInterval_eq_univ_of_le hs]
      exact Set.mem_univ _
    have hbase : (⋃ i, quotientCenteredArc p (x i) (r i)) =
        (fun t : ℝ => (t : AddCircle p)) '' W := by
      rw [show W = ⋃ i, centeredInterval
        (x i + (shift i : ℝ) * p) (r i) from rfl, image_iUnion]
      apply iUnion_congr
      intro i
      calc
        quotientCenteredArc p (x i) (r i) =
            quotientCenteredArc p (x i + (shift i : ℝ) * p) (r i) :=
          (quotientCenteredArc_add_int_mul_period p (x i) (r i) (shift i)).symm
        _ = (fun t : ℝ => (t : AddCircle p)) ''
            centeredInterval (x i + (shift i : ℝ) * p) (r i) := by
          rw [quotientCenteredArc, quotientInterval_of_lt (by
            simpa using harcproper i)]
          rfl
    have hpunctured : (⋃ i, quotientCenteredArc p (x i) (r i)) =
        ({(cut : AddCircle p)} : Set (AddCircle p))ᶜ := by
      rw [hbase, hWF, quotient_image_fundamental_Ioo]
    have hbasevol : volume (⋃ i, quotientCenteredArc p (x i) (r i)) =
        ENNReal.ofReal p := by
      have hsingleton :
          volume ({(cut : AddCircle p)} : Set (AddCircle p)) = 0 := by
        rw [← Metric.closedBall_zero]
        rw [AddCircle.volume_closedBall]
        simp
      rw [hpunctured,
        measure_compl (measurableSet_singleton (cut : AddCircle p))
          (by simp [hsingleton]),
        hsingleton, AddCircle.measure_univ]
      simp
    calc
      volume (⋃ i, quotientCenteredDilate c p (x i) (r i))
          ≤ volume (Set.univ : Set (AddCircle p)) := measure_mono (subset_univ _)
      _ = ENNReal.ofReal p := AddCircle.measure_univ p
      _ = 1 * ENNReal.ofReal p := by simp
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal p :=
        mul_le_mul_right' (by simpa using ENNReal.ofReal_le_ofReal hc) _
      _ = ENNReal.ofReal c *
          volume (⋃ i, quotientCenteredArc p (x i) (r i)) := by rw [hbasevol]
  · exact volume_iUnion_quotientCenteredDilate_le_of_common_cut
      c p cut hc x r hr shift hshift hWF

/-- Arbitrary-family Haar growth for the zero-safe hybrid convention.  The
positive-radius arcs form an open measurable union `U`; the zero-radius centres
are an arbitrary set `Z`.  Carathéodory splitting by `U` charges `Z \ U` only
once.  This includes saturation and requires no positive-radius hypothesis. -/
theorem volume_iUnion_quotientHybridCenteredDilate_le
    {ι : Type*} (c p : ℝ) [Fact (0 < p)] (hc : 1 ≤ c)
    (x r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) :
    volume (⋃ i, quotientHybridCenteredDilate c p (x i) (r i)) ≤
      ENNReal.ofReal c *
        volume (⋃ i, quotientHybridCenteredArc p (x i) (r i)) := by
  let P := {i : ι // 0 < r i}
  let ZI := {i : ι // r i = 0}
  let U : Set (AddCircle p) :=
    ⋃ i : P, quotientCenteredArc p (x i) (r i)
  let V : Set (AddCircle p) :=
    ⋃ i : P, quotientCenteredDilate c p (x i) (r i)
  let Z : Set (AddCircle p) := ⋃ i : ZI, {((x i : ℝ) : AddCircle p)}
  have hUopen : IsOpen U := by
    apply isOpen_iUnion
    intro i
    exact isOpen_quotientInterval _ _ _
  have hUV : U ⊆ V := by
    intro q hq
    change q ∈ ⋃ i : P, quotientCenteredArc p (x i) (r i) at hq
    change q ∈ ⋃ i : P, quotientCenteredDilate c p (x i) (r i)
    rw [Set.mem_iUnion] at hq ⊢
    obtain ⟨i, hi⟩ := hq
    exact ⟨i, quotientCenteredArc_subset_quotientCenteredDilate hc
      (hr i) hi⟩
  have hpositive : volume V ≤ ENNReal.ofReal c * volume U := by
    exact volume_iUnion_quotientCenteredDilate_le c p hc
      (fun i : P => x i) (fun i : P => r i) (fun i => hr i)
  have hbase : (⋃ i, quotientHybridCenteredArc p (x i) (r i)) = U ∪ Z := by
    ext q
    simp only [Set.mem_iUnion, Set.mem_union, U, Z, P, ZI,
      quotientHybridCenteredArc, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi⟩
      by_cases hir : r i = 0
      · exact Or.inr ⟨⟨i, hir⟩, by simpa [hir] using hi⟩
      · have hirpos : 0 < r i := lt_of_le_of_ne (hr i) (Ne.symm hir)
        exact Or.inl ⟨⟨i, hirpos⟩, by simpa [hir] using hi⟩
    · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
      · exact ⟨(i : ι), by simpa [quotientHybridCenteredArc,
          (ne_of_gt i.property)] using hi⟩
      · exact ⟨(i : ι), by simpa [quotientHybridCenteredArc, i.property] using hi⟩
  have hdilate :
      (⋃ i, quotientHybridCenteredDilate c p (x i) (r i)) = V ∪ Z := by
    ext q
    simp only [Set.mem_iUnion, Set.mem_union, V, Z, P, ZI,
      quotientHybridCenteredDilate, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi⟩
      by_cases hir : r i = 0
      · exact Or.inr ⟨⟨i, hir⟩, by simpa [hir] using hi⟩
      · have hirpos : 0 < r i := lt_of_le_of_ne (hr i) (Ne.symm hir)
        exact Or.inl ⟨⟨i, hirpos⟩, by simpa [hir] using hi⟩
    · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
      · exact ⟨(i : ι), by simpa [quotientHybridCenteredDilate,
          (ne_of_gt i.property)] using hi⟩
      · exact ⟨(i : ι), by simpa [quotientHybridCenteredDilate, i.property] using hi⟩
  have hZU : U ∪ Z = (Z \ U) ∪ U := by
    ext q
    constructor
    · rintro (hq | hq)
      · exact Or.inr hq
      · by_cases hqU : q ∈ U
        · exact Or.inr hqU
        · exact Or.inl ⟨hq, hqU⟩
    · rintro (hq | hq)
      · exact Or.inr hq.1
      · exact Or.inl hq
  have hsplit : volume (U ∪ Z) = volume U + volume (Z \ U) := by
    rw [hZU, measure_union]
    · exact add_comm _ _
    · exact Set.disjoint_left.2 (fun _ hzU hU => hzU.2 hU)
    · exact hUopen.measurableSet
  rw [hdilate, hbase]
  calc
    volume (V ∪ Z) ≤ volume (V ∪ (Z \ U)) := by
      apply measure_mono
      rintro q (hqV | hqZ)
      · exact Or.inl hqV
      · by_cases hqU : q ∈ U
        · exact Or.inl (hUV hqU)
        · exact Or.inr ⟨hqZ, hqU⟩
    _ ≤ volume V + volume (Z \ U) := measure_union_le _ _
    _ ≤ ENNReal.ofReal c * volume U +
        ENNReal.ofReal c * volume (Z \ U) := by
      apply add_le_add hpositive
      calc
        volume (Z \ U) = 1 * volume (Z \ U) := by simp
        _ ≤ ENNReal.ofReal c * volume (Z \ U) := by
          apply mul_le_mul_right'
          simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hc
    _ = ENNReal.ofReal c * volume (U ∪ Z) := by
      rw [hsplit, mul_add]

end

end StarKakeyaLower
