import StarKakeyaLower.OneTenthSourcesGeometry

/-! # Borel direction partition and the actual physical-lift adapter -/
open Set MeasureTheory
namespace StarKakeyaLower.OneTenth.Sources
noncomputable section

/-- Low directions, in the chart actually accepted by CircleLifts. -/
def L (o : Plane) (c : ℝ → Plane) : Set ℝ := chart ∩ {q | M o c q < 99/100}
/-- Endpoint eligibility, not nearest-point eligibility. -/
def B (o : Plane) (c : ℝ → Plane) : Set ℝ := {q | 2/5 ≤ N o c q}
def U (o : Plane) (c : ℝ → Plane) : Set ℝ := L o c \ B o c
def F (o : Plane) (c : ℝ → Plane) : Set ℝ :=
  chart ∩ {q | 99/100 ≤ M o c q ∧ M o c q < 8/5}
def dyadicScale (n : ℕ) : ℝ := (8/5) * 2^n
def D (o : Plane) (c : ℝ → Plane) (n : ℕ) : Set ℝ :=
  chart ∩ {q | dyadicScale n ≤ M o c q ∧ M o c q < 2*dyadicScale n}

theorem measurableSet_L (o : Plane) {c : ℝ → Plane} (hc : Measurable c) : MeasurableSet (L o c) :=
  measurableSet_Ioc.inter (measurableSet_lt (measurable_M o hc) measurable_const)
theorem measurableSet_B (o : Plane) {c : ℝ → Plane} (hc : Measurable c) : MeasurableSet (B o c) :=
  measurableSet_le measurable_const (measurable_N o hc)
theorem measurableSet_U (o : Plane) {c : ℝ → Plane} (hc : Measurable c) : MeasurableSet (U o c) :=
  (measurableSet_L o hc).diff (measurableSet_B o hc)
theorem measurableSet_F (o : Plane) {c : ℝ → Plane} (hc : Measurable c) : MeasurableSet (F o c) :=
  measurableSet_Ioc.inter ((measurableSet_le measurable_const (measurable_M o hc)).inter
    (measurableSet_lt (measurable_M o hc) measurable_const))
theorem measurableSet_D (o : Plane) {c : ℝ → Plane} (hc : Measurable c) (n : ℕ) :
    MeasurableSet (D o c n) :=
  measurableSet_Ioc.inter ((measurableSet_le measurable_const (measurable_M o hc)).inter
    (measurableSet_lt (measurable_M o hc) measurable_const))

theorem low_split (o : Plane) (c : ℝ → Plane) :
    Disjoint (L o c ∩ B o c) (U o c) ∧ (L o c ∩ B o c) ∪ U o c = L o c := by
  constructor
  · rw [Set.disjoint_left]
    intro q hq hu
    exact hu.2 hq.2
  · ext q
    simp only [U, mem_union, mem_inter_iff, mem_diff]
    tauto

theorem U_far_radius_gt (o : Plane) (c : ℝ → Plane) {q : ℝ} (hq : q ∈ U o c) :
    (3/5 : ℝ) < M o c q := by
  have hn : N o c q < 2/5 := lt_of_not_ge hq.2
  have h := one_le_M_add_N o c q
  linarith

theorem low_x_bounds (o : Plane) (c : ℝ → Plane) {q : ℝ} (hq : q ∈ L o c) :
    (1/2 : ℝ) ≤ x o c q ∧ x o c q < 99/100 ∧ 0 < 1-x o c q := by
  have hx := x_le_M o c q
  have hxpos : (1/2 : ℝ) ≤ x o c q := by unfold x; linarith [abs_nonneg (longitudinal o c q)]
  refine ⟨hxpos, lt_of_le_of_lt hx hq.2, ?_⟩
  have hM : M o c q < 99/100 := hq.2
  linarith

@[simp] theorem dyadicScale_zero : dyadicScale 0 = 8/5 := by norm_num [dyadicScale]
@[simp] theorem dyadicScale_succ (n : ℕ) : dyadicScale (n+1) = 2*dyadicScale n := by
  simp [dyadicScale, pow_succ]; ring

theorem dyadicScale_mono : Monotone dyadicScale := by
  intro n m h
  unfold dyadicScale
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) h) (by norm_num)

theorem dyadicScale_lower (n : ℕ) : (8/5 : ℝ) ≤ dyadicScale n := by
  simpa using dyadicScale_mono (Nat.zero_le n)

theorem exists_dyadic_interval {r : ℝ} (hr : 8/5 ≤ r) :
    ∃ n : ℕ, dyadicScale n ≤ r ∧ r < 2*dyadicScale n := by
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near (x := r/(8/5)) (y := (2 : ℝ))
    (by linarith) (by norm_num)
  refine ⟨n,?_,?_⟩
  · dsimp [dyadicScale]
    linarith
  · rw [pow_succ] at hn'
    dsimp [dyadicScale]
    linarith

theorem disjoint_L_F (o : Plane) (c : ℝ → Plane) : Disjoint (L o c) (F o c) := by
  rw [Set.disjoint_left]
  intro q hq hq'
  exact not_lt_of_ge hq'.2.1 hq.2

theorem disjoint_L_D (o : Plane) (c : ℝ → Plane) (n : ℕ) : Disjoint (L o c) (D o c n) := by
  rw [Set.disjoint_left]
  intro q hq hq'
  have h := dyadicScale_lower n
  have ha : M o c q < 99/100 := hq.2
  have hb := hq'.2.1
  linarith

theorem disjoint_F_D (o : Plane) (c : ℝ → Plane) (n : ℕ) : Disjoint (F o c) (D o c n) := by
  rw [Set.disjoint_left]
  intro q hq hq'
  exact not_lt_of_ge ((dyadicScale_lower n).trans hq'.2.1) hq.2.2

theorem pairwise_disjoint_D (o : Plane) (c : ℝ → Plane) : Pairwise (fun n m => Disjoint (D o c n) (D o c m)) := by
  intro n m hnm
  rw [Set.disjoint_left]
  intro q hq hq'
  rcases lt_or_gt_of_ne hnm with h | h
  · have hs := dyadicScale_mono (Nat.succ_le_iff.mpr h)
    rw [dyadicScale_succ] at hs
    exact not_lt_of_ge (hs.trans hq'.2.1) hq.2.2
  · have hs := dyadicScale_mono (Nat.succ_le_iff.mpr h)
    rw [dyadicScale_succ] at hs
    exact not_lt_of_ge (hs.trans hq.2.1) hq'.2.2

theorem direction_partition (o : Plane) (c : ℝ → Plane) :
    L o c ∪ F o c ∪ (⋃ n : ℕ, D o c n) = chart := by
  ext q
  constructor
  · rintro ((h|h)|h)
    · exact h.1
    · exact h.1
    · obtain ⟨n,hn⟩ := mem_iUnion.mp h
      exact hn.1
  · intro hq
    by_cases hL : M o c q < 99/100
    · exact Or.inl (Or.inl ⟨hq,hL⟩)
    · by_cases hF : M o c q < 8/5
      · exact Or.inl (Or.inr ⟨hq,le_of_not_gt hL,hF⟩)
      · obtain ⟨n,hn⟩ := exists_dyadic_interval (le_of_not_gt hF)
        exact Or.inr (mem_iUnion.mpr ⟨n,hq,hn⟩)

/-- Every projective direction, including the cut direction, is covered. -/
theorem chart_full_directions :
    (fun q : ℝ => (q : Direction)) '' chart = univ := by
  apply eq_univ_of_forall
  intro d
  let t := AddCircle.equivIoc Real.pi 0 d
  refine ⟨t,?_,?_⟩
  · simpa [chart] using t.property
  · exact (AddCircle.equivIoc Real.pi 0).symm_apply_apply d

theorem partition_full_directions (o : Plane) (c : ℝ → Plane) :
    (fun q : ℝ => (q : Direction)) '' (L o c ∪ F o c ∪ ⋃ n : ℕ, D o c n) = univ := by
  rw [direction_partition, chart_full_directions]

/-- Finite recovery makes all sufficiently high dyadic source classes empty.
The finite cutoff depends on the recovered family, not on a cap hypothesis. -/
theorem finite_dyadic_support (o : Plane) (c : ℝ → Plane) (hc : (range c).Finite) :
    ∃ J : ℕ, ∀ n, J ≤ n → D o c n = ∅ := by
  obtain ⟨R,hR⟩ := finite_midpoints_radius_bound o c hc
  obtain ⟨J,hJ⟩ := pow_unbounded_of_one_lt (R/(8/5)) (by norm_num : (1 : ℝ) < 2)
  have hJR : R < dyadicScale J := by unfold dyadicScale; linarith
  refine ⟨J, fun n hn => ?_⟩
  apply eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hh := dyadicScale_mono hn
  have hm := hq.2.1
  have hb := hR q
  linarith

/-- All source hypotheses of the existing genuine two-physical-lift theorem
are now discharged by the Borel midpoint, not carried as extra assumptions. -/
theorem actual_eligible_lift_length (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hchart : V ⊆ chart) :
    volume.toOuterMeasure (chosenLift V (A o c) ∪ oppositeLift (V ∩ B o c) (A o c)) =
      volume ((fun q : ℝ => (q : ProjectiveDirection)) '' V) +
      volume ((fun q : ℝ => (q : ProjectiveDirection)) '' (V ∩ B o c)) :=
  eligible_lift_length hV (hV.inter (measurableSet_B o hc)) (measurableSet_A o hc)
    hchart inter_subset_left

theorem actual_eligible_lifts_disjoint (o : Plane) (c : ℝ → Plane)
    {V : Set ℝ} (hchart : V ⊆ chart) :
    Disjoint (chosenLift V (A o c)) (oppositeLift (V ∩ B o c) (A o c)) :=
  chosen_opposite_disjoint hchart (inter_subset_left.trans hchart)

/-- A finite direction partition, suitable for finite-sum bank assembly. -/
theorem finite_direction_partition (o : Plane) (c : ℝ → Plane) (hc : (range c).Finite) :
    ∃ J : ℕ, L o c ∪ F o c ∪ (⋃ n : Fin J, D o c n) = chart := by
  obtain ⟨J,hJ⟩ := finite_dyadic_support o c hc
  refine ⟨J, ?_⟩
  have he : (⋃ n : ℕ, D o c n) = ⋃ n : Fin J, D o c n := by
    ext q
    simp only [mem_iUnion]
    constructor
    · rintro ⟨n,hn⟩
      by_cases hlt : n < J
      · exact ⟨⟨n,hlt⟩,hn⟩
      · rw [hJ n (le_of_not_gt hlt)] at hn
        exact hn.elim
    · rintro ⟨n,hn⟩
      exact ⟨n,hn⟩
  rw [← he, direction_partition]

/-- Source direction of a far/eligible-near label. -/
def labelDirection (V : Set ℝ) (o : Plane) (c : ℝ → Plane) :
    EligibleLabel V (V ∩ B o c) → ℝ := Sum.elim (fun q => q) (fun q => q)

theorem labelDirection_mem (V : Set ℝ) (o : Plane) (c : ℝ → Plane)
    (i : EligibleLabel V (V ∩ B o c)) : labelDirection V o c i ∈ V := by
  cases i with
  | inl q => exact q.property
  | inr q => exact q.property.1

/-- Geometry-facing adapter to the existing CircleReceipt. The outstanding
inputs are actual support-triangle membership and the real interval extension
bounds. Source Borelness, near eligibility and physical lift choice are proved
here; there is no assumed geometric or area inequality. -/
theorem actual_support_section_receipt (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hchart : V ⊆ chart)
    (G : Set Plane) (hG : ∀ q ∈ V, triangle o c q ⊆ G)
    (r ρ : ℝ) (hρ : 0 ≤ ρ) (a b : EligibleLabel V (V ∩ B o c) → ℝ)
    (hab : ∀ i, a i ≤ b i)
    (hleft : ∀ i, a i-ρ*(b i-a i) ≤ eligibleAngle V (V ∩ B o c) (A o c) i)
    (hright : ∀ i, eligibleAngle V (V ∩ B o c) (A o c) i ≤ b i+ρ*(b i-a i))
    (hpoints : ∀ i θ, θ ∈ Icc (a i) (b i) →
      polarPoint r θ ∈ supportNeedleTriangle
        (farAngle o c (labelDirection V o c i))
        (farHeight o c (labelDirection V o c i))
        (x o c (labelDirection V o c i)-1/2)) :
    volume ((fun q : ℝ => (q : ProjectiveDirection)) '' V) +
      volume ((fun q : ℝ => (q : ProjectiveDirection)) '' (V ∩ B o c)) ≤
    ENNReal.ofReal (1+2*ρ) *
      volume.toOuterMeasure (physicalSection (sourcePlane o ⁻¹' G) r) := by
  apply eligible_physical_section_receipt hV (hV.inter (measurableSet_B o hc))
    (measurableSet_A o hc) hchart inter_subset_left ρ hρ a b hab hleft hright
  intro i θ hθ
  apply hG (labelDirection V o c i) (labelDirection_mem V o c i)
  rw [triangle_eq_support_image]
  exact ⟨polarPoint r θ, hpoints i θ hθ, rfl⟩

end
end StarKakeyaLower.OneTenth.Sources
