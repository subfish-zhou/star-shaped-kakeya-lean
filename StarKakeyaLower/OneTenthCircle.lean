import StarKakeyaLower.LiGeometry

/-!
# Closed physical-circle union dilation

This supplies the closed-interval version of the circle lemma in the one-tenth
proof. The only covering estimate used is the already proved arbitrary-family
`volume_iUnion_quotientCenteredDilate_le`. Closed arcs, including an arbitrary
union of singleton arcs, are passed to it through open supersets. There is no
measurability assumption on the index family or its union.
-/

open Set MeasureTheory

namespace StarKakeyaLower.OneTenth
noncomputable section

/-- The saturated closed convention is exactly the actual quotient image,
including an interval of length exactly one period. -/
theorem closedInterval_eq_image (p a b : ℝ) [Fact (0 < p)] :
    quotientClosedInterval p a b = (fun t : ℝ => (t : AddCircle p)) '' Icc a b := by
  by_cases h : p ≤ b - a
  · rw [quotientClosedInterval, if_pos h]
    apply Set.Subset.antisymm
    · rw [← AddCircle.coe_image_Icc_eq p a]
      exact image_mono (Icc_subset_Icc le_rfl (by linarith))
    · exact subset_univ _
  · simp [quotientClosedInterval, h]

@[simp] theorem closedArc_zero (p x : ℝ) [Fact (0 < p)] :
    quotientClosedCenteredArc p x 0 = {(x : AddCircle p)} := by
  simp [quotientClosedCenteredArc, closedInterval_eq_image]

/-- A closed arc in a proper open set has a strictly larger, unsaturated open
arc in that same set. The zero-radius case is included, not discarded. -/
theorem exists_open_arc_enlargement {p x r : ℝ} [Fact (0 < p)]
    (hr : 0 ≤ r) {O : Set (AddCircle p)} (hO : IsOpen O) (hproper : O ≠ univ)
    (hsub : quotientClosedCenteredArc p x r ⊆ O) :
    ∃ s : ℝ, r < s ∧ quotientCenteredArc p x s ⊆ O := by
  have hspan : 2 * r < p := by
    by_contra hn
    have hs : quotientClosedCenteredArc p x r = univ := by
      have hp : p ≤ (x + r) - (x - r) := by linarith
      exact if_pos hp
    exact hproper (Set.eq_univ_of_univ_subset (hs ▸ hsub))
  let U : Set ℝ := (fun t : ℝ => (t : AddCircle p)) ⁻¹' O
  have hU : IsOpen U := hO.preimage (AddCircle.continuous_mk' p)
  have hI : Icc (x-r) (x+r) ⊆ U := by
    intro t ht
    apply hsub
    rw [quotientClosedCenteredArc, closedInterval_eq_image]
    exact ⟨t, ht, rfl⟩
  obtain ⟨e, he, hleft⟩ := Metric.isOpen_iff.mp hU (x-r) (hI ⟨le_rfl, by linarith⟩)
  obtain ⟨f, hf, hright⟩ := Metric.isOpen_iff.mp hU (x+r) (hI ⟨by linarith, le_rfl⟩)
  let d := min (min e f) ((p-2*r)/4)
  have hd : 0 < d := lt_min (lt_min he hf) (by linarith)
  have hde : d ≤ e := (min_le_left _ _).trans (min_le_left _ _)
  have hdf : d ≤ f := (min_le_left _ _).trans (min_le_right _ _)
  have hdp : d ≤ (p-2*r)/4 := min_le_right _ _
  refine ⟨r+d, by linarith, ?_⟩
  rw [quotientCenteredArc, quotientInterval_of_lt (by linarith :
    (x+(r+d))-(x-(r+d)) < p)]
  rintro _ ⟨t, ht, rfl⟩
  change t ∈ U
  by_cases hta : t < x-r
  · apply hleft
    rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith : t-(x-r) < 0)]
    linarith [ht.1]
  · by_cases htb : x+r < t
    · apply hright
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith : 0 < t-(x+r))]
      linarith [ht.2]
    · exact hI ⟨le_of_not_gt hta, le_of_not_gt htb⟩

/-- Strictly larger open radii contain the entire closed dilation, endpoints
included. Saturation is handled in the quotient, not by a chosen chart. -/
theorem closedDilate_subset_openDilate {c p x r s : ℝ} [Fact (0 < p)]
    (hc : 0 < c) (hrs : r < s) :
    quotientClosedCenteredDilate c p x r ⊆ quotientCenteredDilate c p x s := by
  rw [quotientClosedCenteredDilate, closedInterval_eq_image]
  by_cases hs : p ≤ (x+c*s)-(x-c*s)
  · rw [quotientCenteredDilate, quotientInterval_eq_univ_of_le hs]
    exact subset_univ _
  · rw [quotientCenteredDilate, quotientInterval_of_lt (lt_of_not_ge hs)]
    apply image_mono
    intro t ht
    have hmul := mul_lt_mul_of_pos_left hrs hc
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- Unconditional closed-arc union dilation for arbitrary positive period.
Measure evaluation is its outer measure; no union measurability is assumed. -/
theorem outer_iUnion_closedDilate_le {ι : Type*} (c p : ℝ) [Fact (0 < p)]
    (hc : 1 ≤ c) (x r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) :
    volume.toOuterMeasure (⋃ i, quotientClosedCenteredDilate c p (x i) (r i)) ≤
      ENNReal.ofReal c *
        volume.toOuterMeasure (⋃ i, quotientClosedCenteredArc p (x i) (r i)) := by
  simp only [Measure.toOuterMeasure_apply]
  rw [Set.measure_eq_iInf_isOpen (⋃ i, quotientClosedCenteredArc p (x i) (r i)) volume]
  have hc0 : 0 < c := by linarith
  simp only [ENNReal.mul_iInf_of_ne (ne_of_gt (ENNReal.ofReal_pos.mpr hc0))
    ENNReal.ofReal_ne_top]
  apply le_iInf
  intro O
  apply le_iInf
  intro hsub
  apply le_iInf
  intro hO
  by_cases hfull : O = univ
  · rw [hfull]
    exact (measure_mono (subset_univ _)).trans
      (le_mul_of_one_le_left' (by simpa using ENNReal.ofReal_le_ofReal hc))
  · have hex (i : ι) := exists_open_arc_enlargement (hr i) hO hfull
      ((subset_iUnion (fun j => quotientClosedCenteredArc p (x j) (r j)) i).trans hsub)
    choose s hs hsin using hex
    calc
      volume (⋃ i, quotientClosedCenteredDilate c p (x i) (r i)) ≤
          volume (⋃ i, quotientCenteredDilate c p (x i) (s i)) :=
        measure_mono (iUnion_mono fun i => closedDilate_subset_openDilate hc0 (hs i))
      _ ≤ ENNReal.ofReal c * volume (⋃ i, quotientCenteredArc p (x i) (s i)) :=
        volume_iUnion_quotientCenteredDilate_le c p hc x s (fun i => (hr i).trans (hs i).le)
      _ ≤ ENNReal.ofReal c * volume O :=
        mul_le_mul_left' (measure_mono (iUnion_subset hsin)) _

/-- The physical circle has length `2π`, not `π`. -/
theorem physicalCircle_length :
    volume (univ : Set PolarAngle) = ENNReal.ofReal (2 * Real.pi) :=
  AddCircle.measure_univ _

/-- Ordinary full-circle version, retaining the zero-radius singleton union. -/
theorem physical_outer_iUnion_closedDilate_le {ι : Type*}
    (c : ℝ) (hc : 1 ≤ c) (x r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) :
    volume.toOuterMeasure (⋃ i, quotientClosedCenteredDilate c (2*Real.pi) (x i) (r i)) ≤
      ENNReal.ofReal c * volume.toOuterMeasure
        (⋃ i, quotientClosedCenteredArc (2*Real.pi) (x i) (r i)) :=
  outer_iUnion_closedDilate_le c (2*Real.pi) hc x r hr

/-- An interval with each endpoint moved outwards by at most `ρ` times its
original length lies in the centered `(1+2ρ)` dilation. Thus either one-sided
extension is covered, even when different labels choose opposite sides. -/
theorem extendedInterval_subset_closedDilate {p ρ a b a' b' : ℝ} [Fact (0 < p)]
    (hleft : a - ρ*(b-a) ≤ a') (hright : b' ≤ b + ρ*(b-a)) :
    quotientClosedInterval p a' b' ⊆
      quotientClosedCenteredDilate (1+2*ρ) p ((a+b)/2) ((b-a)/2) := by
  rw [closedInterval_eq_image p a' b',
    quotientClosedCenteredDilate, closedInterval_eq_image]
  apply image_mono
  apply Icc_subset_Icc <;> nlinarith

/-- One union, one growth factor. Closed endpoints, repeats, opposite extension
sides and arbitrary (possibly nonmeasurable) singleton unions are all allowed. -/
theorem physical_outer_iUnion_extension_le {ι : Type*}
    (ρ : ℝ) (hρ : 0 ≤ ρ) (a b a' b' : ι → ℝ)
    (hab : ∀ i, a i ≤ b i)
    (hleft : ∀ i, a i - ρ*(b i-a i) ≤ a' i)
    (hright : ∀ i, b' i ≤ b i + ρ*(b i-a i)) :
    volume.toOuterMeasure (⋃ i, polarArc (a' i) (b' i)) ≤
      ENNReal.ofReal (1+2*ρ) * volume.toOuterMeasure (⋃ i, polarArc (a i) (b i)) := by
  have h := physical_outer_iUnion_closedDilate_le (1+2*ρ) (by linarith)
    (fun i => (a i+b i)/2) (fun i => (b i-a i)/2) (fun i => by linarith [hab i])
  have hbase : (⋃ i, quotientClosedCenteredArc (2*Real.pi) ((a i+b i)/2) ((b i-a i)/2)) =
      ⋃ i, polarArc (a i) (b i) := by
    apply iUnion_congr
    intro i
    unfold quotientClosedCenteredArc polarArc
    congr 1 <;> ring
  rw [hbase] at h
  apply le_trans (measure_mono (iUnion_mono fun i =>
    extendedInterval_subset_closedDilate (hleft i) (hright i))) h

/-- One-sided anchor receipt, before constructing the triangle-specific lobes.
Its premises are literal real endpoint inequalities and physical set inclusion,
not an assumed measure or area estimate. -/
theorem physical_anchor_receipt {ι : Type*}
    (ρ : ℝ) (hρ : 0 ≤ ρ) (a b t : ι → ℝ) (S : Set PolarAngle)
    (hab : ∀ i, a i ≤ b i)
    (htleft : ∀ i, a i - ρ*(b i-a i) ≤ t i)
    (htright : ∀ i, t i ≤ b i + ρ*(b i-a i))
    (hbase : ∀ i, polarArc (a i) (b i) ⊆ S) :
    volume.toOuterMeasure (Set.range (fun i => (t i : PolarAngle))) ≤
      ENNReal.ofReal (1+2*ρ) * volume.toOuterMeasure S := by
  have h := physical_outer_iUnion_extension_le ρ hρ a b t t hab htleft htright
  have heq : (⋃ i, polarArc (t i) (t i)) = Set.range (fun i => (t i : PolarAngle)) := by
    simp [polarArc, closedInterval_eq_image, iUnion_singleton_eq_range]
  rw [heq] at h
  exact h.trans (mul_le_mul_left' (measure_mono (iUnion_subset hbase)) _)

#print axioms outer_iUnion_closedDilate_le
#print axioms physical_outer_iUnion_extension_le
#print axioms physical_anchor_receipt

end
end StarKakeyaLower.OneTenth
