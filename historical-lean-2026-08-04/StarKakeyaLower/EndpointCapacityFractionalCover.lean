import StarKakeyaLower.CaseIIGeometry

/-!
# Finite fractional-cover foundations

The endpoint-capacity schedule uses finite simple payments on arbitrary,
possibly nonmeasurable direction classes.  The first input is strong
submodularity of the outer evaluation induced by a genuine measure.

This module proves the application-level finite fractional-cover lemma used by
the 32-class schedule: arbitrary nonmeasurable pairwise-disjoint atoms and
finite weighted unions of those atoms.  A wrapper for completely arbitrary
finite sets `B_i` would require Boolean atomisation and is not claimed here.
No continuum Fubini argument is used.
-/

open Set MeasureTheory
open scoped ENNReal

namespace StarKakeyaLower

noncomputable section

/-- The outer evaluation attached to any measure is strongly submodular on
arbitrary sets.  No measurability or finiteness hypothesis is required. -/
theorem measure_apply_union_add_inter_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (A B : Set α) :
    μ (A ∪ B) + μ (A ∩ B) ≤ μ A + μ B := by
  let HA := toMeasurable μ A
  let HB := toMeasurable μ B
  calc
    μ (A ∪ B) + μ (A ∩ B)
        ≤ μ (HA ∪ HB) + μ (HA ∩ HB) :=
      add_le_add
        (measure_mono (union_subset_union (subset_toMeasurable μ A)
          (subset_toMeasurable μ B)))
        (measure_mono (inter_subset_inter (subset_toMeasurable μ A)
          (subset_toMeasurable μ B)))
    _ = μ HA + μ HB :=
      measure_union_add_inter HA (measurableSet_toMeasurable μ B)
    _ = μ A + μ B := by
      simp [HA, HB, measure_toMeasurable]

/-- The projective angular outer measure used by the Kakeya development inherits
strong submodularity from its proved identification with Haar outer measure. -/
theorem directionAngleOuter_union_add_inter_le (A B : Set Direction) :
    directionAngleOuter (A ∪ B) + directionAngleOuter (A ∩ B) ≤
      directionAngleOuter A + directionAngleOuter B := by
  simp_rw [← directionOuterMeasure_eq_directionAngleOuter]
  exact measure_apply_union_add_inter_le volume A B

/-- Diminishing returns for finite outer-measure marginals. -/
private theorem measure_marginal_antitone
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (X Y A : Set α) (hXY : X ⊆ Y) (hdisj : Disjoint A Y)
    (hfin : μ Set.univ ≠ ∞) :
    (μ (Y ∪ A)).toReal - (μ Y).toReal ≤
      (μ (X ∪ A)).toReal - (μ X).toReal := by
  have hi : Y ∩ (X ∪ A) = X := by
    ext x
    constructor
    · rintro ⟨hxY, hxX | hxA⟩
      · exact hxX
      · exact False.elim (Set.disjoint_left.1 hdisj hxA hxY)
    · intro hx
      exact ⟨hXY hx, Or.inl hx⟩
  have hu : Y ∪ (X ∪ A) = Y ∪ A := by
    ext x
    simp only [mem_union]
    tauto
  have hsub := measure_apply_union_add_inter_le μ Y (X ∪ A)
  rw [hi, hu] at hsub
  have hne (E : Set α) : μ E ≠ ∞ :=
    ne_top_of_le_ne_top hfin (measure_mono (subset_univ E))
  have hr := ENNReal.toReal_le_toReal
    (by simp [hne]) (by simp [hne]) |>.2 hsub
  rw [ENNReal.toReal_add (hne (Y ∪ A)) (hne X),
      ENNReal.toReal_add (hne Y) (hne (X ∪ A))] at hr
  linarith

/-- A class union receives at least the sum of the common greedy marginals of
its atoms. -/
private theorem measure_class_ge_sum_marginals
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (A : ℕ → Set α) (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range n)
    (hdisj : (Finset.range n : Set ℕ).PairwiseDisjoint A)
    (hfin : μ Set.univ ≠ ∞) :
    ∑ j ∈ S, ((μ (⋃ k ∈ Finset.range (j + 1), A k)).toReal -
      (μ (⋃ k ∈ Finset.range j, A k)).toReal) ≤
      (μ (⋃ j ∈ S, A j)).toReal := by
  let F : Finset ℕ → Set α := fun T => ⋃ j ∈ T, A j
  let delta : ℕ → ℝ := fun j => (μ (F (Finset.range (j + 1)))).toReal -
    (μ (F (Finset.range j))).toReal
  have hstep : ∀ k < n,
      delta k ≤ (μ (F (insert k (S ∩ Finset.range k)))).toReal -
        (μ (F (S ∩ Finset.range k))).toReal := by
    intro k hk
    have hsub : F (S ∩ Finset.range k) ⊆ F (Finset.range k) := by
      intro x hx
      simp only [F, mem_iUnion] at hx ⊢
      obtain ⟨j, hj, hxA⟩ := hx
      exact ⟨j, (Finset.mem_inter.1 hj).2, hxA⟩
    have hd : Disjoint (A k) (F (Finset.range k)) := by
      apply Set.disjoint_left.2
      intro x hxA hxU
      simp only [F, mem_iUnion] at hxU
      obtain ⟨j, hj, hxj⟩ := hxU
      have hjlt : j < k := Finset.mem_range.1 hj
      have hak : k ∈ (Finset.range n : Set ℕ) := Finset.mem_range.2 hk
      have haj : j ∈ (Finset.range n : Set ℕ) :=
        Finset.mem_range.2 (lt_trans hjlt hk)
      exact Set.disjoint_left.1 (hdisj hak haj (ne_of_gt hjlt)) hxA hxj
    have hm := measure_marginal_antitone μ
      (F (S ∩ Finset.range k)) (F (Finset.range k)) (A k) hsub hd hfin
    have hrange : F (Finset.range (k + 1)) = F (Finset.range k) ∪ A k := by
      ext x
      simp only [F, mem_iUnion, Finset.mem_range, mem_union]
      constructor
      · rintro ⟨j, hj, hx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact Or.inl ⟨j, hj, hx⟩
        · exact Or.inr hx
      · rintro (⟨j, hj, hx⟩ | hx)
        · exact ⟨j, Nat.lt_succ_of_lt hj, hx⟩
        · exact ⟨k, Nat.lt_succ_self k, hx⟩
    have hinsert : F (insert k (S ∩ Finset.range k)) =
        F (S ∩ Finset.range k) ∪ A k := by
      ext x
      simp only [F, mem_iUnion, Finset.mem_insert, mem_union]
      constructor
      · rintro ⟨j, (rfl | hj), hx⟩
        · exact Or.inr hx
        · exact Or.inl ⟨j, hj, hx⟩
      · rintro (⟨j, hj, hx⟩ | hx)
        · exact ⟨j, Or.inr hj, hx⟩
        · exact ⟨k, Or.inl rfl, hx⟩
    dsimp [delta]
    rw [hrange, hinsert]
    simpa [union_comm] using hm
  have hind : ∀ k ≤ n,
      ∑ j ∈ S ∩ Finset.range k, delta j ≤
        (μ (F (S ∩ Finset.range k))).toReal := by
    intro k hk
    induction k with
    | zero => simp [F]
    | succ k ih =>
      have hkn : k < n := Nat.lt_of_succ_le hk
      have hi := ih (Nat.le_trans (Nat.le_succ k) hk)
      by_cases hmem : k ∈ S
      · have hinter : S ∩ Finset.range (k + 1) =
            insert k (S ∩ Finset.range k) := by
          ext j
          constructor
          · intro hj
            have hjS := (Finset.mem_inter.1 hj).1
            have hjlt := Finset.mem_range.1 (Finset.mem_inter.1 hj).2
            rcases Nat.lt_succ_iff_lt_or_eq.1 hjlt with hjlt | heq
            · exact Finset.mem_insert.2 (Or.inr (Finset.mem_inter.2
                ⟨hjS, Finset.mem_range.2 hjlt⟩))
            · subst j
              exact Finset.mem_insert_self k _
          · intro hj
            rcases Finset.mem_insert.1 hj with heq | hj
            · subst j
              exact Finset.mem_inter.2
                ⟨hmem, Finset.mem_range.2 (Nat.lt_succ_self k)⟩
            · exact Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hj).1,
                Finset.mem_range.2 (Nat.lt_succ_of_lt
                  (Finset.mem_range.1 (Finset.mem_inter.1 hj).2))⟩
        have hknot : k ∉ S ∩ Finset.range k := by simp
        rw [hinter, Finset.sum_insert hknot]
        have hs := hstep k hkn
        linarith
      · have hinter : S ∩ Finset.range (k + 1) = S ∩ Finset.range k := by
          ext j
          constructor
          · intro hj
            have hjS := (Finset.mem_inter.1 hj).1
            have hjlt := Finset.mem_range.1 (Finset.mem_inter.1 hj).2
            rcases Nat.lt_succ_iff_lt_or_eq.1 hjlt with hjlt | rfl
            · exact Finset.mem_inter.2 ⟨hjS, Finset.mem_range.2 hjlt⟩
            · exact False.elim (hmem hjS)
          · intro hj
            exact Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hj).1,
              Finset.mem_range.2 (Nat.lt_succ_of_lt
                (Finset.mem_range.1 (Finset.mem_inter.1 hj).2))⟩
        simpa [hinter] using hi
  have hn := hind n (le_refl n)
  have hinter : S ∩ Finset.range n = S := Finset.inter_eq_left.2 hS
  simpa [F, delta, hinter] using hn

/-- **Finite fractional cover for arbitrary disjoint atoms.**

The atom sets and all class unions may be nonmeasurable.  If every atom label
receives weight at least `c`, then the weighted outer measures of the class
unions dominate `c` times the outer measure of the full atom union.

This is the application-level finite Lemma F needed by the endpoint-capacity
schedule. -/
theorem measure_biUnion_atoms_le_weighted_classes
    {α κ : Type*} [MeasurableSpace α]
    (μ : Measure α) (A : ℕ → Set α) (n : ℕ)
    (I : Finset κ) (S : κ → Finset ℕ) (d : κ → NNReal) (c : NNReal)
    (hS : ∀ i ∈ I, S i ⊆ Finset.range n)
    (hdisj : (Finset.range n : Set ℕ).PairwiseDisjoint A)
    (hcover : ∀ j ∈ Finset.range n,
      c ≤ ∑ i ∈ I.filter (fun i => j ∈ S i), d i)
    (hfin : μ Set.univ ≠ ∞) :
    (c : ENNReal) * μ (⋃ j ∈ Finset.range n, A j) ≤
      ∑ i ∈ I, (d i : ENNReal) * μ (⋃ j ∈ S i, A j) := by
  classical
  let U : ℕ → Set α := fun k => ⋃ j ∈ Finset.range k, A j
  let delta : ℕ → ℝ := fun j =>
    (μ (U (j + 1))).toReal - (μ (U j)).toReal
  have hne (E : Set α) : μ E ≠ ∞ :=
    ne_top_of_le_ne_top hfin (measure_mono (subset_univ E))
  have hdelta_nonneg : ∀ j, 0 ≤ delta j := by
    intro j
    apply sub_nonneg.2
    apply ENNReal.toReal_mono (hne (U (j + 1)))
    apply measure_mono
    intro x hx
    simp only [U, mem_iUnion, Finset.mem_range] at hx ⊢
    obtain ⟨k, hk, hxA⟩ := hx
    exact ⟨k, Nat.lt_succ_of_lt hk, hxA⟩
  have htel : ∑ j ∈ Finset.range n, delta j = (μ (U n)).toReal := by
    have ht := Finset.sum_range_sub' (fun k => (μ (U k)).toReal) n
    have hneg : ∑ j ∈ Finset.range n, delta j =
        -∑ j ∈ Finset.range n,
          ((μ (U j)).toReal - (μ (U (j + 1))).toReal) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [delta]
      ring
    rw [hneg, ht]
    simp [U]
  have hclass : ∀ i ∈ I,
      ∑ j ∈ S i, delta j ≤ (μ (⋃ j ∈ S i, A j)).toReal := by
    intro i hi
    simpa [U, delta] using
      measure_class_ge_sum_marginals μ A n (S i) (hS i hi) hdisj hfin
  have hreal : c.toReal * (μ (U n)).toReal ≤
      ∑ i ∈ I, (d i).toReal * (μ (⋃ j ∈ S i, A j)).toReal := by
    rw [← htel]
    calc
      c.toReal * ∑ j ∈ Finset.range n, delta j =
          ∑ j ∈ Finset.range n, c.toReal * delta j := by
            rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ Finset.range n,
          (∑ i ∈ I.filter (fun i => j ∈ S i), (d i).toReal) * delta j := by
            apply Finset.sum_le_sum
            intro j hj
            apply mul_le_mul_of_nonneg_right _ (hdelta_nonneg j)
            exact_mod_cast hcover j hj
      _ = ∑ i ∈ I, (d i).toReal * ∑ j ∈ S i, delta j := by
            simp_rw [Finset.sum_filter, Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
            have hf : (Finset.range n).filter (fun j => j ∈ S i) = S i := by
              ext j
              simp only [Finset.mem_filter, Finset.mem_range]
              constructor
              · exact fun hj => hj.2
              · intro hj
                exact ⟨Finset.mem_range.1 (hS i hi hj), hj⟩
            rw [← hf, Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro j hj
            split <;> simp_all
      _ ≤ ∑ i ∈ I, (d i).toReal *
          (μ (⋃ j ∈ S i, A j)).toReal := by
            apply Finset.sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_left (hclass i hi) (by positivity)
  have hleft : (c : ENNReal) * μ (⋃ j ∈ Finset.range n, A j) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (hne _)
  have hterm : ∀ i ∈ I,
      (d i : ENNReal) * μ (⋃ j ∈ S i, A j) ≠ ∞ := by
    intro i hi
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (hne _)
  have hright : ∑ i ∈ I, (d i : ENNReal) * μ (⋃ j ∈ S i, A j) ≠ ∞ :=
    ENNReal.sum_ne_top.2 hterm
  apply (ENNReal.toReal_le_toReal hleft hright).1
  rw [ENNReal.toReal_mul, ENNReal.toReal_sum]
  · simpa [U, ENNReal.toReal_ofNat] using hreal
  · exact hterm

end

end StarKakeyaLower
