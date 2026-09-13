import StarKakeyaLower.StarKakeyaSet

/-!
# Carathéodory splitting along a closed ball

`PROOF.md` Lemma 7.1.  A closed ball is measurable, so it splits the outer
measure of an *arbitrary* (possibly nonmeasurable) planar set additively.  This
is the only place where the "inside" and the "outside" ledgers of the joint
argument are glued, so it is isolated in its own clean module: the file imports
nothing but `StarKakeyaLower.StarKakeyaSet` (itself `import Mathlib` only), and
in particular no module carrying the frozen witness constants.
-/

open Set MeasureTheory
open scoped Function

namespace StarKakeyaLower

noncomputable section

/-- **Closed-ball Carathéodory split.**  For an arbitrary set `E` the planar
outer measure splits additively along a closed ball.  No measurability of `E`
is assumed. -/
theorem outerMeasure_split_closedBall (E : Set Plane) (o : Plane) (r : ℝ) :
    volume.toOuterMeasure E =
      volume.toOuterMeasure (E ∩ Metric.closedBall o r) +
        volume.toOuterMeasure (E \ Metric.closedBall o r) := by
  simp only [Measure.toOuterMeasure_apply]
  exact (measure_inter_add_diff E measurableSet_closedBall).symm

/-- Use site of `outerMeasure_split_closedBall`: an inner lower bound and an
outer lower bound add up to a lower bound for the whole set.  This is the exact
shape in which the joint inner/outer ledger consumes the split. -/
theorem outerMeasure_ge_add_of_inter_of_diff (E : Set Plane) (o : Plane) (r : ℝ)
    {a b : ENNReal}
    (ha : a ≤ volume.toOuterMeasure (E ∩ Metric.closedBall o r))
    (hb : b ≤ volume.toOuterMeasure (E \ Metric.closedBall o r)) :
    a + b ≤ volume.toOuterMeasure E := by
  rw [outerMeasure_split_closedBall E o r]
  exact add_le_add ha hb

/-! ## The countable ledger

`PROOF.md` Lemma 7.2.  The split above is the two-set case; the ledger of §8.5
needs the countably-infinite version, and it must hold for an **arbitrary**
`A`, which is why the outer measure appears on the left. -/

/-- **Separated countable superadditivity** (`PROOF.md` Lemma 7.2).  For an
arbitrary, possibly nonmeasurable `A` and a countable disjoint family of
measurable sets `M`, the outer measures of the pieces `A ∩ M i` sum to at most
the outer measure of `A`.  The index type is `ℕ`, so the sum is a genuine
infinite series, not a finite sum. -/
theorem tsum_outerMeasure_inter_le {A : Set Plane} {M : ℕ → Set Plane}
    (hmeas : ∀ i, MeasurableSet (M i))
    (hdisj : Pairwise (Disjoint on M)) :
    ∑' i, volume.toOuterMeasure (A ∩ M i) ≤ volume.toOuterMeasure A := by
  set U := toMeasurable volume A with hUdef
  have hAU : A ⊆ U := subset_toMeasurable volume A
  have hUmeas (i : ℕ) : MeasurableSet (U ∩ M i) :=
    (measurableSet_toMeasurable volume A).inter (hmeas i)
  have hUdisj : Pairwise (Disjoint on fun i => U ∩ M i) := by
    intro i j hij
    exact ((hdisj hij).mono inter_subset_right inter_subset_right)
  calc ∑' i, volume.toOuterMeasure (A ∩ M i)
      ≤ ∑' i, volume (U ∩ M i) := by
        refine ENNReal.tsum_le_tsum (fun i => ?_)
        rw [Measure.toOuterMeasure_apply]
        exact measure_mono (inter_subset_inter_left _ hAU)
    _ ≤ volume (⋃ i, U ∩ M i) :=
        tsum_meas_le_meas_iUnion_of_disjoint volume hUmeas hUdisj
    _ ≤ volume U := measure_mono (iUnion_subset fun _ => inter_subset_left)
    _ = volume.toOuterMeasure A := by
        rw [Measure.toOuterMeasure_apply, hUdef, measure_toMeasurable]

end

end StarKakeyaLower
