import StarKakeyaLower.CaseIIGeometry

/-!
# Fixed-ball greedy selection for Case II

This is the ROUND-2 selection: after selecting `θ_j`, delete the fixed
projective ball of radius `2 H_j`.  It does not use the variable-radius
`projectiveShadow` intersection relation.  The old equal-ball counterexample
remains in `CaseIIGeometry` as a negative control only.
-/

open Set MeasureTheory Metric Filter

namespace StarKakeyaLower

noncomputable section

/-- Exact fixed deletion set used by ROUND-2. -/
def fixedDeletionBall (theta : Direction) (H : ℝ) : Set Direction :=
  Metric.ball theta (2 * H)

/-- A fixed deletion ball of radius `2H` costs at most `4H` in angular
Hausdorff outer measure.  For a proper ball we lift one interval; once the
nominal interval is at least a full projective period, the full circle bound is
already enough. -/
theorem directionAngleOuter_fixedDeletionBall_le {theta : Direction} {H : ℝ}
    (hH : 0 ≤ H) :
    directionAngleOuter (fixedDeletionBall theta H) ≤ ENNReal.ofReal (4 * H) := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective theta
  by_cases hproper : 4 * H < Real.pi
  · have hball : fixedDeletionBall (t : Direction) H =
        directionQuotient '' Set.Ioo (t - 2 * H) (t + 2 * H) := by
      have hq := quotientInterval_eq_ball (p := Real.pi)
        (a := t - 2 * H) (b := t + 2 * H) (by linarith)
      rw [quotientInterval_of_lt (by linarith)] at hq
      simpa [fixedDeletionBall, directionQuotient] using hq.symm
    rw [hball]
    calc
      directionAngleOuter (directionQuotient '' Set.Ioo (t - 2 * H) (t + 2 * H)) ≤
          volume.toOuterMeasure (Set.Ioo (t - 2 * H) (t + 2 * H)) :=
        directionAngleOuter_image_directionQuotient_le _
      _ = volume (Set.Ioo (t - 2 * H) (t + 2 * H)) := by
        rw [Measure.toOuterMeasure_apply]
      _ = ENNReal.ofReal (4 * H) := by
        rw [Real.volume_Ioo]
        congr 1
        ring
  · have hpi : Real.pi ≤ 4 * H := le_of_not_gt hproper
    have himage : directionQuotient '' Set.Icc t (t + Real.pi) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro q
      let y : ℝ := AddCircle.equivIco Real.pi t q
      have hy := (AddCircle.equivIco Real.pi t q).property
      refine ⟨y, ⟨hy.1, hy.2.le⟩, ?_⟩
      exact AddCircle.coe_equivIco
    calc
      directionAngleOuter (fixedDeletionBall (t : Direction) H) ≤ directionAngleOuter Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = directionAngleOuter (directionQuotient '' Set.Icc t (t + Real.pi)) := by rw [himage]
      _ ≤ volume.toOuterMeasure (Set.Icc t (t + Real.pi)) :=
        directionAngleOuter_image_directionQuotient_le _
      _ = ENNReal.ofReal Real.pi := by
        rw [Measure.toOuterMeasure_apply, Real.volume_Icc]
        · congr 1
          ring
      _ ≤ ENNReal.ofReal (4 * H) := ENNReal.ofReal_le_ofReal hpi

/-! ## The actual greedy construction

The previous version of this file started with a countably infinite selection as
data.  That is not legitimate when the algorithm stops.  The following
definitions make the choice and the recursion first, and only then split into a
finite and an infinite outcome. -/

/-- Supremum of the heights still present in a set of directions. -/
def remainingSup (height : Direction → ℝ) (S : Set Direction) : ℝ :=
  sSup (height '' S)

/-- A strict `m`-approximate maximizer.  The value in the impossible/fallback
branch is irrelevant; all its specifications below assume positive supremum. -/
def chooseAbove (height : Direction → ℝ) (m : ℝ) (S : Set Direction) : Direction :=
  by
    classical
    exact if h : ∃ θ ∈ S, m * remainingSup height S < height θ then
      Classical.choose h
    else Classical.choice inferInstance

/-- Remaining sets produced by deleting the fixed ball of radius `2H` around
the strict approximate maximizer. -/
def fixedGreedyRemaining (height H : Direction → ℝ) (m : ℝ)
    (A : Set Direction) : ℕ → Set Direction
  | 0 => A
  | n + 1 =>
      let S := fixedGreedyRemaining height H m A n
      S \ fixedDeletionBall (chooseAbove height m S)
        (H (chooseAbove height m S))

/-- The selected direction at stage `n` (meaningful exactly while that stage
has positive remaining supremum). -/
def fixedGreedySelected (height H : Direction → ℝ) (m : ℝ)
    (A : Set Direction) (n : ℕ) : Direction :=
  chooseAbove height m (fixedGreedyRemaining height H m A n)

theorem fixedGreedyRemaining_zero (height H : Direction → ℝ) (m : ℝ)
    (A : Set Direction) : fixedGreedyRemaining height H m A 0 = A := rfl

theorem fixedGreedyRemaining_succ (height H : Direction → ℝ) (m : ℝ)
    (A : Set Direction) (n : ℕ) :
    fixedGreedyRemaining height H m A (n + 1) =
      fixedGreedyRemaining height H m A n \
        fixedDeletionBall (fixedGreedySelected height H m A n)
          (H (fixedGreedySelected height H m A n)) := rfl

theorem fixedGreedyRemaining_subset (height H : Direction → ℝ) (m : ℝ)
    (A : Set Direction) (n : ℕ) :
    fixedGreedyRemaining height H m A n ⊆ A := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih => exact diff_subset.trans ih

theorem fixedGreedyRemaining_antitone (height H : Direction → ℝ) (m : ℝ)
    (A : Set Direction) : Antitone (fixedGreedyRemaining height H m A) := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact Subset.rfl
  | succ j hij ih =>
      rw [fixedGreedyRemaining_succ]
      exact diff_subset.trans ih

/-- Positive supremum gives the strict approximate maximizer required by the
paper.  Boundedness is inherited from the fixed initial set. -/
theorem exists_chooseAbove
    {height : Direction → ℝ} {m a : ℝ} {A S : Set Direction}
    (hm0 : 0 < m) (hm1 : m < 1) (hS : S ⊆ A)
    (hbound : ∀ θ ∈ A, height θ ≤ a)
    (hsup : 0 < remainingSup height S) :
    ∃ θ ∈ S, m * remainingSup height S < height θ := by
  have hne : (height '' S).Nonempty := by
    by_contra h
    unfold remainingSup at hsup
    rw [not_nonempty_iff_eq_empty.mp h, Real.sSup_empty] at hsup
    exact lt_irrefl 0 hsup
  have hlt : m * remainingSup height S < remainingSup height S := by
    nlinarith
  obtain ⟨y, hy, hmy⟩ := exists_lt_of_lt_csSup hne hlt
  obtain ⟨θ, hθ, rfl⟩ := hy
  exact ⟨θ, hθ, hmy⟩

theorem chooseAbove_mem
    {height : Direction → ℝ} {m a : ℝ} {A S : Set Direction}
    (hm0 : 0 < m) (hm1 : m < 1) (hS : S ⊆ A)
    (hbound : ∀ θ ∈ A, height θ ≤ a)
    (hsup : 0 < remainingSup height S) :
    chooseAbove height m S ∈ S := by
  rw [chooseAbove, dif_pos (exists_chooseAbove hm0 hm1 hS hbound hsup)]
  exact (Classical.choose_spec (exists_chooseAbove hm0 hm1 hS hbound hsup)).1

theorem chooseAbove_dominates
    {height : Direction → ℝ} {m a : ℝ} {A S : Set Direction}
    (hm0 : 0 < m) (hm1 : m < 1) (hS : S ⊆ A)
    (hbound : ∀ θ ∈ A, height θ ≤ a)
    (hsup : 0 < remainingSup height S) {θ : Direction} (hθ : θ ∈ S) :
    m * height θ < height (chooseAbove height m S) := by
  have himage : height θ ∈ height '' S := ⟨θ, hθ, rfl⟩
  have hbdd : BddAbove (height '' S) :=
    ⟨a, fun y hy => by obtain ⟨x, hx, rfl⟩ := hy; exact hbound x (hS hx)⟩
  have hle : height θ ≤ remainingSup height S := le_csSup hbdd himage
  have hspec := (Classical.choose_spec
    (exists_chooseAbove hm0 hm1 hS hbound hsup)).2
  rw [chooseAbove, dif_pos (exists_chooseAbove hm0 hm1 hS hbound hsup)]
  exact (mul_le_mul_of_nonneg_left hle hm0.le).trans_lt hspec

/-- Genuine finite output: only the `N` directions which were actually
selected are indexed.  `residual` is the stage at which the supremum vanished. -/
structure FiniteFixedSelection (height H : Direction → ℝ) (m : ℝ)
    (A : Set Direction) where
  N : ℕ
  selected : Fin N → Direction
  residual : Set Direction
  selected_eq : ∀ i, selected i = fixedGreedySelected height H m A i
  residual_eq : residual = fixedGreedyRemaining height H m A N
  positive_before : ∀ i : Fin N,
    0 < remainingSup height (fixedGreedyRemaining height H m A i)
  stopped : remainingSup height residual = 0

/-- The construction either stops at a real finite stage or runs forever.
There is no padded `ℕ`-sequence in the finite alternative. -/
inductive FixedSelectionOutcome (height H : Direction → ℝ) (m : ℝ)
    (A : Set Direction) where
  | finite (F : FiniteFixedSelection height H m A)
  | infinite (hpositive : ∀ n,
      0 < remainingSup height (fixedGreedyRemaining height H m A n))

noncomputable def fixedSelectionOutcome (height H : Direction → ℝ) (m : ℝ)
    (A : Set Direction) {a : ℝ}
    (hheight0 : ∀ θ, 0 ≤ height θ)
    (hbound : ∀ θ ∈ A, height θ ≤ a) :
    FixedSelectionOutcome height H m A := by
  classical
  by_cases hall : ∀ n, 0 < remainingSup height (fixedGreedyRemaining height H m A n)
  · exact .infinite hall
  · push_neg at hall
    let N := Nat.find hall
    have hN : remainingSup height (fixedGreedyRemaining height H m A N) ≤ 0 :=
      Nat.find_spec hall
    have hbdd : BddAbove (height '' fixedGreedyRemaining height H m A N) :=
      ⟨a, fun y hy => by
        obtain ⟨θ, hθ, rfl⟩ := hy
        exact hbound θ (fixedGreedyRemaining_subset height H m A N hθ)⟩
    have hnonneg : 0 ≤ remainingSup height
        (fixedGreedyRemaining height H m A N) := by
      by_cases hne : (height '' fixedGreedyRemaining height H m A N).Nonempty
      · obtain ⟨_, θ, hθ, rfl⟩ := hne
        exact (hheight0 θ).trans (le_csSup hbdd ⟨θ, hθ, rfl⟩)
      · unfold remainingSup
        rw [not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    apply FixedSelectionOutcome.finite
    refine { N := N
             selected := fun i => fixedGreedySelected height H m A i
             residual := fixedGreedyRemaining height H m A N
             selected_eq := fun _ => rfl
             residual_eq := rfl
             positive_before := ?_
             stopped := le_antisymm hN hnonneg }
    intro i
    exact lt_of_not_ge (Nat.find_min hall i.isLt)

namespace FiniteFixedSelection

variable {height H : Direction → ℝ} {m a : ℝ} {A : Set Direction}

/-- At a genuine finite stop every remaining height is zero. -/
theorem residual_height_zero (F : FiniteFixedSelection height H m A)
    (hheight0 : ∀ θ, 0 ≤ height θ)
    (hbound : ∀ θ ∈ A, height θ ≤ a) :
    ∀ θ ∈ F.residual, height θ = 0 := by
  intro θ hθ
  have hbdd : BddAbove (height '' F.residual) :=
    ⟨a, fun y hy => by
      obtain ⟨x, hx, rfl⟩ := hy
      apply hbound x
      rw [F.residual_eq] at hx
      exact fixedGreedyRemaining_subset height H m A F.N hx⟩
  have hle : height θ ≤ remainingSup height F.residual :=
    le_csSup hbdd ⟨θ, hθ, rfl⟩
  rw [F.stopped] at hle
  exact le_antisymm hle (hheight0 θ)

end FiniteFixedSelection


/-- Infinite fixed-ball greedy data. `dominates` is the strict approximate-sup
choice `height(selected n) > m * height x` for every currently remaining `x`.
The deletion-cost field isolates only the standard circle-length fact
`|B(θ,2H)| ≤ 4H`; it is unrelated to intersection of variable-radius balls. -/
structure FixedDeletionGreedyData (height H : Direction → ℝ) where
  initial : Set Direction
  remaining : ℕ → Set Direction
  selected : ℕ → Direction
  deleted : ℕ → Set Direction
  multiplier : ℝ
  multiplier_pos : 0 < multiplier
  multiplier_lt_one : multiplier < 1
  start : remaining 0 = initial
  selected_mem : ∀ n, selected n ∈ remaining n
  step : ∀ n, remaining (n + 1) = remaining n \ deleted n
  deleted_eq_fixedBall : ∀ n,
    deleted n = fixedDeletionBall (selected n) (H (selected n))
  dominates : ∀ n x, x ∈ remaining n →
    multiplier * height x < height (selected n)
  deleted_cost : ∀ n,
    directionAngleOuter (deleted n) ≤ ENNReal.ofReal (4 * H (selected n))

/-- The infinite alternative of `fixedSelectionOutcome`, instantiated as the
legacy record used by the geometric lemmas below.  All selection fields are
proved from `Classical.choose` and the recursive remaining sets. -/
noncomputable def infiniteGreedyData
    {height H : Direction → ℝ} {m a : ℝ} {A : Set Direction}
    (hm0 : 0 < m) (hm1 : m < 1)
    (hbound : ∀ θ ∈ A, height θ ≤ a)
    (hpositive : ∀ n,
      0 < remainingSup height (fixedGreedyRemaining height H m A n))
    (hcost : ∀ n, directionAngleOuter
      (fixedDeletionBall (fixedGreedySelected height H m A n)
        (H (fixedGreedySelected height H m A n))) ≤
      ENNReal.ofReal (4 * H (fixedGreedySelected height H m A n))) :
    FixedDeletionGreedyData height H where
  initial := A
  remaining := fixedGreedyRemaining height H m A
  selected := fixedGreedySelected height H m A
  deleted := fun n => fixedDeletionBall (fixedGreedySelected height H m A n)
    (H (fixedGreedySelected height H m A n))
  multiplier := m
  multiplier_pos := hm0
  multiplier_lt_one := hm1
  start := rfl
  selected_mem n := chooseAbove_mem hm0 hm1
    (fixedGreedyRemaining_subset height H m A n) hbound (hpositive n)
  step _ := rfl
  deleted_eq_fixedBall _ := rfl
  dominates n x hx := chooseAbove_dominates hm0 hm1
    (fixedGreedyRemaining_subset height H m A n) hbound (hpositive n) hx
  deleted_cost := hcost

namespace FixedDeletionGreedyData

variable {height H : Direction → ℝ} (G : FixedDeletionGreedyData height H)

/-- The remaining sets are decreasing. -/
theorem antitone_remaining : Antitone G.remaining := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact Subset.rfl
  | succ j hij ih =>
      rw [G.step j]
      exact diff_subset.trans ih

/-- Every stage stays in the initial set. -/
theorem remaining_subset_initial (n : ℕ) : G.remaining n ⊆ G.initial := by
  rw [← G.start]
  exact G.antitone_remaining (Nat.zero_le n)

/-- A later selected direction survived the earlier fixed deletion. -/
theorem selected_not_mem_earlier_deleted {j n : ℕ} (hjn : j < n) :
    G.selected n ∉ G.deleted j := by
  have hn : G.selected n ∈ G.remaining (j + 1) :=
    G.antitone_remaining (Nat.succ_le_iff.mpr hjn) (G.selected_mem n)
  rw [G.step j] at hn
  exact hn.2

/-- Fixed deletion gives the exact centre separation `d ≥ 2H_j`. -/
theorem future_distance_ge_two_H {j n : ℕ} (hjn : j < n) :
    2 * H (G.selected j) ≤ dist (G.selected j) (G.selected n) := by
  have hnot := G.selected_not_mem_earlier_deleted hjn
  rw [G.deleted_eq_fixedBall j, fixedDeletionBall, Metric.mem_ball, not_lt] at hnot
  simpa [dist_comm] using hnot

/-- Approximate-sup selection controls the future *unscaled* inverse-sine
shadow by the selected scaled weight.  This is the inequality actually used in
ROUND-2; it does not claim the generally false `H_n < H_j`. -/
theorem future_arcsin_lt_selected_H
    {rho : ℝ} (hrho : 0 < rho)
    (hheight_pos : ∀ n, 0 < height (G.selected n))
    (hheight_scaled : ∀ n, height (G.selected n) < G.multiplier * rho)
    (hH : ∀ n, H (G.selected n) =
      Real.arcsin (height (G.selected n) / (G.multiplier * rho)))
    {j n : ℕ} (hjn : j < n) :
    Real.arcsin (height (G.selected n) / rho) < H (G.selected j) := by
  have hm := G.multiplier_pos
  have hdom := G.dominates j (G.selected n)
    (G.antitone_remaining (Nat.le_of_lt hjn) (G.selected_mem n))
  have harg : height (G.selected n) / rho <
      height (G.selected j) / (G.multiplier * rho) := by
    rw [div_lt_div_iff₀ hrho (mul_pos hm hrho)]
    nlinarith
  rw [hH j]
  apply Real.arcsin_lt_arcsin
  · have := hheight_pos n
    have : 0 ≤ height (G.selected n) / rho := div_nonneg this.le hrho.le
    linarith
  · exact harg
  · rw [div_le_one (mul_pos hm hrho)]
    exact (hheight_scaled j).le

/-- The selected direction's own unscaled shadow is strictly smaller than its
scaled ROUND-2 weight. -/
theorem selected_arcsin_lt_H
    {rho : ℝ} (hrho : 0 < rho)
    (hheight_pos : ∀ n, 0 < height (G.selected n))
    (hheight_scaled : ∀ n, height (G.selected n) < G.multiplier * rho)
    (hH : ∀ n, H (G.selected n) =
      Real.arcsin (height (G.selected n) / (G.multiplier * rho)))
    (n : ℕ) :
    Real.arcsin (height (G.selected n) / rho) < H (G.selected n) := by
  have hm0 := G.multiplier_pos
  have hm1 := G.multiplier_lt_one
  have hp := hheight_pos n
  have harg : height (G.selected n) / rho <
      height (G.selected n) / (G.multiplier * rho) := by
    apply (div_lt_div_iff_of_pos_left hp hrho (mul_pos hm0 hrho)).2
    nlinarith
  rw [hH n]
  apply Real.arcsin_lt_arcsin
  · have : 0 ≤ height (G.selected n) / rho := div_nonneg hp.le hrho.le
    linarith
  · exact harg
  · rw [div_le_one (mul_pos hm0 hrho)]
    exact (hheight_scaled n).le

/-- ROUND-2's strict triangle-separation inequality. -/
theorem future_triangle_shadow_sum_lt_distance
    {rho : ℝ} (hrho : 0 < rho)
    (hheight_pos : ∀ n, 0 < height (G.selected n))
    (hheight_scaled : ∀ n, height (G.selected n) < G.multiplier * rho)
    (hH : ∀ n, H (G.selected n) =
      Real.arcsin (height (G.selected n) / (G.multiplier * rho)))
    {j n : ℕ} (hjn : j < n) :
    Real.arcsin (height (G.selected j) / rho) +
      Real.arcsin (height (G.selected n) / rho) <
        dist (G.selected j) (G.selected n) := by
  calc
    _ < H (G.selected j) + H (G.selected j) :=
      add_lt_add (G.selected_arcsin_lt_H hrho hheight_pos hheight_scaled hH j)
        (G.future_arcsin_lt_selected_H hrho hheight_pos hheight_scaled hH hjn)
    _ = 2 * H (G.selected j) := by ring
    _ ≤ _ := G.future_distance_ge_two_H hjn

/-- Consequently the selected complete open triangles are pairwise disjoint.
This uses centre separation from fixed deletion, not intersection-defined
shadows. -/
theorem pairwise_disjoint_selected_triangleInterior
    {rho : ℝ} (o : Plane) (needle : ℕ → UnitNeedle)
    (hrho : 0 < rho)
    (hneedle : ∀ n, height (G.selected n) = (needle n).height o)
    (hheight_pos : ∀ n, 0 < height (G.selected n))
    (hheight_scaled : ∀ n, height (G.selected n) < G.multiplier * rho)
    (hH : ∀ n, H (G.selected n) =
      Real.arcsin (height (G.selected n) / (G.multiplier * rho)))
    (hdir : ∀ n, (needle n).HasDirection (G.selected n))
    (hout : ∀ n, (needle n).OutsideBall rho o) :
    Pairwise (fun i j => Disjoint ((needle i).triangleInterior o)
      ((needle j).triangleInterior o)) := by
  apply pairwise_disjoint_triangleInterior (rayDirection o) G.selected
    (fun n => height (G.selected n))
    (fun n => Real.arcsin (height (G.selected n) / rho)) rho o needle
  · intro n
    rw [hneedle n]
    apply (needle n).triangleRayControlled_of_outside hrho
    · simpa [hneedle n] using hheight_pos n
    · rw [← hneedle n]
      exact (hheight_scaled n).trans_le
        (mul_le_of_le_one_left hrho.le G.multiplier_lt_one.le)
    · exact hdir n
    · exact hout n
  · exact fun _ => le_rfl
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    rw [Metric.mem_ball] at hxi hxj
    have hdist : dist (G.selected i) (G.selected j) <
        Real.arcsin (height (G.selected i) / rho) +
          Real.arcsin (height (G.selected j) / rho) := by
      calc
        dist (G.selected i) (G.selected j) ≤
            dist (G.selected i) x + dist x (G.selected j) := dist_triangle _ _ _
        _ < _ := add_lt_add (by simpa [dist_comm] using hxi) hxj
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · exact (not_lt_of_ge (G.future_triangle_shadow_sum_lt_distance hrho
        hheight_pos hheight_scaled hH hij').le) hdist
    · have hsep := G.future_triangle_shadow_sum_lt_distance hrho
        hheight_pos hheight_scaled hH hji'
      rw [dist_comm, add_comm] at hsep
      exact (not_lt_of_ge hsep.le) hdist

/-- A residual direction survives every fixed deletion. -/
theorem residual_not_mem_deleted {theta : Direction}
    (htheta : theta ∈ greedyResidual G.remaining) (n : ℕ) :
    theta ∉ G.deleted n := by
  have hn := mem_iInter.mp htheta (n + 1)
  rw [G.step n] at hn
  exact hn.2

/-- Fixed-ball ROUND-2 separation between the zero-height residual fan and all
selected open triangles.  Survival gives distance at least `2H_n`, while the
selected triangle's unscaled ray shadow is strictly below `H_n`. -/
theorem disjoint_residualFan_selectedTriangleUnion
    {E : Set Plane} (K : StarShapedKakeya E) {rho : ℝ}
    (hrho : 0 < rho)
    (hzero : ∀ theta ∈ greedyResidual G.remaining,
      (K.needleFamily theta).height K.center = 0)
    (hout : ∀ theta ∈ G.initial,
      (K.needleFamily theta).OutsideBall rho K.center)
    (hheight : ∀ theta, height theta =
      (K.needleFamily theta).height K.center)
    (hselected_pos : ∀ n, 0 < height (G.selected n))
    (hselected_lt : ∀ n, height (G.selected n) < G.multiplier * rho)
    (hH : ∀ n, H (G.selected n) =
      Real.arcsin (height (G.selected n) / (G.multiplier * rho))) :
    Disjoint (residualFan K (greedyResidual G.remaining))
      (⋃ n, (K.needleFamily (G.selected n)).triangleInterior K.center) := by
  rw [Set.disjoint_left]
  intro p hpFan hpTriangles
  simp only [residualFan, mem_iUnion] at hpFan
  obtain ⟨theta, htheta, hpseg⟩ := hpFan
  simp only [mem_iUnion] at hpTriangles
  obtain ⟨n, hpTri⟩ := hpTriangles
  have hselinit : G.selected n ∈ G.initial :=
    G.remaining_subset_initial n (G.selected_mem n)
  have hthetainit : theta ∈ G.initial :=
    G.remaining_subset_initial 0 (mem_iInter.mp htheta 0)
  have hpne : p ≠ K.center := by
    intro h
    subst p
    exact (K.needleFamily (G.selected n)).center_not_mem_triangleInterior_of_outside
      hrho (by simpa [← hheight] using hselected_pos n) (hout _ hselinit) hpTri
  have hpray : rayDirection K.center p = theta :=
    (K.needleFamily theta).rayDirection_eq_of_mem_segment_left hrho
      (hzero theta htheta) (K.needleFamily_hasDirection theta)
      (hout theta hthetainit) hpseg hpne
  have hshadow : dist (G.selected n) theta <
      Real.arcsin (height (G.selected n) / rho) := by
    rw [← hpray, hheight]
    rw [dist_comm]
    exact (K.needleFamily (G.selected n)).triangleRayControlled_of_outside hrho
      (by simpa [← hheight] using hselected_pos n)
      (by
        rw [← hheight]
        exact (hselected_lt n).trans_le
          (mul_le_of_le_one_left hrho.le G.multiplier_lt_one.le))
      (K.needleFamily_hasDirection (G.selected n)) (hout _ hselinit) p hpTri
  have hnot := G.residual_not_mem_deleted htheta n
  rw [G.deleted_eq_fixedBall n, fixedDeletionBall, Metric.mem_ball, not_lt] at hnot
  rw [dist_comm] at hnot
  have hasin := G.selected_arcsin_lt_H hrho hselected_pos hselected_lt hH n
  have hHpos : 0 < H (G.selected n) := (Real.arcsin_nonneg.2
    (div_nonneg (hselected_pos n).le hrho.le)).trans_lt hasin
  linarith

/-- The fixed-ball infinite branch gives the exact residual-fan plus selected
triangle-area inequality used by the minimax step. -/
theorem geometric_outerMeasure_lower
    {E : Set Plane} (K : StarShapedKakeya E) {rho : ℝ}
    (hrho : 0 < rho)
    (hzero : ∀ theta ∈ greedyResidual G.remaining,
      (K.needleFamily theta).height K.center = 0)
    (hout : ∀ theta ∈ G.initial,
      (K.needleFamily theta).OutsideBall rho K.center)
    (hheight : ∀ theta, height theta =
      (K.needleFamily theta).height K.center)
    (hselected_pos : ∀ n, 0 < height (G.selected n))
    (hselected_lt : ∀ n, height (G.selected n) < G.multiplier * rho)
    (hH : ∀ n, H (G.selected n) =
      Real.arcsin (height (G.selected n) / (G.multiplier * rho))) :
    ENNReal.ofReal (rho ^ 2 / 2) * directionAngleOuter (greedyResidual G.remaining) +
        ∑' n, volume ((K.needleFamily (G.selected n)).triangleInterior K.center) ≤
      volume.toOuterMeasure E := by
  let R := greedyResidual G.remaining
  let needle : ℕ → UnitNeedle := fun n => K.needleFamily (G.selected n)
  have hresinit : R ⊆ G.initial := fun theta htheta =>
    G.remaining_subset_initial 0 (mem_iInter.mp htheta 0)
  have hfan := K.residualFan_outerMeasure_lower hrho R hzero
    (fun theta htheta => hout theta (hresinit htheta))
  have hpair := G.pairwise_disjoint_selected_triangleInterior K.center needle hrho
    (fun n => hheight (G.selected n)) hselected_pos hselected_lt hH
    (fun n => K.needleFamily_hasDirection (G.selected n))
    (fun n => hout _ (G.remaining_subset_initial n (G.selected_mem n)))
  have hdisjoint := G.disjoint_residualFan_selectedTriangleUnion K hrho hzero hout
    hheight hselected_pos hselected_lt hH
  let U : Set Plane := ⋃ n, (needle n).triangleInterior K.center
  have hU : MeasurableSet U := measurableSet_selectedTriangleUnion K.center needle
  have hUE : U ⊆ E := iUnion_subset fun n =>
    (UnitNeedle.triangleInterior_subset_triangleHull K.center _).trans
      (K.triangleHull_subset (G.selected n))
  have hadd : volume.toOuterMeasure (residualFan K R) + volume U ≤
      volume.toOuterMeasure E :=
    outerMeasure_add_le_of_disjoint_measurable hU hdisjoint
      (K.residualFan_subset R) hUE
  calc
    ENNReal.ofReal (rho ^ 2 / 2) * directionAngleOuter R +
          ∑' n, volume ((needle n).triangleInterior K.center) =
        ENNReal.ofReal (rho ^ 2 / 2) * directionAngleOuter R + volume U := by
      rw [volume_selectedTriangleUnion K.center needle hpair]
    _ ≤ volume.toOuterMeasure (residualFan K R) + volume U :=
      add_le_add hfan le_rfl
    _ ≤ volume.toOuterMeasure E := hadd

/-- Even before identifying the residual, the pairwise-disjoint selected
triangles alone are bounded by the ambient outer measure. -/
theorem selected_triangle_volume_le_outer
    {E : Set Plane} (K : StarShapedKakeya E) {rho : ℝ}
    (hrho : 0 < rho)
    (hheight : ∀ theta, height theta =
      (K.needleFamily theta).height K.center)
    (hselected_pos : ∀ n, 0 < height (G.selected n))
    (hselected_lt : ∀ n, height (G.selected n) < G.multiplier * rho)
    (hH : ∀ n, H (G.selected n) =
      Real.arcsin (height (G.selected n) / (G.multiplier * rho)))
    (hout : ∀ theta ∈ G.initial,
      (K.needleFamily theta).OutsideBall rho K.center) :
    (∑' n, volume ((K.needleFamily (G.selected n)).triangleInterior K.center)) ≤
      volume.toOuterMeasure E := by
  let needle : ℕ → UnitNeedle := fun n => K.needleFamily (G.selected n)
  have hpair := G.pairwise_disjoint_selected_triangleInterior K.center needle hrho
    (fun n => hheight (G.selected n)) hselected_pos hselected_lt hH
    (fun n => K.needleFamily_hasDirection (G.selected n))
    (fun n => hout _ (G.remaining_subset_initial n (G.selected_mem n)))
  let U : Set Plane := ⋃ n, (needle n).triangleInterior K.center
  have hsub : U ⊆ E := iUnion_subset fun n =>
    (UnitNeedle.triangleInterior_subset_triangleHull K.center _).trans
      (K.triangleHull_subset (G.selected n))
  calc
    _ = volume U := (volume_selectedTriangleUnion K.center needle hpair).symm
    _ ≤ volume.toOuterMeasure E := measure_mono hsub

/-- The residual is exactly the initial set minus all fixed deletions. -/
theorem greedyResidual_eq_fixed :
    greedyResidual G.remaining = G.initial \ ⋃ n, G.deleted n := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · simpa [G.start] using mem_iInter.mp hx 0
    · simp only [mem_iUnion, not_exists]
      intro n hdel
      have hn := mem_iInter.mp hx (n + 1)
      rw [G.step n] at hn
      exact hn.2 hdel
  · rintro ⟨hinit, hnot⟩
    simp only [mem_iUnion, not_exists] at hnot
    rw [greedyResidual, mem_iInter]
    intro n
    induction n with
    | zero => simpa [G.start] using hinit
    | succ n ih => rw [G.step n]; exact ⟨ih, hnot n⟩

/-- Outer-measure cover in the exact ROUND-2 normalization:
`initial ≤ residual + Σ 4H_n`. -/
theorem initial_directionAngleOuter_le_residual_add_cost :
    directionAngleOuter G.initial ≤ directionAngleOuter (greedyResidual G.remaining) +
      ∑' n, ENNReal.ofReal (4 * H (G.selected n)) := by
  have hcover : G.initial ⊆ greedyResidual G.remaining ∪ ⋃ n, G.deleted n := by
    rw [G.greedyResidual_eq_fixed]
    aesop
  calc
    directionAngleOuter G.initial ≤ directionAngleOuter (greedyResidual G.remaining ∪ ⋃ n, G.deleted n) :=
      MeasureTheory.OuterMeasure.mono _ hcover
    _ ≤ directionAngleOuter (greedyResidual G.remaining) + directionAngleOuter (⋃ n, G.deleted n) :=
      measure_union_le _ _
    _ ≤ directionAngleOuter (greedyResidual G.remaining) + ∑' n, directionAngleOuter (G.deleted n) :=
      add_le_add_right (measure_iUnion_le _) _
    _ ≤ directionAngleOuter (greedyResidual G.remaining) +
        ∑' n, ENNReal.ofReal (4 * H (G.selected n)) :=
      add_le_add_right (ENNReal.tsum_le_tsum G.deleted_cost) _

/-- Infinite selection with finite total deletion cost has zero residual height. -/
theorem residual_height_zero_of_summable_cost
    (height_nonneg : ∀ theta, 0 ≤ height theta)
    (hheight_le_H : ∀ n, height (G.selected n) ≤ H (G.selected n))
    (hcost : Summable (fun n => H (G.selected n))) :
    ∀ theta ∈ greedyResidual G.remaining, height theta = 0 := by
  have hHtend : Tendsto (fun n => H (G.selected n)) atTop (nhds 0) :=
    hcost.tendsto_atTop_zero
  have hheighttend : Tendsto (fun n => height (G.selected n)) atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall fun n => height_nonneg _)
      (Eventually.of_forall hheight_le_H) hHtend
  intro theta htheta
  exact residual_height_eq_zero_of_tendsto height G.remaining height_nonneg
    G.multiplier_pos
    (fun n x hx => (G.dominates n x (mem_iInter.mp hx n)).le)
    hheighttend htheta

/-- Finite stopping branch: if a stage has no positive remaining height, every
residual direction has height zero. -/
theorem residual_height_zero_of_finite_stop
    (height_nonneg : ∀ theta, 0 ≤ height theta) (N : ℕ)
    (hstop : ∀ theta ∈ G.remaining N, height theta ≤ 0) :
    ∀ theta ∈ greedyResidual G.remaining, height theta = 0 := by
  intro theta htheta
  exact StarKakeyaLower.residual_height_eq_zero_of_finite_stop
    height G.remaining height_nonneg N hstop htheta

end FixedDeletionGreedyData

namespace FiniteFixedSelection

variable {height H : Direction → ℝ} {m a : ℝ} {A : Set Direction}

/-- The genuine finite union of the triangles selected before stopping. -/
def selectedTriangleUnion (F : FiniteFixedSelection height H m A)
    {E : Set Plane} (K : StarShapedKakeya E) : Set Plane :=
  ⋃ i : Fin F.N, (K.needleFamily (F.selected i)).triangleInterior K.center

theorem measurableSet_selectedTriangleUnion
    (F : FiniteFixedSelection height H m A) {E : Set Plane}
    (K : StarShapedKakeya E) : MeasurableSet (F.selectedTriangleUnion K) :=
  MeasurableSet.iUnion fun i =>
    (K.needleFamily (F.selected i)).triangleInterior_measurable K.center

theorem selectedTriangleUnion_subset
    (F : FiniteFixedSelection height H m A) {E : Set Plane}
    (K : StarShapedKakeya E) : F.selectedTriangleUnion K ⊆ E :=
  iUnion_subset fun i =>
    (UnitNeedle.triangleInterior_subset_triangleHull K.center _).trans
      (K.triangleHull_subset (F.selected i))

theorem selected_mem (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (hbound : ∀ θ ∈ A, height θ ≤ a)
    (i : Fin F.N) : F.selected i ∈ fixedGreedyRemaining height H m A i := by
  rw [F.selected_eq i]
  exact chooseAbove_mem hm0 hm1 (fixedGreedyRemaining_subset height H m A i) hbound
    (F.positive_before i)

theorem selected_mem_initial (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (hbound : ∀ θ ∈ A, height θ ≤ a)
    (i : Fin F.N) : F.selected i ∈ A :=
  fixedGreedyRemaining_subset height H m A i (F.selected_mem hm0 hm1 hbound i)

theorem residual_subset_initial (F : FiniteFixedSelection height H m A) :
    F.residual ⊆ A := by
  rw [F.residual_eq]
  exact fixedGreedyRemaining_subset height H m A F.N

theorem selected_not_mem_earlier_ball (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (hbound : ∀ θ ∈ A, height θ ≤ a)
    {i j : Fin F.N} (hij : i < j) :
    F.selected j ∉ fixedDeletionBall (F.selected i) (H (F.selected i)) := by
  have hj := F.selected_mem hm0 hm1 hbound j
  have hjstage := fixedGreedyRemaining_antitone height H m A
    (Nat.succ_le_iff.mpr hij) hj
  rw [fixedGreedyRemaining_succ, ← F.selected_eq i] at hjstage
  exact hjstage.2

theorem future_distance_ge_two_H (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (hbound : ∀ θ ∈ A, height θ ≤ a)
    {i j : Fin F.N} (hij : i < j) :
    2 * H (F.selected i) ≤ dist (F.selected i) (F.selected j) := by
  have h := F.selected_not_mem_earlier_ball hm0 hm1 hbound hij
  rw [fixedDeletionBall, Metric.mem_ball, not_lt] at h
  simpa [dist_comm] using h

theorem dominates_future (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (hbound : ∀ θ ∈ A, height θ ≤ a)
    {i j : Fin F.N} (hij : i < j) :
    m * height (F.selected j) < height (F.selected i) := by
  have hj := F.selected_mem hm0 hm1 hbound j
  have hjstage := fixedGreedyRemaining_antitone height H m A (Nat.le_of_lt hij) hj
  rw [F.selected_eq i]
  exact chooseAbove_dominates hm0 hm1 (fixedGreedyRemaining_subset height H m A i)
    hbound (F.positive_before i) hjstage

theorem triangle_shadow_sum_lt_distance (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (hbound : ∀ θ ∈ A, height θ ≤ a)
    {rho : ℝ} (hrho : 0 < rho)
    (hpos : ∀ i, 0 < height (F.selected i))
    (hscaled : ∀ i, height (F.selected i) < m * rho)
    (hH : ∀ i, H (F.selected i) =
      Real.arcsin (height (F.selected i) / (m * rho)))
    {i j : Fin F.N} (hij : i < j) :
    Real.arcsin (height (F.selected i) / rho) +
      Real.arcsin (height (F.selected j) / rho) <
        dist (F.selected i) (F.selected j) := by
  have hself : Real.arcsin (height (F.selected i) / rho) < H (F.selected i) := by
    rw [hH i]
    apply Real.arcsin_lt_arcsin
    · have := div_nonneg (hpos i).le hrho.le; linarith
    · apply (div_lt_div_iff_of_pos_left (hpos i) hrho (mul_pos hm0 hrho)).2
      nlinarith
    · rw [div_le_one (mul_pos hm0 hrho)]
      exact (hscaled i).le
  have hfuture : Real.arcsin (height (F.selected j) / rho) < H (F.selected i) := by
    rw [hH i]
    apply Real.arcsin_lt_arcsin
    · have := div_nonneg (hpos j).le hrho.le; linarith
    · rw [div_lt_div_iff₀ hrho (mul_pos hm0 hrho)]
      nlinarith [F.dominates_future hm0 hm1 hbound hij]
    · rw [div_le_one (mul_pos hm0 hrho)]
      exact (hscaled i).le
  calc
    _ < H (F.selected i) + H (F.selected i) := add_lt_add hself hfuture
    _ = 2 * H (F.selected i) := by ring
    _ ≤ _ := F.future_distance_ge_two_H hm0 hm1 hbound hij

theorem pairwise_disjoint_triangles (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (hbound : ∀ θ ∈ A, height θ ≤ a)
    {E : Set Plane} (K : StarShapedKakeya E) {rho : ℝ} (hrho : 0 < rho)
    (hheight : ∀ θ, height θ = (K.needleFamily θ).height K.center)
    (hpos : ∀ i, 0 < height (F.selected i))
    (hscaled : ∀ i, height (F.selected i) < m * rho)
    (hH : ∀ i, H (F.selected i) =
      Real.arcsin (height (F.selected i) / (m * rho)))
    (hout : ∀ θ ∈ A, (K.needleFamily θ).OutsideBall rho K.center) :
    Pairwise (fun i j : Fin F.N => Disjoint
      ((K.needleFamily (F.selected i)).triangleInterior K.center)
      ((K.needleFamily (F.selected j)).triangleInterior K.center)) := by
  apply pairwise_disjoint_triangleInterior (rayDirection K.center) F.selected
    (fun i => height (F.selected i))
    (fun i => Real.arcsin (height (F.selected i) / rho)) rho K.center
    (fun i => K.needleFamily (F.selected i))
  · intro i
    rw [hheight]
    apply (K.needleFamily (F.selected i)).triangleRayControlled_of_outside hrho
    · simpa [← hheight] using hpos i
    · rw [← hheight]
      exact (hscaled i).trans_le (mul_le_of_le_one_left hrho.le hm1.le)
    · exact K.needleFamily_hasDirection _
    · exact hout _ (F.selected_mem_initial hm0 hm1 hbound i)
  · exact fun _ => le_rfl
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    rw [Metric.mem_ball] at hxi hxj
    have hd : dist (F.selected i) (F.selected j) <
        Real.arcsin (height (F.selected i) / rho) +
          Real.arcsin (height (F.selected j) / rho) :=
      (dist_triangle _ x _).trans_lt (add_lt_add (by simpa [dist_comm] using hxi) hxj)
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact (not_lt_of_ge (F.triangle_shadow_sum_lt_distance hm0 hm1 hbound hrho
        hpos hscaled hH hij).le) hd
    · have hs := F.triangle_shadow_sum_lt_distance hm0 hm1 hbound hrho
        hpos hscaled hH hji
      rw [dist_comm, add_comm] at hs
      exact (not_lt_of_ge hs.le) hd

theorem residual_not_mem_selected_ball (F : FiniteFixedSelection height H m A)
    {theta : Direction} (htheta : theta ∈ F.residual) (i : Fin F.N) :
    theta ∉ fixedDeletionBall (F.selected i) (H (F.selected i)) := by
  rw [F.residual_eq] at htheta
  have hi := fixedGreedyRemaining_antitone height H m A (Nat.succ_le_iff.mpr i.isLt) htheta
  rw [fixedGreedyRemaining_succ, ← F.selected_eq i] at hi
  exact hi.2

theorem disjoint_residualFan_selectedTriangleUnion
    (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (hbound : ∀ θ ∈ A, height θ ≤ a)
    {E : Set Plane} (K : StarShapedKakeya E) {rho : ℝ} (hrho : 0 < rho)
    (hzero : ∀ theta ∈ F.residual,
      (K.needleFamily theta).height K.center = 0)
    (hheight : ∀ θ, height θ = (K.needleFamily θ).height K.center)
    (hpos : ∀ i, 0 < height (F.selected i))
    (hscaled : ∀ i, height (F.selected i) < m * rho)
    (hH : ∀ i, H (F.selected i) =
      Real.arcsin (height (F.selected i) / (m * rho)))
    (hout : ∀ θ ∈ A, (K.needleFamily θ).OutsideBall rho K.center) :
    Disjoint (residualFan K F.residual)
      (⋃ i : Fin F.N, (K.needleFamily (F.selected i)).triangleInterior K.center) := by
  rw [Set.disjoint_left]
  intro p hpFan hpTriangles
  simp only [residualFan, mem_iUnion] at hpFan hpTriangles
  obtain ⟨theta, htheta, hpseg⟩ := hpFan
  obtain ⟨i, hpTri⟩ := hpTriangles
  have hpne : p ≠ K.center := by
    intro heq; subst p
    exact (K.needleFamily (F.selected i)).center_not_mem_triangleInterior_of_outside
      hrho (by simpa [← hheight] using hpos i)
      (hout _ (F.selected_mem_initial hm0 hm1 hbound i)) hpTri
  have hpray := (K.needleFamily theta).rayDirection_eq_of_mem_segment_left hrho
    (hzero theta htheta) (K.needleFamily_hasDirection theta)
    (hout theta (F.residual_subset_initial htheta)) hpseg hpne
  have hshadow : dist (F.selected i) theta <
      Real.arcsin (height (F.selected i) / rho) := by
    rw [← hpray, dist_comm, hheight]
    exact (K.needleFamily (F.selected i)).triangleRayControlled_of_outside hrho
      (by simpa [← hheight] using hpos i)
      (by
        rw [← hheight]
        exact (hscaled i).trans_le (mul_le_of_le_one_left hrho.le hm1.le))
      (K.needleFamily_hasDirection _) (hout _ (F.selected_mem_initial hm0 hm1 hbound i))
      p hpTri
  have hnot := F.residual_not_mem_selected_ball htheta i
  rw [fixedDeletionBall, Metric.mem_ball, not_lt, dist_comm] at hnot
  have hself : Real.arcsin (height (F.selected i) / rho) < H (F.selected i) := by
    rw [hH i]
    apply Real.arcsin_lt_arcsin
    · have := div_nonneg (hpos i).le hrho.le; linarith
    · apply (div_lt_div_iff_of_pos_left (hpos i) hrho (mul_pos hm0 hrho)).2
      nlinarith
    · rw [div_le_one (mul_pos hm0 hrho)]; exact (hscaled i).le
  have hHpos : 0 < H (F.selected i) := (Real.arcsin_nonneg.2
    (div_nonneg (hpos i).le hrho.le)).trans_lt hself
  linarith

theorem volume_selectedTriangleUnion
    (F : FiniteFixedSelection height H m A)
    {E : Set Plane} (K : StarShapedKakeya E)
    (hpair : Pairwise (fun i j : Fin F.N => Disjoint
      ((K.needleFamily (F.selected i)).triangleInterior K.center)
      ((K.needleFamily (F.selected j)).triangleInterior K.center))) :
    volume (F.selectedTriangleUnion K) =
      ∑' i : Fin F.N,
        volume ((K.needleFamily (F.selected i)).triangleInterior K.center) := by
  exact MeasureTheory.measure_iUnion hpair fun i =>
    (K.needleFamily (F.selected i)).triangleInterior_measurable K.center

/-- Finite geometric assembly: the stopped residual fan and all genuinely
selected triangles are combined without padding the selection by dummy terms. -/
theorem geometric_outerMeasure_lower
    (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (hbound : ∀ θ ∈ A, height θ ≤ a)
    {E : Set Plane} (K : StarShapedKakeya E) {rho : ℝ} (hrho : 0 < rho)
    (hzero : ∀ theta ∈ F.residual,
      (K.needleFamily theta).height K.center = 0)
    (hheight : ∀ θ, height θ = (K.needleFamily θ).height K.center)
    (hpos : ∀ i, 0 < height (F.selected i))
    (hscaled : ∀ i, height (F.selected i) < m * rho)
    (hH : ∀ i, H (F.selected i) =
      Real.arcsin (height (F.selected i) / (m * rho)))
    (hout : ∀ θ ∈ A, (K.needleFamily θ).OutsideBall rho K.center) :
    ENNReal.ofReal (rho ^ 2 / 2) * directionAngleOuter F.residual +
        ∑' i : Fin F.N,
          volume ((K.needleFamily (F.selected i)).triangleInterior K.center) ≤
      volume.toOuterMeasure E := by
  have hfan := K.residualFan_outerMeasure_lower hrho F.residual hzero
    (fun theta htheta => hout theta (F.residual_subset_initial htheta))
  have hpair := F.pairwise_disjoint_triangles hm0 hm1 hbound K hrho hheight
    hpos hscaled hH hout
  have hdisjoint := F.disjoint_residualFan_selectedTriangleUnion hm0 hm1 hbound
    K hrho hzero hheight hpos hscaled hH hout
  have hadd : volume.toOuterMeasure (residualFan K F.residual) +
      volume (F.selectedTriangleUnion K) ≤ volume.toOuterMeasure E :=
    outerMeasure_add_le_of_disjoint_measurable
      (F.measurableSet_selectedTriangleUnion K) hdisjoint
      (K.residualFan_subset F.residual) (F.selectedTriangleUnion_subset K)
  calc
    _ = ENNReal.ofReal (rho ^ 2 / 2) * directionAngleOuter F.residual +
        volume (F.selectedTriangleUnion K) := by rw [F.volume_selectedTriangleUnion K hpair]
    _ ≤ volume.toOuterMeasure (residualFan K F.residual) +
        volume (F.selectedTriangleUnion K) := add_le_add hfan le_rfl
    _ ≤ volume.toOuterMeasure E := hadd

theorem initial_cover (F : FiniteFixedSelection height H m A) :
    A ⊆ F.residual ∪ ⋃ i : Fin F.N,
      fixedDeletionBall (F.selected i) (H (F.selected i)) := by
  intro theta htheta
  by_cases hr : theta ∈ F.residual
  · exact Or.inl hr
  · right
    by_contra hu
    simp only [mem_iUnion, not_exists] at hu
    have hremain : ∀ n, n ≤ F.N → theta ∈ fixedGreedyRemaining height H m A n := by
      intro n hn
      induction n with
      | zero => exact htheta
      | succ n ih =>
          rw [fixedGreedyRemaining_succ]
          refine ⟨ih (Nat.le_trans (Nat.le_succ n) hn), ?_⟩
          simpa [F.selected_eq ⟨n, Nat.lt_of_succ_le hn⟩] using
            hu ⟨n, Nat.lt_of_succ_le hn⟩
    exact hr (F.residual_eq.symm ▸ hremain F.N le_rfl)

theorem initial_directionAngleOuter_le_residual_add_cost
    (F : FiniteFixedSelection height H m A) (hH0 : ∀ i, 0 ≤ H (F.selected i)) :
    directionAngleOuter A ≤ directionAngleOuter F.residual +
      ∑' i : Fin F.N, ENNReal.ofReal (4 * H (F.selected i)) := by
  calc
    directionAngleOuter A ≤ directionAngleOuter (F.residual ∪ ⋃ i : Fin F.N,
        fixedDeletionBall (F.selected i) (H (F.selected i))) := measure_mono F.initial_cover
    _ ≤ directionAngleOuter F.residual + directionAngleOuter (⋃ i : Fin F.N,
        fixedDeletionBall (F.selected i) (H (F.selected i))) := measure_union_le _ _
    _ ≤ directionAngleOuter F.residual + ∑' i : Fin F.N,
        directionAngleOuter (fixedDeletionBall (F.selected i) (H (F.selected i))) :=
      add_le_add le_rfl
        (measure_iUnion_le
          (fun i : Fin F.N => fixedDeletionBall (F.selected i) (H (F.selected i))))
    _ ≤ directionAngleOuter F.residual + ∑' i : Fin F.N,
        ENNReal.ofReal (4 * H (F.selected i)) :=
      add_le_add le_rfl
        (ENNReal.tsum_le_tsum fun i => directionAngleOuter_fixedDeletionBall_le (hH0 i))

end FiniteFixedSelection

/-- Exact negative control: approximate-sup selection does **not** imply future
scaled weights decrease.  Here `m=9/10`, current height `91/100`, and a future
height `1` satisfy `m*future < current`, but the corresponding scaled `arcsin`
weight is larger in the future (take `rho=2`). -/
theorem approximate_sup_does_not_force_future_H_decrease :
    let m : ℝ := 9 / 10
    let rho : ℝ := 2
    let current : ℝ := 91 / 100
    let future : ℝ := 1
    m * future < current ∧
      Real.arcsin (current / (m * rho)) < Real.arcsin (future / (m * rho)) := by
  dsimp
  constructor
  · norm_num
  · apply Real.arcsin_lt_arcsin <;> norm_num

/-- Finiteness of the ENNReal deletion-cost sum is exactly what is needed to
obtain a real summable weight sequence.  This closes the `B < ∞` gap (and avoids
using `ENNReal.toReal ⊤`). -/
theorem summable_of_cost_tsum_ne_top {H : ℕ → ℝ}
    (hH0 : ∀ n, 0 ≤ H n)
    (hB : (∑' n, ENNReal.ofReal (4 * H n)) ≠ ⊤) : Summable H := by
  have hs4 : Summable (fun n => 4 * H n) := by
    have hs := ENNReal.summable_toReal hB
    have heq : (fun n => (ENNReal.ofReal (4 * H n)).toReal) =
        (fun n => 4 * H n) := by
      funext n
      rw [ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (hH0 n))]
    rwa [heq] at hs
  have hsquarter := Summable.mul_left (1 / 4 : ℝ) hs4
  convert hsquarter using 1
  funext n
  ring

/-- For the paper weight `H = asin(δ/(mρ))`, the defining equality gives the
precise height estimate used in the residual-zero argument. -/
theorem height_eq_multiplier_rho_sin_paperWeight
    {delta m rho : ℝ} (hm : 0 < m) (hrho : 0 < rho)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ m * rho) :
    delta = m * rho * Real.sin (Real.arcsin (delta / (m * rho))) := by
  have hden : 0 < m * rho := mul_pos hm hrho
  rw [Real.sin_arcsin (by
    have := div_nonneg hdelta0 hden.le
    linarith) ((div_le_one hden).2 hdelta)]
  field_simp

/-- Finite selected-area payment, indexed only by the directions that were
actually selected. -/
theorem finite_selected_triangle_volume_ge_cost
    {ι : Type*} [Fintype ι] {o : Plane} {needle : ι → UnitNeedle}
    {H : ι → ℝ} {c kappa : ℝ}
    (hc : 0 ≤ c) (hk : 0 ≤ kappa)
    (hpay : ∀ i, c * kappa * H i ≤ (needle i).height o / 2) :
    ENNReal.ofReal (c * kappa / 4) *
        (∑' i, ENNReal.ofReal (4 * H i)) ≤
      ∑' i, volume ((needle i).triangleInterior o) := by
  rw [show (fun i => volume ((needle i).triangleInterior o)) =
      (fun i => ENNReal.ofReal ((needle i).height o / 2)) by
    funext i
    exact UnitNeedle.volume_triangleInterior o (needle i)]
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro i
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ c * kappa / 4)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [hpay i]

/-- Fully instantiated paper-weight payment for a genuine finite selection. -/
theorem finite_paperWeight_payment
    {ι : Type*} [Fintype ι] {o : Plane} {needle : ι → UnitNeedle}
    {eps a rho : ℝ}
    (heps0 : 0 < eps) (heps1 : eps < 1)
    (ha : 0 < a) (harho : a < rho)
    (hh0 : ∀ i, 0 ≤ (needle i).height o)
    (hha : ∀ i, (needle i).height o ≤ a)
    (hscaled : ∀ i, (needle i).height o ≤ (1 - eps) * rho) :
    ENNReal.ofReal (caseIIC a rho * caseIIKappa eps / 4) *
        (∑' i, ENNReal.ofReal
          (4 * caseIIPaperWeight eps rho ((needle i).height o))) ≤
      ∑' i, volume ((needle i).triangleInterior o) := by
  apply finite_selected_triangle_volume_ge_cost
    (caseIIC_pos ha harho).le (caseIIKappa_nonneg heps1.le)
  intro i
  exact caseII_paperWeight_paid_by_height heps0 heps1 ha harho
    (hh0 i) (hha i) (hscaled i)

/-- Countable selected-area payment.  Combined with
`UnitNeedle.volume_triangleInterior`, this turns the pointwise ROUND-2 estimate
`|Δ_n| ≥ c κ H_n` into the required sum estimate. -/
theorem tsum_selected_area_ge_cost
    {area H : ℕ → ℝ} {c kappa : ℝ}
    (hc : 0 ≤ c) (hk : 0 ≤ kappa)
    (harea : ∀ n, c * kappa * H n ≤ area n) :
    ENNReal.ofReal (c * kappa / 4) *
        (∑' n, ENNReal.ofReal (4 * H n)) ≤
      ∑' n, ENNReal.ofReal (area n) := by
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro n
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ c * kappa / 4)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [harea n]

/-- `tsum_selected_area_ge_cost` with the abstract `area` replaced by the
actual open-triangle volume. -/
theorem tsum_selected_triangle_volume_ge_cost
    {o : Plane} {needle : ℕ → UnitNeedle} {H : ℕ → ℝ} {c kappa : ℝ}
    (hc : 0 ≤ c) (hk : 0 ≤ kappa)
    (hpay : ∀ n, c * kappa * H n ≤ (needle n).height o / 2) :
    ENNReal.ofReal (c * kappa / 4) *
        (∑' n, ENNReal.ofReal (4 * H n)) ≤
      ∑' n, volume ((needle n).triangleInterior o) := by
  rw [show (fun n => volume ((needle n).triangleInterior o)) =
      (fun n => ENNReal.ofReal ((needle n).height o / 2)) by
    funext n
    exact UnitNeedle.volume_triangleInterior o (needle n)]
  exact tsum_selected_area_ge_cost hc hk hpay

/-- Fully instantiated paper-weight payment.  No `area` sequence is supplied by
the caller: both the weight and every summand are the concrete needle data. -/
theorem paperWeight_payment_tsum
    {o : Plane} {needle : ℕ → UnitNeedle} {eps a rho : ℝ}
    (heps0 : 0 < eps) (heps1 : eps < 1)
    (ha : 0 < a) (harho : a < rho)
    (hh0 : ∀ n, 0 ≤ (needle n).height o)
    (hha : ∀ n, (needle n).height o ≤ a)
    (hscaled : ∀ n, (needle n).height o ≤ (1 - eps) * rho) :
    ENNReal.ofReal (caseIIC a rho * caseIIKappa eps / 4) *
        (∑' n, ENNReal.ofReal
          (4 * caseIIPaperWeight eps rho ((needle n).height o))) ≤
      ∑' n, volume ((needle n).triangleInterior o) := by
  apply tsum_selected_triangle_volume_ge_cost
    (caseIIC_pos ha harho).le (caseIIKappa_nonneg heps1.le)
  intro n
  exact caseII_paperWeight_paid_by_height heps0 heps1 ha harho
    (hh0 n) (hha n) (hscaled n)

/-- ROUND-2 minimax in outer-measure form. `B = Σ 4H_n`, `q = cκ/4`,
`R` is residual angle and `b` is selected area.  Since this is an `ENNReal`
statement, the ambient-infinite branch is included automatically. -/
theorem caseII_round2_initial_angle_lower_bound
    {q s L R B b M : ENNReal}
    (hq_le_s : q ≤ s) (hcover : L ≤ R + B)
    (hpayment : q * B ≤ b) (hgeom : s * R + b ≤ M) :
    q * L ≤ M := by
  calc
    q * L ≤ q * (R + B) := mul_le_mul_left' hcover q
    _ = q * R + q * B := mul_add q R B
    _ ≤ s * R + b := add_le_add (mul_le_mul_right' hq_le_s R) hpayment
    _ ≤ M := hgeom

/-- In the `B=∞` branch, positive selected-area payment forces the ambient
outer measure to be infinite. -/
theorem caseII_round2_infinite_cost_forces_top
    {q B b M : ENNReal} (hq : q ≠ 0) (hB : B = ⊤)
    (hpayment : q * B ≤ b) (hbM : b ≤ M) : M = ⊤ := by
  have hb : b = ⊤ := by
    apply top_unique
    simpa [hB, ENNReal.mul_top, hq] using hpayment
  exact top_unique (hb ▸ hbM)

/-- The `outerMeasure E = ∞` branch of every Case-II lower bound is automatic.
Keeping it explicit prevents accidental use of `ENNReal.toReal ⊤ = 0`. -/
theorem caseII_lower_bound_of_outerMeasure_eq_top
    {E : Set Plane} {q : ℝ} {L : ENNReal}
    (hE : volume.toOuterMeasure E = ⊤) :
    ENNReal.ofReal q * L ≤ volume.toOuterMeasure E := by
  rw [hE]
  exact le_top

/-- Complete fixed-ball Case-II selection theorem.  The finite/infinite object is
constructed here by `fixedSelectionOutcome`; callers do not supply a selection
or a prepackaged final inequality. -/
theorem caseII_fixed_greedy_lower_bound
    {E : Set Plane} (K : StarShapedKakeya E) (A : Set Direction)
    {eps a rho : ℝ}
    (heps0 : 0 < eps) (heps1 : eps < 1)
    (ha : 0 < a) (harho : a < rho)
    (harhoScaled : a < (1 - eps) * rho)
    (hrhoHalf : 1 / 2 < rho) (hrhoOne : rho ≤ 1)
    (hout : ∀ theta ∈ A,
      (K.needleFamily theta).OutsideBall rho K.center)
    (hlow : ∀ theta ∈ A, (K.needleFamily theta).height K.center < a) :
    ENNReal.ofReal (caseIIC a rho * caseIIKappa eps / 4) * directionAngleOuter A ≤
      volume.toOuterMeasure E := by
  let height : Direction → ℝ := fun theta =>
    (K.needleFamily theta).height K.center
  let m : ℝ := 1 - eps
  let H : Direction → ℝ := fun theta => caseIIPaperWeight eps rho (height theta)
  have hm0 : 0 < m := by dsimp [m]; linarith
  have hm1 : m < 1 := by dsimp [m]; linarith
  have hrho : 0 < rho := by linarith
  have hheight0 : ∀ theta, 0 ≤ height theta := by
    intro theta
    dsimp [height]
    exact UnitNeedle.height_nonneg _ _
  have hbound : ∀ theta ∈ A, height theta ≤ a := fun theta htheta =>
    (hlow theta htheta).le
  have hscaledA : ∀ theta ∈ A, height theta < m * rho := fun theta htheta =>
    (hlow theta htheta).trans (by simpa [m] using harhoScaled)
  have hH_eq : ∀ theta, H theta = Real.arcsin (height theta / (m * rho)) := by
    intro theta
    rfl
  have hq_le_s : ENNReal.ofReal (caseIIC a rho * caseIIKappa eps / 4) ≤
      ENNReal.ofReal (rho ^ 2 / 2) := by
    apply ENNReal.ofReal_le_ofReal
    have hc := caseIIC_lt_half_rho ha harho
    have hk0 := (caseIIKappa_pos heps0 heps1).le
    have hk1 := (caseIIKappa_lt_one heps0).le
    have hc0 := (caseIIC_pos ha harho).le
    nlinarith
  cases fixedSelectionOutcome height H m A hheight0 hbound with
  | finite F =>
      have hmem : ∀ i, F.selected i ∈ A :=
        fun i => F.selected_mem_initial hm0 hm1 hbound i
      have hpos : ∀ i, 0 < height (F.selected i) := by
        intro i
        have hd := chooseAbove_dominates hm0 hm1
          (fixedGreedyRemaining_subset height H m A i) hbound
          (F.positive_before i) (F.selected_mem hm0 hm1 hbound i)
        have heq : chooseAbove height m (fixedGreedyRemaining height H m A i) =
            F.selected i := by
          rw [F.selected_eq i]
          rfl
        rw [heq] at hd
        nlinarith [hheight0 (F.selected i)]
      have hscaled : ∀ i, height (F.selected i) < m * rho :=
        fun i => hscaledA _ (hmem i)
      have hzeroHeight := F.residual_height_zero hheight0 hbound
      have hzero : ∀ theta ∈ F.residual,
          (K.needleFamily theta).height K.center = 0 := by
        simpa [height] using hzeroHeight
      have hH0 : ∀ i, 0 ≤ H (F.selected i) := by
        intro i
        rw [hH_eq]
        exact Real.arcsin_nonneg.2 (div_nonneg (hheight0 _)
          (mul_pos hm0 hrho).le)
      have hcover := F.initial_directionAngleOuter_le_residual_add_cost hH0
      have hpayment : ENNReal.ofReal
            (caseIIC a rho * caseIIKappa eps / 4) *
            (∑' i : Fin F.N, ENNReal.ofReal (4 * H (F.selected i))) ≤
          ∑' i : Fin F.N,
            volume ((K.needleFamily (F.selected i)).triangleInterior K.center) := by
        simpa [H, height] using finite_paperWeight_payment
          (ι := Fin F.N) (o := K.center)
          (needle := fun i => K.needleFamily (F.selected i))
          heps0 heps1 ha harho
          (fun i => hheight0 _) (fun i => hbound _ (hmem i))
          (fun i => (hscaled i).le)
      have hgeom := F.geometric_outerMeasure_lower hm0 hm1 hbound K hrho
        hzero (fun _ => rfl) hpos hscaled (fun i => hH_eq _) hout
      exact caseII_round2_initial_angle_lower_bound hq_le_s hcover hpayment hgeom
  | infinite hpositive =>
      let G : FixedDeletionGreedyData height H := infiniteGreedyData hm0 hm1 hbound
        hpositive (fun n => directionAngleOuter_fixedDeletionBall_le (by
          rw [hH_eq]
          exact Real.arcsin_nonneg.2 (div_nonneg (hheight0 _)
            (mul_pos hm0 hrho).le)))
      have hmem : ∀ n, G.selected n ∈ A := fun n =>
        G.remaining_subset_initial n (G.selected_mem n)
      have hpos : ∀ n, 0 < height (G.selected n) := by
        intro n
        have hd := G.dominates n (G.selected n) (G.selected_mem n)
        change m * height (G.selected n) < height (G.selected n) at hd
        nlinarith [hheight0 (G.selected n)]
      have hscaled : ∀ n, height (G.selected n) < G.multiplier * rho := by
        intro n
        change height (G.selected n) < m * rho
        exact hscaledA _ (hmem n)
      have hHG : ∀ n, H (G.selected n) =
          Real.arcsin (height (G.selected n) / (G.multiplier * rho)) := by
        intro n
        change H (G.selected n) = Real.arcsin (height (G.selected n) / (m * rho))
        exact hH_eq _
      let B : ENNReal := ∑' n, ENNReal.ofReal (4 * H (G.selected n))
      let b : ENNReal := ∑' n,
        volume ((K.needleFamily (G.selected n)).triangleInterior K.center)
      have hpayment : ENNReal.ofReal
            (caseIIC a rho * caseIIKappa eps / 4) * B ≤ b := by
        simpa [B, b, H, height] using paperWeight_payment_tsum
          (o := K.center) (needle := fun n => K.needleFamily (G.selected n))
          heps0 heps1 ha harho
          (fun n => hheight0 _) (fun n => hbound _ (hmem n))
          (fun n => (hscaledA _ (hmem n)).le)
      by_cases hB : B = ⊤
      · have hbM : b ≤ volume.toOuterMeasure E := by
          dsimp [b]
          exact G.selected_triangle_volume_le_outer K hrho (fun _ => rfl)
            hpos hscaled hHG hout
        have hq : ENNReal.ofReal
            (caseIIC a rho * caseIIKappa eps / 4) ≠ 0 := by
          exact (ENNReal.ofReal_pos.2 (div_pos
            (mul_pos (caseIIC_pos ha harho) (caseIIKappa_pos heps0 heps1))
            (by norm_num))).ne'
        have htop := caseII_round2_infinite_cost_forces_top hq hB hpayment hbM
        rw [htop]
        exact le_top
      · have hsum : Summable (fun n => H (G.selected n)) := by
          apply summable_of_cost_tsum_ne_top
          · intro n
            rw [hHG]
            exact Real.arcsin_nonneg.2 (div_nonneg (hheight0 _)
              (mul_pos hm0 hrho).le)
          · simpa [B] using hB
        have hheight_le_H : ∀ n, height (G.selected n) ≤ H (G.selected n) := by
          intro n
          have hdelta := height_eq_multiplier_rho_sin_paperWeight hm0 hrho
            (hheight0 _) (hscaled n).le
          rw [← hH_eq] at hdelta
          have hH0 : 0 ≤ H (G.selected n) := by
            rw [hHG]
            exact Real.arcsin_nonneg.2 (div_nonneg (hheight0 _)
              (mul_pos hm0 hrho).le)
          have hmrho : m * rho ≤ 1 := by
            have hmle : m ≤ 1 := hm1.le
            nlinarith
          rw [hdelta]
          have hsin := Real.sin_le hH0
          have hsin0 : 0 ≤ Real.sin (H (G.selected n)) := by
            have harg0 : -1 ≤ height (G.selected n) / (m * rho) := by
              have hn := div_nonneg (hheight0 (G.selected n)) (mul_pos hm0 hrho).le
              linarith
            have harg1 : height (G.selected n) / (m * rho) ≤ 1 :=
              (div_le_one (mul_pos hm0 hrho)).2 (hscaledA _ (hmem n)).le
            rw [hH_eq, Real.sin_arcsin harg0 harg1]
            exact div_nonneg (hheight0 (G.selected n)) (mul_pos hm0 hrho).le
          nlinarith
        have hzeroHeight := G.residual_height_zero_of_summable_cost hheight0
          hheight_le_H hsum
        have hzero : ∀ theta ∈ greedyResidual G.remaining,
            (K.needleFamily theta).height K.center = 0 := by
          simpa [height] using hzeroHeight
        have hcover := G.initial_directionAngleOuter_le_residual_add_cost
        have hgeom := G.geometric_outerMeasure_lower K hrho hzero hout
          (fun _ => rfl) hpos hscaled hHG
        exact caseII_round2_initial_angle_lower_bound hq_le_s
          (by simpa [B] using hcover) hpayment (by simpa [b] using hgeom)

/-- Paper radius-`A_out` specialization.  The no-high premise supplies low
height, while radius membership itself supplies `OutsideBall (R₁ - 1)` via the
radial structure of `triangleHull`; callers supply no outside-ball premise. -/
theorem caseII_A_out_fixed_greedy_lower_bound
    {E : Set Plane} (K : StarShapedKakeya E) {eps a R₁ : ℝ}
    (heps0 : 0 < eps) (heps1 : eps < 1)
    (ha : 0 < a) (harho : a < R₁ - 1)
    (harhoScaled : a < (1 - eps) * (R₁ - 1))
    (hrhoHalf : 1 / 2 < R₁ - 1) (hrhoOne : R₁ - 1 ≤ 1)
    (hhigh : ¬ ∃ theta : Direction,
      a ≤ (K.needleFamily theta).height K.center) :
    ENNReal.ofReal (caseIIC a (R₁ - 1) * caseIIKappa eps / 4) *
        directionAngleOuter (K.A_out_radius R₁) ≤ volume.toOuterMeasure E := by
  apply caseII_fixed_greedy_lower_bound K (K.A_out_radius R₁)
    heps0 heps1 ha harho harhoScaled hrhoHalf hrhoOne
  · intro theta htheta
    exact (K.needleFamily theta).outsideBall_sub_one_of_not_triangleHull_subset_closedBall
      (by linarith) htheta
  · intro theta _
    exact lt_of_not_ge (fun h => hhigh ⟨theta, h⟩)

end

end StarKakeyaLower
