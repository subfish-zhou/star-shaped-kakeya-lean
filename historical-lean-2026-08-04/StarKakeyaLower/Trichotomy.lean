import StarKakeyaLower.TriangleArea

/-!
# Outer-measure direction trichotomy

The direction sets in this file need not be measurable.  All their sizes are
therefore taken with `volume.toOuterMeasure`.  The proof uses only coverage of
the direction circle, monotonicity, and finite subadditivity; in particular it
does not silently replace outer measure by measure on either branch.
-/

open Set MeasureTheory

namespace StarKakeyaLower

noncomputable section

namespace UnitNeedle

/-- Whether the perpendicular projection of `o` lies in the closed unit base.
This coordinate condition is orientation-independent (reversing the endpoints
replaces the scalar coordinate by `1 - t`). -/
def projectionInside (o : Plane) (n : UnitNeedle) : Prop :=
  let d := n.right - n.left
  let v := o - n.left
  0 ≤ d 0 * v 0 + d 1 * v 1 ∧
    d 0 * v 0 + d 1 * v 1 ≤ 1

end UnitNeedle

namespace StarShapedKakeya

variable {E : Set Plane} (K : StarShapedKakeya E)

/-- Low-height directions whose perpendicular foot is in the needle. -/
def A_in (a : ℝ) : Set Direction :=
  {θ | (K.needleFamily θ).height K.center < a ∧
    (K.needleFamily θ).projectionInside K.center}

/-- Low-height directions whose perpendicular foot is outside the needle. -/
def A_out (a : ℝ) : Set Direction :=
  {θ | (K.needleFamily θ).height K.center < a ∧
    ¬(K.needleFamily θ).projectionInside K.center}

/-! The preceding projection split is retained for the local coordinate
arguments which use it.  The split in the paper, however, is the following
literal radius split of the complete filled triangles. -/

/-- Paper Case I directions: the complete chosen triangle is in the radius
`R` closed ball.  No measurability of this set is asserted or needed. -/
def A_in_radius (R : ℝ) : Set Direction :=
  {θ | (K.needleFamily θ).triangleHull K.center ⊆ Metric.closedBall K.center R}

/-- Paper Case II directions, definitionally the set-theoretic complement of
`A_in_radius`. -/
def A_out_radius (R : ℝ) : Set Direction :=
  (K.A_in_radius R)ᶜ

/-- Outer Haar measure on the unoriented direction circle. -/
def directionOuterMeasure (s : Set Direction) : ENNReal :=
  volume.toOuterMeasure s

@[simp] theorem directionOuterMeasure_univ :
    directionOuterMeasure (Set.univ : Set Direction) = ENNReal.ofReal Real.pi := by
  simp [directionOuterMeasure, AddCircle.measure_univ]

/-- If no chosen triangle reaches height `a`, the two low-height direction sets
cover the entire direction circle. -/
theorem univ_subset_A_in_union_A_out_of_no_high {a : ℝ}
    (hhigh : ¬ ∃ θ : Direction, a ≤ (K.needleFamily θ).height K.center) :
    (Set.univ : Set Direction) ⊆ K.A_in a ∪ K.A_out a := by
  intro θ _
  have hh : (K.needleFamily θ).height K.center < a := by
    exact lt_of_not_ge (fun h => hhigh ⟨θ, h⟩)
  by_cases hin : (K.needleFamily θ).projectionInside K.center
  · exact Or.inl ⟨hh, hin⟩
  · exact Or.inr ⟨hh, hin⟩

/-- Under the no-high hypothesis used at the paper split, every direction is
in exactly one of the two radius classes.  (The coverage itself is tautological;
the hypothesis is retained because it supplies low height in Case II.) -/
theorem univ_subset_A_in_radius_union_A_out_radius_of_no_high {a R : ℝ}
    (_hhigh : ¬ ∃ θ : Direction, a ≤ (K.needleFamily θ).height K.center) :
    (Set.univ : Set Direction) ⊆ K.A_in_radius R ∪ K.A_out_radius R := by
  intro θ _
  by_cases hin : (K.needleFamily θ).triangleHull K.center ⊆
      Metric.closedBall K.center R
  · exact Or.inl hin
  · exact Or.inr hin

/-- The paper radius classes are disjoint. -/
theorem disjoint_A_in_radius_A_out_radius (R : ℝ) :
    Disjoint (K.A_in_radius R) (K.A_out_radius R) := by
  rw [Set.disjoint_left]
  exact fun _ hin hout => hout hin

/-- The universal three-way split.  The parameter assumptions are exactly what
is needed to divide the circle length as `pπ + (1-p)π = π`.

Both direction alternatives are outer-measure statements, so this remains
valid when `A_in` and `A_out` are nonmeasurable.  Notice also that negating each
`≥` branch produces a strict `<`; those two strict inequalities are what
contradict outer-measure subadditivity. -/
theorem direction_trichotomy (a p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∃ θ : Direction, a ≤ (K.needleFamily θ).height K.center) ∨
    ENNReal.ofReal (p * Real.pi) ≤ directionOuterMeasure (K.A_in a) ∨
    ENNReal.ofReal ((1 - p) * Real.pi) ≤ directionOuterMeasure (K.A_out a) := by
  by_cases hhigh : ∃ θ : Direction, a ≤ (K.needleFamily θ).height K.center
  · exact Or.inl hhigh
  right
  by_cases hin : ENNReal.ofReal (p * Real.pi) ≤ directionOuterMeasure (K.A_in a)
  · exact Or.inl hin
  right
  by_contra hout
  have hin_lt : directionOuterMeasure (K.A_in a) <
      ENNReal.ofReal (p * Real.pi) := lt_of_not_ge hin
  have hout_lt : directionOuterMeasure (K.A_out a) <
      ENNReal.ofReal ((1 - p) * Real.pi) := lt_of_not_ge hout
  have hcover := K.univ_subset_A_in_union_A_out_of_no_high hhigh
  have hsub : directionOuterMeasure (Set.univ : Set Direction) ≤
      directionOuterMeasure (K.A_in a) + directionOuterMeasure (K.A_out a) := by
    calc
      directionOuterMeasure (Set.univ : Set Direction) ≤
          directionOuterMeasure (K.A_in a ∪ K.A_out a) :=
        measure_mono hcover
      _ ≤ directionOuterMeasure (K.A_in a) + directionOuterMeasure (K.A_out a) :=
        measure_union_le _ _
  have hstrict : directionOuterMeasure (K.A_in a) +
      directionOuterMeasure (K.A_out a) < ENNReal.ofReal Real.pi := by
    calc
      directionOuterMeasure (K.A_in a) + directionOuterMeasure (K.A_out a) <
          ENNReal.ofReal (p * Real.pi) + ENNReal.ofReal ((1 - p) * Real.pi) :=
        ENNReal.add_lt_add hin_lt hout_lt
      _ = ENNReal.ofReal Real.pi := by
        rw [← ENNReal.ofReal_add (mul_nonneg hp0 Real.pi_pos.le)
          (mul_nonneg (sub_nonneg.mpr hp1) Real.pi_pos.le)]
        congr 1
        ring
  rw [directionOuterMeasure_univ] at hsub
  exact (not_lt_of_ge hsub) hstrict

/-- The actual paper trichotomy, using containment of the complete triangle in
the radius-`R` ball rather than the auxiliary projection split.  Outer measure
is used throughout, so neither radius class is required to be measurable. -/
theorem direction_radius_trichotomy (a R p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∃ θ : Direction, a ≤ (K.needleFamily θ).height K.center) ∨
    ENNReal.ofReal (p * Real.pi) ≤ directionOuterMeasure (K.A_in_radius R) ∨
    ENNReal.ofReal ((1 - p) * Real.pi) ≤
      directionOuterMeasure (K.A_out_radius R) := by
  by_cases hhigh : ∃ θ : Direction, a ≤ (K.needleFamily θ).height K.center
  · exact Or.inl hhigh
  right
  by_cases hin : ENNReal.ofReal (p * Real.pi) ≤
      directionOuterMeasure (K.A_in_radius R)
  · exact Or.inl hin
  right
  by_contra hout
  have hin_lt : directionOuterMeasure (K.A_in_radius R) <
      ENNReal.ofReal (p * Real.pi) := lt_of_not_ge hin
  have hout_lt : directionOuterMeasure (K.A_out_radius R) <
      ENNReal.ofReal ((1 - p) * Real.pi) := lt_of_not_ge hout
  have hcover := K.univ_subset_A_in_radius_union_A_out_radius_of_no_high
    (R := R) hhigh
  have hsub : directionOuterMeasure (Set.univ : Set Direction) ≤
      directionOuterMeasure (K.A_in_radius R) +
        directionOuterMeasure (K.A_out_radius R) := by
    calc
      directionOuterMeasure (Set.univ : Set Direction) ≤
          directionOuterMeasure (K.A_in_radius R ∪ K.A_out_radius R) :=
        measure_mono hcover
      _ ≤ directionOuterMeasure (K.A_in_radius R) +
          directionOuterMeasure (K.A_out_radius R) := measure_union_le _ _
  have hstrict : directionOuterMeasure (K.A_in_radius R) +
      directionOuterMeasure (K.A_out_radius R) < ENNReal.ofReal Real.pi := by
    calc
      _ < ENNReal.ofReal (p * Real.pi) +
          ENNReal.ofReal ((1 - p) * Real.pi) :=
        ENNReal.add_lt_add hin_lt hout_lt
      _ = ENNReal.ofReal Real.pi := by
        rw [← ENNReal.ofReal_add (mul_nonneg hp0 Real.pi_pos.le)
          (mul_nonneg (sub_nonneg.mpr hp1) Real.pi_pos.le)]
        congr 1
        ring
  rw [directionOuterMeasure_univ] at hsub
  exact (not_lt_of_ge hsub) hstrict

/-- High-triangle branch converted unconditionally to an outer-area lower bound. -/
theorem high_branch_outerMeasure
    {a : ℝ} (hhigh : ∃ θ : Direction, a ≤ (K.needleFamily θ).height K.center) :
    ENNReal.ofReal (a / 2) ≤ volume.toOuterMeasure E := by
  obtain ⟨θ, hθ⟩ := hhigh
  exact K.outerMeasure_ge_half_of_height StarKakeyaLower.triangleAreaBridge hθ

/-- The area-valued entry point used by later lower-bound arguments.  It does
not mention, and hence does not assume, any later `Li` or Case-II estimate. -/
theorem outerMeasure_direction_trichotomy
    (a p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ENNReal.ofReal (a / 2) ≤ volume.toOuterMeasure E ∨
    ENNReal.ofReal (p * Real.pi) ≤ directionOuterMeasure (K.A_in a) ∨
    ENNReal.ofReal ((1 - p) * Real.pi) ≤ directionOuterMeasure (K.A_out a) := by
  rcases K.direction_trichotomy a p hp0 hp1 with hhigh | hin | hout
  · exact Or.inl (K.high_branch_outerMeasure hhigh)
  · exact Or.inr (Or.inl hin)
  · exact Or.inr (Or.inr hout)

/-- Area-valued paper entry point for the radius split. -/
theorem outerMeasure_direction_radius_trichotomy
    (a R p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ENNReal.ofReal (a / 2) ≤ volume.toOuterMeasure E ∨
    ENNReal.ofReal (p * Real.pi) ≤ directionOuterMeasure (K.A_in_radius R) ∨
    ENNReal.ofReal ((1 - p) * Real.pi) ≤
      directionOuterMeasure (K.A_out_radius R) := by
  rcases K.direction_radius_trichotomy a R p hp0 hp1 with hhigh | hin | hout
  · exact Or.inl (K.high_branch_outerMeasure hhigh)
  · exact Or.inr (Or.inl hin)
  · exact Or.inr (Or.inr hout)

end StarShapedKakeya

end

end StarKakeyaLower
