import StarKakeyaLower.LiGeometry

/-!
# Endpoint-capacity unit-chord geometry

The first geometry layer for the finite radial-schedule lower bound.  A unit
chord on a support line is parametrised by

`supportPoint α δ x`,  `x ∈ [c - 1/2, c + 1/2]`.

This module identifies the point of minimum squared radius and proves that the
larger endpoint squared radius exceeds that minimum by at least `1/4`.
No selector, measurability, or schedule hypothesis appears here.
-/

open Set

namespace StarKakeyaLower

noncomputable section

/-- Signed tangential coordinate of the closest point of the unit chord to the
origin.  This is the metric projection of zero onto
`[c - 1/2, c + 1/2]`. -/
def unitChordNearestParameter (c : ℝ) : ℝ :=
  if 0 < c - 1 / 2 then c - 1 / 2
  else if c + 1 / 2 < 0 then c + 1 / 2
  else 0

/-- The closest parameter belongs to the unit-chord parameter interval. -/
theorem unitChordNearestParameter_mem (c : ℝ) :
    unitChordNearestParameter c ∈ Icc (c - 1 / 2) (c + 1 / 2) := by
  dsimp [unitChordNearestParameter]
  split_ifs with hlo hhi
  · constructor <;> linarith
  · constructor <;> linarith
  · constructor <;> linarith

/-- The selected parameter minimises the squared tangential coordinate. -/
theorem unitChordNearestParameter_sq_le {c x : ℝ}
    (hx : x ∈ Icc (c - 1 / 2) (c + 1 / 2)) :
    unitChordNearestParameter c ^ 2 ≤ x ^ 2 := by
  by_cases hlo : 0 < c - 1 / 2
  · rw [unitChordNearestParameter, if_pos hlo]
    nlinarith [hx.1]
  · rw [unitChordNearestParameter, if_neg hlo]
    by_cases hhi : c + 1 / 2 < 0
    · rw [if_pos hhi]
      nlinarith [hx.2]
    · rw [if_neg hhi]
      simpa using sq_nonneg x

/-- The chosen support-line point realises the minimum squared radius along the
whole unit chord. -/
theorem unitChordNearestParameter_realizes_minimum (α δ c : ℝ) :
    IsLeast
      (planeNormSq ∘ supportPoint α δ '' Icc (c - 1 / 2) (c + 1 / 2))
      (planeNormSq (supportPoint α δ (unitChordNearestParameter c))) := by
  constructor
  · exact ⟨unitChordNearestParameter c, unitChordNearestParameter_mem c, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    simp only [Function.comp_apply, planeNormSq_supportPoint]
    nlinarith [unitChordNearestParameter_sq_le hx]

/-- **Unit-chord radial gap.**  The larger endpoint squared radius exceeds the
minimum squared radius along the chord by at least `1/4`.

This is the coordinate core of the paper inequality `M² ≥ m² + 1/4`; the bridge
to extrema of an arbitrary physical `UnitNeedle` is deliberately a later
module. -/
theorem unitChord_max_endpoint_sq_ge_min_add_quarter (α δ c : ℝ) :
    max
        (planeNormSq (supportPoint α δ (c - 1 / 2)))
        (planeNormSq (supportPoint α δ (c + 1 / 2)))
      ≥ planeNormSq (supportPoint α δ (unitChordNearestParameter c)) + 1 / 4 := by
  simp only [planeNormSq_supportPoint]
  by_cases hlo : 0 < c - 1 / 2
  · rw [unitChordNearestParameter, if_pos hlo]
    apply le_max_of_le_right
    nlinarith
  · rw [unitChordNearestParameter, if_neg hlo]
    by_cases hhi : c + 1 / 2 < 0
    · rw [if_pos hhi]
      apply le_max_of_le_left
      nlinarith
    · rw [if_neg hhi]
      by_cases hc : 0 ≤ c
      · apply le_max_of_le_right
        nlinarith
      · apply le_max_of_le_left
        nlinarith

end

end StarKakeyaLower
