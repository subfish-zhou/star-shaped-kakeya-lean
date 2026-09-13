import StarKakeyaLower.EndpointCapacityNeedleAdapter

/-!
# High closest-radius foot-outside geometry

If the support-line height is below `eta` while the nearest chord radius exceeds
`a ≥ eta`, the perpendicular foot cannot lie in the unit chord.  The farther
endpoint is then one tangential unit beyond the nearer endpoint, yielding the
exact high-tail squared-radius bound.
-/

open Set Real

namespace StarKakeyaLower

noncomputable section

/-- Coordinate form of the high closest-radius estimate. -/
theorem unitChord_high_foot_outside_sq
    {h eta a c : ℝ}
    (hh : 0 ≤ h) (hheta : h < eta) (heta0 : 0 ≤ eta) (hetaa : eta ≤ a)
    (ha : a ^ 2 < h ^ 2 + (unitChordNearestParameter c) ^ 2) :
    a ^ 2 + 1 + 2 * Real.sqrt (a ^ 2 - eta ^ 2) <
      h ^ 2 + max ((c - 1 / 2) ^ 2) ((c + 1 / 2) ^ 2) := by
  have ha0 : 0 ≤ a := le_trans heta0 hetaa
  have heta_sq : eta ^ 2 ≤ a ^ 2 := by nlinarith
  have hh_sq : h ^ 2 < eta ^ 2 := by nlinarith
  have hrad : 0 ≤ a ^ 2 - eta ^ 2 := by nlinarith
  have hsqrt_sq : (Real.sqrt (a ^ 2 - eta ^ 2)) ^ 2 = a ^ 2 - eta ^ 2 :=
    Real.sq_sqrt hrad
  have hsqrt0 : 0 ≤ Real.sqrt (a ^ 2 - eta ^ 2) := Real.sqrt_nonneg _
  have hfoot : 0 ∉ Icc (c - 1 / 2) (c + 1 / 2) := by
    intro hzero
    have hnearest0 : unitChordNearestParameter c = 0 := by
      rw [unitChordNearestParameter]
      split_ifs with hleft
      · nlinarith [hzero.1]
      · nlinarith [hzero.2]
      · rfl
    rw [hnearest0] at ha
    norm_num at ha
    nlinarith
  by_cases hlo : 0 < c - 1 / 2
  · rw [unitChordNearestParameter, if_pos hlo] at ha
    have hsqrt_lt : Real.sqrt (a ^ 2 - eta ^ 2) < c - 1 / 2 := by
      nlinarith
    have hmax : (c + 1 / 2) ^ 2 ≤
        max ((c - 1 / 2) ^ 2) ((c + 1 / 2) ^ 2) := le_max_right _ _
    nlinarith
  · rw [unitChordNearestParameter, if_neg hlo] at ha
    by_cases hhi : c + 1 / 2 < 0
    · rw [if_pos hhi] at ha
      have hsqrt_lt : Real.sqrt (a ^ 2 - eta ^ 2) < -(c + 1 / 2) := by
        nlinarith
      have hmax : (c - 1 / 2) ^ 2 ≤
          max ((c - 1 / 2) ^ 2) ((c + 1 / 2) ^ 2) := le_max_left _ _
      nlinarith
    · rw [if_neg hhi] at ha
      exact (hfoot ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩).elim

/-- `DirectionNeedle` wrapper for the squared high foot-outside estimate. -/
theorem DirectionNeedle.high_foot_outside_sq
    {d : ProjectiveDirection} (N : DirectionNeedle d) {eta a : ℝ}
    (hh : 0 ≤ N.height) (hheta : N.height < eta)
    (heta0 : 0 ≤ eta) (hetaa : eta ≤ a)
    (ha : a ^ 2 < N.nearestRadiusSq) :
    a ^ 2 + 1 + 2 * Real.sqrt (a ^ 2 - eta ^ 2) <
      N.maxEndpointRadiusSq :=
  unitChord_high_foot_outside_sq hh hheta heta0 hetaa ha

end

end StarKakeyaLower
