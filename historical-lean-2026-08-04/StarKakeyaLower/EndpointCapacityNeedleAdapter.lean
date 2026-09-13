import StarKakeyaLower.EndpointCapacitySliverGeometry

/-!
# Endpoint-capacity direction-needle adapter

Field-level wrappers that expose the nearest and farthest squared radii of a
`DirectionNeedle` and apply the coordinate side-selection theorem to its
literal triangle.  This is not yet the projective sliver-family construction.
-/

open Set Real

namespace StarKakeyaLower

noncomputable section

/-- Squared distance of the closest point of the unit chord carried by `N`. -/
def DirectionNeedle.nearestRadiusSq {d : ProjectiveDirection}
    (N : DirectionNeedle d) : ℝ :=
  N.height ^ 2 + (unitChordNearestParameter N.centre) ^ 2

/-- Maximum squared endpoint distance of the unit chord carried by `N`. -/
def DirectionNeedle.maxEndpointRadiusSq {d : ProjectiveDirection}
    (N : DirectionNeedle d) : ℝ :=
  N.height ^ 2 +
    max ((N.centre - 1 / 2) ^ 2) ((N.centre + 1 / 2) ^ 2)

/-- The maximum endpoint radius exceeds the nearest chord radius by at least
`1/4` in squared distance. -/
theorem DirectionNeedle.maxEndpointRadiusSq_ge_nearest_add_quarter
    {d : ProjectiveDirection} (N : DirectionNeedle d) :
    N.nearestRadiusSq + 1 / 4 ≤ N.maxEndpointRadiusSq := by
  have h := unitChord_max_endpoint_sq_ge_min_add_quarter
    N.angle N.height N.centre
  simp only [planeNormSq_supportPoint] at h
  dsimp [DirectionNeedle.nearestRadiusSq, DirectionNeedle.maxEndpointRadiusSq]
  rw [← max_add_add_left]
  exact h

/-- A positively oriented direction needle whose nearest/farthest squared radii
contain `[r²,R²]` carries one of the two exact arcsine slivers at every
`rho ∈ [r,R]`.

The conclusion is stated in `N.triangle`, which is definitionally the coordinate
`supportNeedleTriangle N.angle N.height N.centre`. -/
theorem DirectionNeedle.radialWindow_exists_side
    {d : ProjectiveDirection} (N : DirectionNeedle d)
    {r R rho : ℝ} (hh : 0 < N.height) (hhr : N.height ≤ r)
    (hrR : r ≤ R)
    (hinner : N.nearestRadiusSq ≤ r ^ 2)
    (houter : R ^ 2 ≤ N.maxEndpointRadiusSq)
    (hrho : rho ∈ Icc r R) :
    (Real.arcsin (N.height / rho) ∈
          Icc (Real.arcsin (N.height / R))
            (Real.arcsin (N.height / r)) ∧
        polarPoint rho (N.angle + Real.arcsin (N.height / rho)) ∈ N.triangle) ∨
      (Real.pi - Real.arcsin (N.height / rho) ∈
          Icc (Real.pi - Real.arcsin (N.height / r))
            (Real.pi - Real.arcsin (N.height / R)) ∧
        polarPoint rho
            (N.angle + Real.pi - Real.arcsin (N.height / rho)) ∈ N.triangle) := by
  exact supportChord_radialWindow_exists_side
    hh hhr hrR hinner houter hrho

end

end StarKakeyaLower
