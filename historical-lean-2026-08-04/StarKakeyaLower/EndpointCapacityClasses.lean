import StarKakeyaLower.EndpointCapacityLayerCake

/-!
# Endpoint-capacity nearest-radius classes

Generic initial and half-open bands for the squared nearest radius of the
canonical positive selector, together with the eligibility lemmas consumed by a
finite radial schedule.
-/

open Set

namespace StarKakeyaLower

noncomputable section

/-- The squared nearest radius is nonnegative. -/
theorem DirectionNeedle.nearestRadiusSq_nonneg
    {d : ProjectiveDirection} (N : DirectionNeedle d) :
    0 ≤ N.nearestRadiusSq := by
  rw [DirectionNeedle.nearestRadiusSq]
  positivity

/-- Initial low class `m² ≤ b²`. -/
def endpointCapacityInitialClass
    {E : Set Plane} (K : StarShapedKakeya E) (b : ℝ) :
    Set ProjectiveDirection :=
  {d | (universalPositiveNeedle K d).nearestRadiusSq ≤ b ^ 2}

/-- Half-open low band `a² < m² ≤ b²`. -/
def endpointCapacityBandClass
    {E : Set Plane} (K : StarShapedKakeya E) (a b : ℝ) :
    Set ProjectiveDirection :=
  {d | a ^ 2 < (universalPositiveNeedle K d).nearestRadiusSq ∧
    (universalPositiveNeedle K d).nearestRadiusSq ≤ b ^ 2}

/-- The initial class is eligible for every window whose inner radius is at
least `b` and whose outer squared radius is at most `1/4`. -/
theorem endpointCapacityInitialClass_subset_windowDirections
    {E : Set Plane} (K : StarShapedKakeya E)
    {b r R : ℝ} (hb : 0 ≤ b) (hbr : b ≤ r) (hR : R ^ 2 ≤ 1 / 4) :
    endpointCapacityInitialClass K b ⊆ endpointCapacityWindowDirections K r R := by
  intro d hd
  let N := universalPositiveNeedle K d
  have hb2 : b ^ 2 ≤ r ^ 2 := by nlinarith
  have hn0 : 0 ≤ N.nearestRadiusSq := N.nearestRadiusSq_nonneg
  have hgap := N.maxEndpointRadiusSq_ge_nearest_add_quarter
  exact ⟨hd.trans hb2, by nlinarith⟩

/-- A half-open band is eligible when the window starts above its upper cut and
the outer radius is paid for by the lower cut plus the unit-chord `1/4` gap. -/
theorem endpointCapacityBandClass_subset_windowDirections
    {E : Set Plane} (K : StarShapedKakeya E)
    {a b r R : ℝ} (hb : 0 ≤ b) (hbr : b ≤ r)
    (hR : R ^ 2 ≤ a ^ 2 + 1 / 4) :
    endpointCapacityBandClass K a b ⊆ endpointCapacityWindowDirections K r R := by
  intro d hd
  let N := universalPositiveNeedle K d
  have hb2 : b ^ 2 ≤ r ^ 2 := by nlinarith
  have hgap := N.maxEndpointRadiusSq_ge_nearest_add_quarter
  exact ⟨hd.2.trans hb2, by nlinarith [hd.1]⟩

/-- Two ordered half-open nearest-radius bands are disjoint. -/
theorem endpointCapacityBandClass_disjoint
    {E : Set Plane} (K : StarShapedKakeya E)
    {a b c d : ℝ} (hbc : b ≤ c) (hb : 0 ≤ b) :
    Disjoint (endpointCapacityBandClass K a b)
      (endpointCapacityBandClass K c d) := by
  rw [Set.disjoint_left]
  intro theta hleft hright
  have hsq : b ^ 2 ≤ c ^ 2 := by nlinarith
  exact (not_lt_of_ge (hleft.2.trans hsq)) hright.1

/-- The initial class is disjoint from every later band whose lower cut is at
least its upper cut. -/
theorem endpointCapacityInitialClass_disjoint_band
    {E : Set Plane} (K : StarShapedKakeya E)
    {b c d : ℝ} (hbc : b ≤ c) (hb : 0 ≤ b) :
    Disjoint (endpointCapacityInitialClass K b)
      (endpointCapacityBandClass K c d) := by
  rw [Set.disjoint_left]
  intro theta hleft hright
  have hsq : b ^ 2 ≤ c ^ 2 := by nlinarith
  exact (not_lt_of_ge (hleft.trans hsq)) hright.1

end

end StarKakeyaLower
