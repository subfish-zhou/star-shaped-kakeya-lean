import StarKakeyaLower.EndpointCapacityFixedWindow
import StarKakeyaLower.UniversalNeedleAdapter

/-!
# Universal star-shaped Kakeya specialization of the radial sliver theorem

The canonical physical needle family is first normalized to nonnegative support
height by `universalPositiveNeedle`.  Eligibility is stated by the exact
coordinate nearest and maximum-endpoint squared radii.
-/

open Set MeasureTheory
open scoped ENNReal

namespace StarKakeyaLower

noncomputable section

/-- Directions whose canonical selected needle reaches the fixed radial window
`[r,R]`. -/
def endpointCapacityWindowDirections
    {E : Set Plane} (K : StarShapedKakeya E) (r R : ℝ) :
    Set ProjectiveDirection :=
  {d | (universalPositiveNeedle K d).nearestRadiusSq ≤ r ^ 2 ∧
    R ^ 2 ≤ (universalPositiveNeedle K d).maxEndpointRadiusSq}

/-- Each canonical positive support triangle lies in the centered Kakeya set. -/
theorem universalPositiveNeedle_triangle_subset_centeredSet
    {E : Set Plane} (K : StarShapedKakeya E) (d : ProjectiveDirection) :
    (universalPositiveNeedle K d).triangle ⊆ centeredCoordinate K '' E := by
  intro z hz
  exact universalPositiveTriangleUnion_subset K
    (triangle_subset_directionTriangleUnion_univ
      (universalPositiveNeedle K) d hz)

/-- Universal-selector fixed-window radial sliver theorem, in the exact selected
triangle-union form used by the paper capacity.  No measurability of the selected
needle family or eligible direction set is assumed. -/
theorem StarShapedKakeya.endpointCapacity_fixedWindow
    {E : Set Plane} (K : StarShapedKakeya E)
    (r0 r R : ℝ) (hr : 0 < r) (hrR : r < R) (hr0 : r0 < r) :
    ENNReal.ofReal ((R - r) / (R + r)) *
        volume (endpointCapacityWindowDirections K r R) ≤
      radialSuperlevelOuter
        (directionTriangleUnion (universalPositiveNeedle K) Set.univ) r0 := by
  apply ofReal_windowRatio_mul_volume_le_radialSuperlevelOuter
    (endpointCapacityWindowDirections K r R)
    (universalPositiveNeedle K)
    (directionTriangleUnion (universalPositiveNeedle K) Set.univ)
    r0 r R hr hrR hr0
  · intro d hd
    exact universalPositiveNeedle_height_nonneg K d
  · intro d hd
    exact hd.1
  · intro d hd
    exact hd.2
  · intro d hd
    exact triangle_subset_directionTriangleUnion_univ
      (universalPositiveNeedle K) d

/-- Monotone corollary with the whole centered Kakeya set on the right. -/
theorem StarShapedKakeya.endpointCapacity_fixedWindow_centeredSet
    {E : Set Plane} (K : StarShapedKakeya E)
    (r0 r R : ℝ) (hr : 0 < r) (hrR : r < R) (hr0 : r0 < r) :
    ENNReal.ofReal ((R - r) / (R + r)) *
        volume (endpointCapacityWindowDirections K r R) ≤
      radialSuperlevelOuter (centeredCoordinate K '' E) r0 :=
  (K.endpointCapacity_fixedWindow r0 r R hr hrR hr0).trans
    (radialSuperlevelOuter_mono (universalPositiveTriangleUnion_subset K))

end

end StarKakeyaLower
