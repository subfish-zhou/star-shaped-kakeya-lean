import StarKakeyaLower.CaseIRadialCore
import StarKakeyaLower.LiNeedleAdapter
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# The universal physical-to-raw needle adapter

This file constructs, rather than assumes, the support-coordinate family attached
to the arbitrary physical needle family of a `StarShapedKakeya` set.

It also carries the coordinate transport: the measure-preserving identification
`planeCoordinateEquiv`, the unrestricted outer-measure transport
`outerMeasure_centeredCoordinate_image`, and the *restricted* transport across
`Metric.closedBall K.center r0` / `originClosedDisk r0` used by the confined
branch.  Those declarations were moved here from
`StarKakeyaLower.UniversalAssembly` so that the whole adapter/transport layer is
reachable from an import closure free of frozen witness constants.
-/

open Set MeasureTheory

namespace StarKakeyaLower

noncomputable section

/-- The canonical coordinate equivalence from the Euclidean plane to the product plane. -/
def planeCoordinateEquiv : Plane ≃ᵐ CoordinatePlane :=
  coordinatePlaneEquiv.symm

@[simp] theorem planeCoordinateEquiv_apply (x : Plane) :
    planeCoordinateEquiv x = (x 0, x 1) := rfl

/-- Translate the star centre to zero and pass to product coordinates. -/
def centeredCoordinate {E : Set Plane} (K : StarShapedKakeya E) (x : Plane) :
    CoordinatePlane := planeCoordinateEquiv (x - K.center)

/-- Data of an oriented lift of one universally chosen physical needle. -/
structure UniversalOrientedNeedleLift {E : Set Plane} (K : StarShapedKakeya E)
    (d : ProjectiveDirection) where
  angle : ℝ
  direction_eq : (angle : ProjectiveDirection) = d
  orientation : ℝ
  orientation_abs : |orientation| = 1
  endpoint_sub :
    (K.needleFamily d).right - (K.needleFamily d).left =
      orientation • angleVector angle

/-- Choice of the oriented lift furnished by `needleFamily_hasDirection`. -/
def universalOrientedNeedleLift {E : Set Plane} (K : StarShapedKakeya E)
    (d : ProjectiveDirection) : UniversalOrientedNeedleLift K d := by
  let h := UnitNeedle.hasDirection_oriented_lift (K.needleFamily_hasDirection d)
  exact {
    angle := Classical.choose h
    direction_eq := (Classical.choose_spec h).1
    orientation := Classical.choose (Classical.choose_spec h).2
    orientation_abs := (Classical.choose_spec (Classical.choose_spec h).2).1
    endpoint_sub := (Classical.choose_spec (Classical.choose_spec h).2).2 }

/-- Tangential coordinate along the chosen oriented direction. -/
def tangentialCoord (t : ℝ) (x : Plane) : ℝ :=
  x 0 * Real.cos t + x 1 * Real.sin t

/-- The raw support-coordinate needle canonically extracted from the physical one. -/
def universalDirectionNeedle {E : Set Plane} (K : StarShapedKakeya E)
    (d : ProjectiveDirection) : DirectionNeedle d :=
  let L := universalOrientedNeedleLift K d
  let p := (K.needleFamily d).left - K.center
  let q := (K.needleFamily d).right - K.center
  { angle := L.angle
    height := normalCoord L.angle p
    centre := (tangentialCoord L.angle p + tangentialCoord L.angle q) / 2
    direction_eq := L.direction_eq }

private theorem orientation_eq_one_or_neg_one {c : ℝ} (hc : |c| = 1) :
    c = 1 ∨ c = -1 :=
  (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hc

/-- Normal and tangential coordinates reconstruct a point in the oriented frame. -/
private theorem supportPoint_normalCoord_tangentialCoord (t : ℝ) (p : Plane) :
    coordinatePlaneEquiv
      (supportPoint t (normalCoord t p) (tangentialCoord t p)) = p := by
  ext i
  fin_cases i
  · simp [supportPoint, normalCoord, tangentialCoord, det, addCoordinatePlane,
      scaleCoordinatePlane, unitDirection, unitNormal]
    linear_combination (p 0) * Real.cos_sq_add_sin_sq t
  · simp [supportPoint, normalCoord, tangentialCoord, det, addCoordinatePlane,
      scaleCoordinatePlane, unitDirection, unitNormal]
    linear_combination (p 1) * Real.cos_sq_add_sin_sq t

private theorem universal_tangential_difference
    {E : Set Plane} (K : StarShapedKakeya E) (d : ProjectiveDirection) :
    tangentialCoord (universalOrientedNeedleLift K d).angle
        ((K.needleFamily d).right - K.center) -
      tangentialCoord (universalOrientedNeedleLift K d).angle
        ((K.needleFamily d).left - K.center) =
      (universalOrientedNeedleLift K d).orientation := by
  let L := universalOrientedNeedleLift K d
  have h0 := congrArg (fun x : Plane => x 0) L.endpoint_sub
  have h1 := congrArg (fun x : Plane => x 1) L.endpoint_sub
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    angleVector_zero, angleVector_one] at h0 h1
  change
    tangentialCoord L.angle ((K.needleFamily d).right - K.center) -
      tangentialCoord L.angle ((K.needleFamily d).left - K.center) = L.orientation
  dsimp [tangentialCoord]
  calc
    _ = Real.cos L.angle *
          ((K.needleFamily d).right 0 - (K.needleFamily d).left 0) +
        Real.sin L.angle *
          ((K.needleFamily d).right 1 - (K.needleFamily d).left 1) := by ring
    _ = L.orientation *
        (Real.cos L.angle ^ 2 + Real.sin L.angle ^ 2) := by
      rw [h0, h1]
      ring
    _ = L.orientation := by rw [Real.cos_sq_add_sin_sq]; ring

private theorem universal_normal_eq
    {E : Set Plane} (K : StarShapedKakeya E) (d : ProjectiveDirection) :
    normalCoord (universalOrientedNeedleLift K d).angle
        ((K.needleFamily d).right - K.center) =
      normalCoord (universalOrientedNeedleLift K d).angle
        ((K.needleFamily d).left - K.center) := by
  let L := universalOrientedNeedleLift K d
  have h0 := congrArg (fun x : Plane => x 0) L.endpoint_sub
  have h1 := congrArg (fun x : Plane => x 1) L.endpoint_sub
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    angleVector_zero, angleVector_one] at h0 h1
  dsimp [normalCoord, det, L, angleVector]
  linear_combination (Real.cos L.angle) * h1 - (Real.sin L.angle) * h0

/-- If the lift has positive orientation, the lower support parameter is the
translated physical left endpoint. -/
theorem universalDirectionNeedle_lower_endpoint_of_orientation_eq_one
    {E : Set Plane} (K : StarShapedKakeya E) (d : ProjectiveDirection)
    (hc : (universalOrientedNeedleLift K d).orientation = 1) :
    coordinatePlaneEquiv
        (supportPoint (universalDirectionNeedle K d).angle
          (universalDirectionNeedle K d).height
          ((universalDirectionNeedle K d).centre - 1 / 2)) =
      (K.needleFamily d).left - K.center := by
  let L := universalOrientedNeedleLift K d
  let p := (K.needleFamily d).left - K.center
  let q := (K.needleFamily d).right - K.center
  have htan := universal_tangential_difference K d
  rw [hc] at htan
  have hparam : (universalDirectionNeedle K d).centre - 1 / 2 =
      tangentialCoord L.angle p := by
    dsimp [universalDirectionNeedle, p, q, L] at htan ⊢
    linarith
  rw [hparam]
  exact supportPoint_normalCoord_tangentialCoord L.angle p

/-- Positive orientation sends the upper support parameter to physical right. -/
theorem universalDirectionNeedle_upper_endpoint_of_orientation_eq_one
    {E : Set Plane} (K : StarShapedKakeya E) (d : ProjectiveDirection)
    (hc : (universalOrientedNeedleLift K d).orientation = 1) :
    coordinatePlaneEquiv
        (supportPoint (universalDirectionNeedle K d).angle
          (universalDirectionNeedle K d).height
          ((universalDirectionNeedle K d).centre + 1 / 2)) =
      (K.needleFamily d).right - K.center := by
  let L := universalOrientedNeedleLift K d
  let p := (K.needleFamily d).left - K.center
  let q := (K.needleFamily d).right - K.center
  have htan := universal_tangential_difference K d
  rw [hc] at htan
  have hparam : (universalDirectionNeedle K d).centre + 1 / 2 =
      tangentialCoord L.angle q := by
    dsimp [universalDirectionNeedle, p, q, L] at htan ⊢
    linarith
  rw [hparam]
  change coordinatePlaneEquiv
      (supportPoint L.angle (normalCoord L.angle p) (tangentialCoord L.angle q)) = q
  rw [← universal_normal_eq K d]
  exact supportPoint_normalCoord_tangentialCoord L.angle q

/-- Negative orientation swaps the two physical endpoints. -/
theorem universalDirectionNeedle_lower_endpoint_of_orientation_eq_neg_one
    {E : Set Plane} (K : StarShapedKakeya E) (d : ProjectiveDirection)
    (hc : (universalOrientedNeedleLift K d).orientation = -1) :
    coordinatePlaneEquiv
        (supportPoint (universalDirectionNeedle K d).angle
          (universalDirectionNeedle K d).height
          ((universalDirectionNeedle K d).centre - 1 / 2)) =
      (K.needleFamily d).right - K.center := by
  let L := universalOrientedNeedleLift K d
  let p := (K.needleFamily d).left - K.center
  let q := (K.needleFamily d).right - K.center
  have htan := universal_tangential_difference K d
  rw [hc] at htan
  have hparam : (universalDirectionNeedle K d).centre - 1 / 2 =
      tangentialCoord L.angle q := by
    dsimp [universalDirectionNeedle, p, q, L] at htan ⊢
    linarith
  rw [hparam]
  change coordinatePlaneEquiv
      (supportPoint L.angle (normalCoord L.angle p) (tangentialCoord L.angle q)) = q
  rw [← universal_normal_eq K d]
  exact supportPoint_normalCoord_tangentialCoord L.angle q

/-- Negative orientation sends the upper support parameter to physical left. -/
theorem universalDirectionNeedle_upper_endpoint_of_orientation_eq_neg_one
    {E : Set Plane} (K : StarShapedKakeya E) (d : ProjectiveDirection)
    (hc : (universalOrientedNeedleLift K d).orientation = -1) :
    coordinatePlaneEquiv
        (supportPoint (universalDirectionNeedle K d).angle
          (universalDirectionNeedle K d).height
          ((universalDirectionNeedle K d).centre + 1 / 2)) =
      (K.needleFamily d).left - K.center := by
  let L := universalOrientedNeedleLift K d
  let p := (K.needleFamily d).left - K.center
  let q := (K.needleFamily d).right - K.center
  have htan := universal_tangential_difference K d
  rw [hc] at htan
  have hparam : (universalDirectionNeedle K d).centre + 1 / 2 =
      tangentialCoord L.angle p := by
    dsimp [universalDirectionNeedle, p, q, L] at htan ⊢
    linarith
  rw [hparam]
  exact supportPoint_normalCoord_tangentialCoord L.angle p

/-- The raw adapter retains the requested projective direction. -/
@[simp] theorem universalDirectionNeedle_direction_eq {E : Set Plane}
    (K : StarShapedKakeya E) (d : ProjectiveDirection) :
    ((universalDirectionNeedle K d).angle : ProjectiveDirection) = d :=
  (universalDirectionNeedle K d).direction_eq

/-- The physical needle translated by its star centre. -/
def UnitNeedle.centered (n : UnitNeedle) (o : Plane) : UnitNeedle where
  left := n.left - o
  right := n.right - o
  unit_length := by simpa [dist_eq_norm] using n.unit_length

private theorem UnitNeedle.ext' {a b : UnitNeedle}
    (hl : a.left = b.left) (hr : a.right = b.right) : a = b := by
  cases a
  cases b
  simp_all

/-- The support endpoint model is literally the centered physical needle, with
its endpoints possibly exchanged by a negative oriented lift. -/
theorem universalDirectionNeedle_toUnitNeedle_eq_centered_or_swap
    {E : Set Plane} (K : StarShapedKakeya E) (d : ProjectiveDirection) :
    (universalDirectionNeedle K d).toUnitNeedle =
        (K.needleFamily d).centered K.center ∨
      (universalDirectionNeedle K d).toUnitNeedle =
        { left := (K.needleFamily d).right - K.center
          right := (K.needleFamily d).left - K.center
          unit_length := by simpa [dist_comm, dist_eq_norm] using
            (K.needleFamily d).unit_length } := by
  rcases orientation_eq_one_or_neg_one
      (universalOrientedNeedleLift K d).orientation_abs with hc | hc
  · left
    apply UnitNeedle.ext'
    · exact universalDirectionNeedle_lower_endpoint_of_orientation_eq_one K d hc
    · exact universalDirectionNeedle_upper_endpoint_of_orientation_eq_one K d hc
  · right
    apply UnitNeedle.ext'
    · exact universalDirectionNeedle_lower_endpoint_of_orientation_eq_neg_one K d hc
    · exact universalDirectionNeedle_upper_endpoint_of_orientation_eq_neg_one K d hc

/-- Translation carries a segment from `o` to `x` to the segment from zero to
`x-o`. -/
private theorem segment_zero_sub_eq_image (o x : Plane) :
    segment ℝ 0 (x - o) = (fun z => z - o) '' segment ℝ o x := by
  rw [segment_eq_image, segment_eq_image]
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨(1 - s) • o + s • x, ⟨s, hs, rfl⟩, ?_⟩
    module
  · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨s, hs, ?_⟩
    module

/-- Translating the endpoints translates the needle carrier. -/
private theorem UnitNeedle.carrier_centered (n : UnitNeedle) (o : Plane) :
    (n.centered o).carrier = (fun x => x - o) '' n.carrier := by
  simp only [UnitNeedle.carrier, UnitNeedle.centered, segment_eq_image]
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨(1 - s) • n.left + s • n.right, ⟨s, hs, rfl⟩, ?_⟩
    module
  · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨s, hs, ?_⟩
    module

/-- Translating both endpoints translates the complete swept triangle. -/
theorem UnitNeedle.triangleHull_centered (n : UnitNeedle) (o : Plane) :
    (n.centered o).triangleHull 0 = (fun x => x - o) '' n.triangleHull o := by
  ext z
  constructor
  · intro hz
    simp only [UnitNeedle.triangleHull, mem_iUnion] at hz
    obtain ⟨x, hx, hz⟩ := hz
    rw [UnitNeedle.carrier_centered] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [segment_zero_sub_eq_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨w, ?_, rfl⟩
    simp only [UnitNeedle.triangleHull, mem_iUnion]
    exact ⟨y, hy, hw⟩
  · rintro ⟨w, hw, rfl⟩
    simp only [UnitNeedle.triangleHull, mem_iUnion] at hw ⊢
    obtain ⟨y, hy, hw⟩ := hw
    refine ⟨y - o, ?_, ?_⟩
    · rw [UnitNeedle.carrier_centered]
      exact ⟨y, hy, rfl⟩
    · rw [segment_zero_sub_eq_image]
      exact ⟨w, hw, rfl⟩

/-- Swapping the endpoints of a unit needle does not change its triangle hull. -/
theorem UnitNeedle.triangleHull_swap (n : UnitNeedle) (o : Plane) :
    ({ left := n.right, right := n.left,
       unit_length := by simpa [dist_comm] using n.unit_length } : UnitNeedle).triangleHull o =
      n.triangleHull o := by
  have hcarrier :
      ({ left := n.right, right := n.left,
         unit_length := by simpa [dist_comm] using n.unit_length } : UnitNeedle).carrier =
        n.carrier := by
    simp only [UnitNeedle.carrier]
    exact segment_symm ℝ n.right n.left
  simp only [UnitNeedle.triangleHull, hcarrier]

/-- Exact set-level bridge from the raw support triangle to the centered physical triangle. -/
theorem universalDirectionNeedle_image_triangle_eq_centered_triangleHull
    {E : Set Plane} (K : StarShapedKakeya E) (d : ProjectiveDirection) :
    coordinatePlaneEquiv '' (universalDirectionNeedle K d).triangle =
      (fun x => x - K.center) '' (K.needleFamily d).triangleHull K.center := by
  rw [DirectionNeedle.image_triangle_eq_triangleHull]
  rcases universalDirectionNeedle_toUnitNeedle_eq_centered_or_swap K d with h | h
  · rw [h, UnitNeedle.triangleHull_centered]
  · rw [h]
    let n := (K.needleFamily d).centered K.center
    have hswap :
        ({ left := (K.needleFamily d).right - K.center
           right := (K.needleFamily d).left - K.center
           unit_length := by simpa [dist_comm, dist_eq_norm] using
             (K.needleFamily d).unit_length } : UnitNeedle).triangleHull 0 =
          n.triangleHull 0 := by
      exact UnitNeedle.triangleHull_swap n 0
    rw [hswap, UnitNeedle.triangleHull_centered]

/-- Equivalent product-coordinate form of the exact triangle bridge. -/
theorem universalDirectionNeedle_triangle_eq_centeredCoordinate_image
    {E : Set Plane} (K : StarShapedKakeya E) (d : ProjectiveDirection) :
    (universalDirectionNeedle K d).triangle =
      centeredCoordinate K '' (K.needleFamily d).triangleHull K.center := by
  apply (Set.image_injective.mpr coordinatePlaneEquiv.injective)
  rw [universalDirectionNeedle_image_triangle_eq_centered_triangleHull]
  simp only [centeredCoordinate, image_image]
  congr 1
  funext x
  ext i
  fin_cases i <;> rfl

/-- The complete universal triangle union lies in the centered Kakeya set. -/
theorem universalDirectionTriangleUnion_subset {E : Set Plane}
    (K : StarShapedKakeya E) :
    directionTriangleUnion (universalDirectionNeedle K) Set.univ ⊆
      centeredCoordinate K '' E := by
  intro z hz
  simp only [directionTriangleUnion, mem_iUnion] at hz
  obtain ⟨⟨d, _hd⟩, hz⟩ := hz
  rw [universalDirectionNeedle_triangle_eq_centeredCoordinate_image] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  exact ⟨x, K.triangleHull_subset d hx, rfl⟩

/-- The raw signed support height has exactly the physical determinant height. -/
theorem universalDirectionNeedle_abs_height {E : Set Plane}
    (K : StarShapedKakeya E) (d : ProjectiveDirection) :
    |(universalDirectionNeedle K d).height| =
      (K.needleFamily d).height K.center := by
  let L := universalOrientedNeedleLift K d
  have h := UnitNeedle.height_eq_abs_normalCoord
    (o := K.center) L.orientation_abs L.endpoint_sub
  rw [h]
  change |normalCoord L.angle ((K.needleFamily d).left - K.center)| =
    |normalCoord L.angle (K.center - (K.needleFamily d).left)|
  have hneg : normalCoord L.angle ((K.needleFamily d).left - K.center) =
      -normalCoord L.angle (K.center - (K.needleFamily d).left) := by
    rw [normalCoord_sub, normalCoord_sub]
    ring
  rw [hneg, abs_neg]

/-! ## Coordinate transport

The two declarations of this section were moved verbatim from
`StarKakeyaLower.UniversalAssembly`; the restricted forms that follow are new.
-/

/-- The coordinate equivalence preserves the exact planar Lebesgue
normalization. -/
theorem planeCoordinateEquiv_measurePreserving :
    MeasurePreserving planeCoordinateEquiv := by
  exact coordinatePlaneEquiv_measurePreserving.symm coordinatePlaneEquiv

/-- The coordinate change preserves outer measure for an arbitrary planar set,
not merely for the Kakeya set of `K`.  The centre of `K` is the only datum the
translation uses. -/
theorem outerMeasure_centeredCoordinate_image_of_set {E : Set Plane}
    (K : StarShapedKakeya E) (S : Set Plane) :
    volume.toOuterMeasure (centeredCoordinate K '' S) =
      volume.toOuterMeasure S := by
  let tau : Plane ≃ᵐ Plane := MeasurableEquiv.addRight (-K.center)
  have htau : MeasurePreserving tau := measurePreserving_add_right volume (-K.center)
  have hcoord : MeasurePreserving planeCoordinateEquiv :=
    planeCoordinateEquiv_measurePreserving
  have hcomp : MeasurePreserving (tau.trans planeCoordinateEquiv) := htau.trans hcoord
  have himage : centeredCoordinate K '' S = (tau.trans planeCoordinateEquiv) '' S := by
    ext z
    simp only [centeredCoordinate, mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, ?_⟩
      change planeCoordinateEquiv (x - K.center) =
        planeCoordinateEquiv (x + -K.center)
      rw [sub_eq_add_neg]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, ?_⟩
      change planeCoordinateEquiv (x + -K.center) =
        planeCoordinateEquiv (x - K.center)
      rw [sub_eq_add_neg]
  rw [himage]
  have hpre := hcomp.measure_preimage_equiv
    ((tau.trans planeCoordinateEquiv) '' S)
  rw [preimage_image_eq S (tau.trans planeCoordinateEquiv).injective] at hpre
  exact hpre.symm

/-- The coordinate change preserves outer measure for arbitrary sets. -/
theorem outerMeasure_centeredCoordinate_image {E : Set Plane}
    (K : StarShapedKakeya E) :
    volume.toOuterMeasure (centeredCoordinate K '' E) =
      volume.toOuterMeasure E :=
  outerMeasure_centeredCoordinate_image_of_set K E

/-- The centred coordinate map is injective: it is a translation followed by a
measurable equivalence. -/
theorem centeredCoordinate_injective {E : Set Plane} (K : StarShapedKakeya E) :
    Function.Injective (centeredCoordinate K) := by
  intro x y hxy
  have h : x - K.center = y - K.center :=
    planeCoordinateEquiv.injective hxy
  exact sub_left_injective h

/-- Membership in the metric ball around the star centre is exactly the
squared-radius inequality used by `originClosedDisk`.  Nonnegativity of the
radius is load bearing: for `r0 < 0` the ball is empty while the right-hand side
is not. -/
theorem dist_le_iff_sq_add_sq_le {E : Set Plane} (K : StarShapedKakeya E)
    {r0 : ℝ} (hr0 : 0 ≤ r0) (x : Plane) :
    dist x K.center ≤ r0 ↔
      (x 0 - K.center 0) ^ 2 + (x 1 - K.center 1) ^ 2 ≤ r0 ^ 2 := by
  have hd : dist x K.center =
      Real.sqrt ((x 0 - K.center 0) ^ 2 + (x 1 - K.center 1) ^ 2) := by
    rw [EuclideanSpace.dist_eq]
    congr 1
    simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]
  have hnn : (0 : ℝ) ≤ (x 0 - K.center 0) ^ 2 + (x 1 - K.center 1) ^ 2 := by
    positivity
  rw [hd]
  constructor
  · intro h
    nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg
      ((x 0 - K.center 0) ^ 2 + (x 1 - K.center 1) ^ 2)]
  · intro h
    have hle := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq hr0] at hle

/-- The centred coordinate map carries the metric closed ball around the star
centre exactly onto the origin-centred closed coordinate disk.  The hypothesis
`0 ≤ r0` cannot be dropped: at negative `r0` the left-hand side is empty and the
right-hand side is the disk of radius `|r0|`. -/
theorem centeredCoordinate_image_closedBall {E : Set Plane}
    (K : StarShapedKakeya E) {r0 : ℝ} (hr0 : 0 ≤ r0) :
    centeredCoordinate K '' Metric.closedBall K.center r0 = originClosedDisk r0 := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Metric.mem_closedBall, dist_le_iff_sq_add_sq_le K hr0] at hx
    simp only [originClosedDisk, mem_setOf_eq, centeredCoordinate,
      planeCoordinateEquiv_apply, PiLp.sub_apply]
    exact hx
  · intro hz
    have hz' : z.1 ^ 2 + z.2 ^ 2 ≤ r0 ^ 2 := hz
    refine ⟨K.center + coordinatePlaneEquiv z, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_le_iff_sq_add_sq_le K hr0]
      simpa using hz'
    · simp only [centeredCoordinate, planeCoordinateEquiv_apply, PiLp.add_apply,
        PiLp.sub_apply, coordinatePlaneEquiv_apply_zero, coordinatePlaneEquiv_apply_one]
      simp

/-- The restricted transport.  Both sides describe the same physical set: the
part of `E` inside the closed ball of radius `r0` around the star centre. -/
theorem outerMeasure_centeredCoordinate_image_inter_closedBall {E : Set Plane}
    (K : StarShapedKakeya E) {r0 : ℝ} (hr0 : 0 ≤ r0) :
    volume.toOuterMeasure ((centeredCoordinate K '' E) ∩ originClosedDisk r0) =
      volume.toOuterMeasure (E ∩ Metric.closedBall K.center r0) := by
  rw [← centeredCoordinate_image_closedBall K hr0,
    ← Set.image_inter (centeredCoordinate_injective K),
    outerMeasure_centeredCoordinate_image_of_set K (E ∩ Metric.closedBall K.center r0)]

/-- The confined form of the triangle-union containment: intersecting both sides
with the coordinate disk is harmless. -/
theorem universalDirectionTriangleUnion_inter_originClosedDisk_subset
    {E : Set Plane} (K : StarShapedKakeya E) {r0 : ℝ} :
    directionTriangleUnion (universalDirectionNeedle K) Set.univ ∩ originClosedDisk r0 ⊆
      (centeredCoordinate K '' E) ∩ originClosedDisk r0 :=
  Set.inter_subset_inter_left _ (universalDirectionTriangleUnion_subset K)

/-! ## Orientation reversal of support coordinates

These three identities were moved here from `StarKakeyaLower.SupportReflection`,
whose import closure is not clean.  They are the prerequisites of
`DirectionNeedle.orientPositive` below, and `SupportReflection` now imports this
module to obtain them.
-/

/-- Reversing the orientation of a support line negates both support
coordinates and leaves the represented point unchanged. -/
theorem supportPoint_add_pi_neg (α δ x : ℝ) :
    supportPoint (α + Real.pi) (-δ) (-x) = supportPoint α δ x := by
  ext <;>
    simp [supportPoint, addCoordinatePlane, scaleCoordinatePlane,
      unitDirection, unitNormal, Real.sin_add, Real.cos_add] <;> ring

/-- The two oriented descriptions have exactly the same filled triangle. -/
theorem supportNeedleTriangle_add_pi_neg (α δ c : ℝ) :
    supportNeedleTriangle (α + Real.pi) (-δ) (-c) =
      supportNeedleTriangle α δ c := by
  ext z
  constructor
  · rintro ⟨lam, hlam, x, hx, rfl⟩
    refine ⟨lam, hlam, -x, ?_, ?_⟩
    · constructor <;> linarith [hx.1, hx.2]
    · simpa using congrArg (scaleCoordinatePlane lam)
        (supportPoint_add_pi_neg α δ (-x))
  · rintro ⟨lam, hlam, x, hx, rfl⟩
    refine ⟨lam, hlam, -x, ?_, ?_⟩
    · constructor <;> linarith [hx.1, hx.2]
    · convert congrArg (scaleCoordinatePlane lam)
        (supportPoint_add_pi_neg α δ x).symm using 1 <;> ring

/-- Orientation reversal does not change an unoriented direction. -/
theorem projectiveDirection_add_pi (α : ℝ) :
    ((α + Real.pi : ℝ) : ProjectiveDirection) = (α : ProjectiveDirection) := by
  rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]

/-! ## Orientation normalization of a raw support needle -/

/-- The equivalent presentation of a raw direction needle with nonnegative
support height.  Reversing the orientation of the support line negates both
support coordinates and leaves the filled triangle unchanged. -/
def DirectionNeedle.orientPositive {d : ProjectiveDirection}
    (N : DirectionNeedle d) : DirectionNeedle d :=
  if 0 ≤ N.height then N
  else
    { angle := N.angle + Real.pi
      height := -N.height
      centre := -N.centre
      direction_eq := by
        rw [projectiveDirection_add_pi]; exact N.direction_eq }

@[simp] theorem DirectionNeedle.orientPositive_height_nonneg
    {d : ProjectiveDirection} (N : DirectionNeedle d) :
    0 ≤ N.orientPositive.height := by
  rw [DirectionNeedle.orientPositive]
  split
  · assumption
  · simp only []
    linarith [not_le.1 (by assumption : ¬ 0 ≤ N.height)]

@[simp] theorem DirectionNeedle.orientPositive_abs_height
    {d : ProjectiveDirection} (N : DirectionNeedle d) :
    |N.orientPositive.height| = |N.height| := by
  rw [DirectionNeedle.orientPositive]
  split
  · rfl
  · exact abs_neg _

@[simp] theorem DirectionNeedle.orientPositive_triangle
    {d : ProjectiveDirection} (N : DirectionNeedle d) :
    N.orientPositive.triangle = N.triangle := by
  rw [DirectionNeedle.orientPositive]
  split
  · rfl
  · exact supportNeedleTriangle_add_pi_neg N.angle N.height N.centre

theorem DirectionNeedle.orientPositive_height_eq_abs
    {d : ProjectiveDirection} (N : DirectionNeedle d) :
    N.orientPositive.height = |N.height| := by
  rw [← abs_of_nonneg N.orientPositive_height_nonneg,
    DirectionNeedle.orientPositive_abs_height]

/-! ## The positively oriented universal support family -/

section PositiveFamily

variable {E : Set Plane}

/-- The universal raw support needle, normalized to nonnegative height. -/
def universalPositiveNeedle (K : StarShapedKakeya E) (d : ProjectiveDirection) :
    DirectionNeedle d := (universalDirectionNeedle K d).orientPositive

@[simp] theorem universalPositiveNeedle_triangle (K : StarShapedKakeya E)
    (d : ProjectiveDirection) :
    (universalPositiveNeedle K d).triangle =
      (universalDirectionNeedle K d).triangle :=
  DirectionNeedle.orientPositive_triangle _

@[simp] theorem universalPositiveNeedle_height_nonneg (K : StarShapedKakeya E)
    (d : ProjectiveDirection) : 0 ≤ (universalPositiveNeedle K d).height :=
  DirectionNeedle.orientPositive_height_nonneg _

theorem universalPositiveNeedle_abs_height (K : StarShapedKakeya E)
    (d : ProjectiveDirection) :
    |(universalPositiveNeedle K d).height| =
      (K.needleFamily d).height K.center := by
  rw [universalPositiveNeedle, DirectionNeedle.orientPositive_abs_height]
  exact universalDirectionNeedle_abs_height K d

theorem universalPositiveNeedle_height_lt_of_no_high {K : StarShapedKakeya E}
    {a : ℝ}
    (hhigh : ¬ ∃ theta : Direction,
      a ≤ (K.needleFamily theta).height K.center) (d : ProjectiveDirection) :
    (universalPositiveNeedle K d).height < a := by
  have h : |(universalPositiveNeedle K d).height| < a := by
    rw [universalPositiveNeedle_abs_height]
    exact lt_of_not_ge (fun hd => hhigh ⟨d, hd⟩)
  exact (le_abs_self _).trans_lt h

theorem universalPositiveNeedle_height_le_of_no_high {K : StarShapedKakeya E}
    {a : ℝ}
    (hhigh : ¬ ∃ theta : Direction,
      a ≤ (K.needleFamily theta).height K.center) :
    ∀ d, |(universalPositiveNeedle K d).height| ≤ a := by
  intro d
  rw [universalPositiveNeedle_abs_height]
  exact (lt_of_not_ge (fun hd => hhigh ⟨d, hd⟩)).le

theorem universalPositiveTriangleUnion_subset (K : StarShapedKakeya E) :
    directionTriangleUnion (universalPositiveNeedle K) Set.univ ⊆
      centeredCoordinate K '' E := by
  intro z hz
  simp only [directionTriangleUnion, mem_iUnion] at hz
  obtain ⟨⟨d, _hd⟩, hz⟩ := hz
  rw [universalPositiveNeedle_triangle] at hz
  exact universalDirectionTriangleUnion_subset K
    (triangle_subset_directionTriangleUnion_univ (universalDirectionNeedle K) d hz)

/-- Restricted form of the positive triangle-union containment.  No radius
hypothesis is needed: intersecting both sides of
`universalPositiveTriangleUnion_subset` with the coordinate disk is harmless. -/
theorem universalPositiveTriangleUnion_inter_originClosedDisk_subset
    (K : StarShapedKakeya E) {r0 : ℝ} :
    directionTriangleUnion (universalPositiveNeedle K) Set.univ ∩ originClosedDisk r0 ⊆
      (centeredCoordinate K '' E) ∩ originClosedDisk r0 :=
  Set.inter_subset_inter_left _ (universalPositiveTriangleUnion_subset K)

end PositiveFamily

end

end StarKakeyaLower
