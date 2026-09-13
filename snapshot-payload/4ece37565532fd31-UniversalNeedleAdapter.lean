import StarKakeyaLower.CaseIAssemblyConditional
import StarKakeyaLower.LiNeedleAdapter
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# The universal physical-to-raw needle adapter

This file constructs, rather than assumes, the support-coordinate family attached
to the arbitrary physical needle family of a `StarShapedKakeya` set.
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

end

end StarKakeyaLower
