import StarKakeyaLower.StarKakeyaSet
import StarKakeyaLower.GreedyResidual
import StarKakeyaLower.QuotientCircle
import StarKakeyaLower.PolarOuterMeasure
import StarKakeyaLower.TriangleArea
import StarKakeyaLower.ParametricCaseII
import StarKakeyaLower.Trichotomy
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Euclidean and measure interfaces for Case II

This file supplies the concrete outside-ball, open-triangle, greedy-residual,
radial-fan, and Carathéodory-separation layers used in Case II.  The exact local
angular statement connecting Euclidean triangle coordinates to the projective
circle is packaged by `TriangleRayControlled` and proved from the actual needle
data by `UnitNeedle.triangleRayControlled_of_outside`; it is no longer a support
hypothesis.  Disjoint weighted direction intervals therefore force geometric
disjointness through `pairwise_disjoint_triangleInterior_of_outside`.
-/

open Set MeasureTheory Metric Filter

namespace StarKakeyaLower

noncomputable section

namespace UnitNeedle

/-- The complete closed unit needle avoids the open ball of radius `rho`.
Boundary contact is allowed.  This is the non-strict condition supplied by the
paper's Case-II reduction. -/
def OutsideBall (rho : ℝ) (o : Plane) (n : UnitNeedle) : Prop :=
  ∀ x ∈ n.carrier, rho ≤ dist o x

/-- The genuinely stronger condition that the complete needle avoids the
closed ball.  It is useful as a convenience interface, but is not silently
substituted for the paper's `OutsideBall` hypothesis. -/
def StrictOutsideBall (rho : ℝ) (o : Plane) (n : UnitNeedle) : Prop :=
  ∀ x ∈ n.carrier, rho < dist o x

theorem StrictOutsideBall.outsideBall {rho : ℝ} {o : Plane} {n : UnitNeedle}
    (h : n.StrictOutsideBall rho o) : n.OutsideBall rho o :=
  fun x hx => (h x hx).le

theorem dist_le_one_of_mem_carrier {n : UnitNeedle} {x y : Plane}
    (hx : x ∈ n.carrier) (hy : y ∈ n.carrier) : dist x y ≤ 1 := by
  rw [carrier, segment_eq_image] at hx hy
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  rw [dist_eq_norm]
  have heq : (1 - s) • n.left + s • n.right -
      ((1 - t) • n.left + t • n.right) =
      (s - t) • (n.right - n.left) := by module
  have hn : ‖n.right - n.left‖ = 1 := by
    rw [← dist_eq_norm, dist_comm, n.unit_length]
  rw [heq, norm_smul, hn, mul_one, Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]

/-- Paper-to-interface conversion used in Case II.  If one point of a unit
needle is strictly beyond radius `R` (equivalently, the needle is not contained
in `closedBall o R`), then the entire needle is strictly outside the closed
ball of radius `R - 1`. -/
theorem outsideBall_sub_one_of_not_subset_closedBall
    {R : ℝ} {o : Plane} {n : UnitNeedle}
    (hnot : ¬ n.carrier ⊆ Metric.closedBall o R) :
    n.OutsideBall (R - 1) o := by
  rw [not_subset] at hnot
  obtain ⟨x, hx, hxo⟩ := hnot
  rw [Metric.mem_closedBall, not_le] at hxo
  rw [dist_comm] at hxo
  intro y hy
  have hxy : dist x y ≤ 1 := n.dist_le_one_of_mem_carrier hx hy
  have htri : dist o x ≤ dist o y + dist y x := dist_triangle _ _ _
  rw [dist_comm y x] at htri
  linarith

/-- Radial structure repairs the tempting but invalid bare subset inference
`¬ triangle ⊆ B → ¬ base ⊆ B`.  Here it is valid because the ball contains the
vertex and is convex: if the whole base were in the ball, every radial segment
from `o` to the base would be in it too. -/
theorem not_carrier_subset_closedBall_of_not_triangleHull_subset_closedBall
    {R : ℝ} {o : Plane} {n : UnitNeedle} (hR : 0 ≤ R)
    (hnot : ¬ n.triangleHull o ⊆ Metric.closedBall o R) :
    ¬ n.carrier ⊆ Metric.closedBall o R := by
  intro hbase
  apply hnot
  intro y hy
  simp only [triangleHull, mem_iUnion] at hy
  obtain ⟨x, hx, hy⟩ := hy
  exact (convex_closedBall o R).segment_subset
    (by simpa using hR) (hbase hx) hy

/-- A complete triangle escaping radius `R` forces the entire unit base to
avoid the open ball of radius `R-1`. -/
theorem outsideBall_sub_one_of_not_triangleHull_subset_closedBall
    {R : ℝ} {o : Plane} {n : UnitNeedle} (hR : 0 ≤ R)
    (hnot : ¬ n.triangleHull o ⊆ Metric.closedBall o R) :
    n.OutsideBall (R - 1) o :=
  n.outsideBall_sub_one_of_not_subset_closedBall
    (n.not_carrier_subset_closedBall_of_not_triangleHull_subset_closedBall hR hnot)

/-- The ordinary open interior of the complete filled triangle. -/
def triangleInterior (o : Plane) (n : UnitNeedle) : Set Plane :=
  interior (n.triangleHull o)

theorem triangleInterior_isOpen (o : Plane) (n : UnitNeedle) :
    IsOpen (n.triangleInterior o) :=
  isOpen_interior

theorem triangleInterior_measurable (o : Plane) (n : UnitNeedle) :
    MeasurableSet (n.triangleInterior o) :=
  measurableSet_interior

theorem triangleInterior_subset_triangleHull (o : Plane) (n : UnitNeedle) :
    n.triangleInterior o ⊆ n.triangleHull o :=
  interior_subset

/-- Every radial segment from the centre to a point of the base is already in
the filled triangle. -/
theorem segment_to_base_subset_triangleHull (o : Plane) (n : UnitNeedle)
    {x : Plane} (hx : x ∈ n.carrier) :
    segment ℝ o x ⊆ n.triangleHull o := by
  intro y hy
  simp only [triangleHull, mem_iUnion]
  exact ⟨x, ⟨hx, hy⟩⟩

/-- A convenient point on the ray from `o` through `x`, at radial parameter
`rho / dist o x`. -/
def radialPoint (o x : Plane) (rho : ℝ) : Plane :=
  (AffineMap.lineMap o x) (rho / dist o x)

/-- If `x` is at least radius `rho > 0`, the radial point lies on `[o,x]`. -/
theorem radialPoint_mem_segment {o x : Plane} {rho : ℝ}
    (hrho : 0 < rho) (hx : rho ≤ dist o x) :
    radialPoint o x rho ∈ segment ℝ o x := by
  rw [radialPoint, segment_eq_image]
  have hdist : 0 < dist o x := hrho.trans_le hx
  refine ⟨rho / dist o x, ?_, ?_⟩
  · exact ⟨(div_nonneg hrho.le hdist.le), (div_le_one hdist).2 hx⟩
  · change (1 - rho / dist o x) • o + (rho / dist o x) • x =
      (rho / dist o x) • (x - o) + o
    rw [sub_smul, one_smul, smul_sub]
    abel

/-- The preceding radial point has exactly the requested radius. -/
theorem dist_radialPoint {o x : Plane} {rho : ℝ}
    (hrho : 0 < rho) (hx : rho ≤ dist o x) :
    dist (radialPoint o x rho) o = rho := by
  have hdist : 0 < dist o x := hrho.trans_le hx
  rw [radialPoint, dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg hrho.le hdist.le)]
  field_simp

/-- Concrete radial consequence of an outside-ball needle.  The zero-height
hypothesis records the residual Case-II branch (and identifies the ray with the
needle direction); radial containment itself follows from star-shapedness and
outside-ball containment and therefore needs no hidden regularity assumption. -/
theorem zero_height_outside_has_radial_segment
    {rho : ℝ} {o : Plane} {n : UnitNeedle}
    (hrho : 0 < rho) (_hzero : n.height o = 0)
    (hout : n.OutsideBall rho o) :
    ∃ y, segment ℝ o y ⊆ n.triangleHull o ∧ dist y o = rho := by
  let x := n.left
  have hxcarrier : x ∈ n.carrier := left_mem_segment ℝ n.left n.right
  have hrad : rho ≤ dist o x := hout x hxcarrier
  let y := radialPoint o x rho
  have hy : y ∈ segment ℝ o x := radialPoint_mem_segment hrho hrad
  refine ⟨y, ?_, dist_radialPoint hrho hrad⟩
  exact ((convex_segment o x).segment_subset (left_mem_segment ℝ o x) hy).trans
    (n.segment_to_base_subset_triangleHull o hxcarrier)

end UnitNeedle

/-! ## Oriented support-line coordinates -/

namespace UnitNeedle

/-- A point is on the affine support line of an oriented needle exactly when
its normal coordinate relative to the left endpoint vanishes. -/
def OnSupportLine (n : UnitNeedle) (t : ℝ) (K : Plane) : Prop :=
  normalCoord t (K - n.left) = 0

theorem onSupportLine_of_mem_carrier
    {n : UnitNeedle} {t c : ℝ} (hd : n.right - n.left = c • angleVector t)
    {K : Plane} (hK : K ∈ n.carrier) : n.OnSupportLine t K := by
  rw [carrier, segment_eq_image] at hK
  obtain ⟨s, _hs, rfl⟩ := hK
  simp only [OnSupportLine, AffineMap.lineMap_apply]
  have hsub : (1 - s) • n.left + s • n.right - n.left =
      s • (n.right - n.left) := by module
  rw [hsub, hd, smul_smul, normalCoord_smul, normalCoord_angleVector]
  simp

/-- The exact determinant calculation behind the Case-II angular shadow.  If
`K` is where the ray of angle `u` meets the support line of a unit needle with
oriented lift `t`, then the sine of the lifted projective angle is height divided
by the radius of `K`.  This theorem derives the sine identity from the actual
needle coordinates; no sine bound is stored in a structure. -/
theorem abs_sin_eq_height_div_norm_supportPoint
    {o K : Plane} {n : UnitNeedle} {t c u r : ℝ}
    (hc : |c| = 1) (hd : n.right - n.left = c • angleVector t)
    (hKline : n.OnSupportLine t K)
    (hKray : K - o = r • angleVector u) (hr : r ≠ 0) :
    |Real.sin (u - t)| = n.height o / ‖K - o‖ := by
  have hheight := n.height_eq_abs_normalCoord (o := o) hc hd
  have hnormal : normalCoord t (o - n.left) =
      -(r * Real.sin (u - t)) := by
    calc
      normalCoord t (o - n.left) =
          normalCoord t (o - K) + normalCoord t (K - n.left) := by
        rw [← normalCoord_add]
        congr 1
        abel
      _ = normalCoord t (o - K) := by rw [hKline, add_zero]
      _ = normalCoord t (-(K - o)) := by congr 1 <;> abel
      _ = -(normalCoord t (K - o)) := by
        rw [show -(K - o) = (-1 : ℝ) • (K - o) by simp]
        rw [normalCoord_smul]
        ring
      _ = -(r * Real.sin (u - t)) := by
        rw [hKray, normalCoord_smul, normalCoord_angleVector]
  have hnorm : ‖K - o‖ = |r| := by
    rw [hKray, norm_smul, norm_angleVector, mul_one, Real.norm_eq_abs]
  rw [hheight, hnormal, abs_neg, abs_mul, hnorm]
  field_simp [abs_ne_zero.mpr hr]

/-- Canonical-ray version of the support-line identity.  The ray angle is now
computed from the actual support point rather than supplied as extra data. -/
theorem abs_sin_vectorAngle_eq_height_div_norm_supportPoint
    {o K : Plane} {n : UnitNeedle} {t c : ℝ}
    (hc : |c| = 1) (hd : n.right - n.left = c • angleVector t)
    (hKline : n.OnSupportLine t K) (hKo : K ≠ o) :
    |Real.sin (vectorAngle (K - o) - t)| = n.height o / ‖K - o‖ := by
  apply n.abs_sin_eq_height_div_norm_supportPoint hc hd hKline
    (u := vectorAngle (K - o)) (r := ‖K - o‖)
  · exact (norm_smul_angleVector_vectorAngle (sub_ne_zero.mpr hKo)).symm
  · exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hKo)

/-- A strict outside-ball hypothesis immediately gives strict radial control. -/
theorem norm_supportPoint_gt_of_strictOutside
    {rho : ℝ} {o K : Plane} {n : UnitNeedle}
    (hout : n.StrictOutsideBall rho o) (hK : K ∈ n.carrier) :
    rho < ‖K - o‖ := by
  rw [← dist_eq_norm, dist_comm]
  exact hout K hK

/-- The equality case excluded in Case II.  If an interior base point touches
`closedBall o rho` while the whole base avoids the open ball, then the support
line is tangent there, so its support distance (the needle height) is `rho`.
The proof makes the tangency statement explicit by testing small displacements
in both directions along the unit base. -/
theorem height_eq_rho_of_openSegment_eq_dist_of_outside
    {rho : ℝ} {o K : Plane} {n : UnitNeedle}
    (hout : n.OutsideBall rho o)
    (hK : K ∈ openSegment ℝ n.left n.right)
    (hKrho : dist o K = rho) :
    n.height o = rho := by
  rw [openSegment_eq_image_lineMap] at hK
  obtain ⟨s, hs, rfl⟩ := hK
  let v : Plane := n.right - n.left
  let q : Plane := (AffineMap.lineMap n.left n.right s) - o
  have hvnorm : ‖v‖ = 1 := by
    dsimp [v]
    rw [← dist_eq_norm, dist_comm, n.unit_length]
  have hqnorm : ‖q‖ = rho := by
    dsimp [q]
    rw [← hKrho, dist_eq_norm, norm_sub_rev]
  let a : ℝ := inner ℝ q v
  have ha : a = 0 := by
    by_contra hane
    have habs : 0 < |a| := abs_pos.mpr hane
    let d : ℝ := min (min s (1 - s)) |a|
    have hmarg : 0 < min s (1 - s) := lt_min hs.1 (sub_pos.mpr hs.2)
    have hd : 0 < d := lt_min hmarg habs
    have hds : d ≤ s := (min_le_left _ _).trans (min_le_left _ _)
    have hd1s : d ≤ 1 - s := (min_le_left _ _).trans (min_le_right _ _)
    have hda : d ≤ |a| := min_le_right _ _
    have hplus_mem : (AffineMap.lineMap n.left n.right (s + d)) ∈ n.carrier := by
      rw [carrier, segment_eq_image]
      refine ⟨s + d, ⟨by linarith, by linarith⟩, ?_⟩
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      module
    have hminus_mem : (AffineMap.lineMap n.left n.right (s - d)) ∈ n.carrier := by
      rw [carrier, segment_eq_image]
      refine ⟨s - d, ⟨by linarith, by linarith⟩, ?_⟩
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      module
    have hplus : ‖q‖ ≤ ‖q + d • v‖ := by
      calc
        ‖q‖ ≤ ‖o - AffineMap.lineMap n.left n.right (s + d)‖ := by
          simpa [hqnorm, dist_eq_norm] using hout _ hplus_mem
        _ = ‖q + d • v‖ := by
          rw [norm_sub_rev]
          congr 1
          dsimp [q, v]
          simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
          module
    have hminus : ‖q‖ ≤ ‖q - d • v‖ := by
      calc
        ‖q‖ ≤ ‖o - AffineMap.lineMap n.left n.right (s - d)‖ := by
          simpa [hqnorm, dist_eq_norm] using hout _ hminus_mem
        _ = ‖q - d • v‖ := by
          rw [norm_sub_rev]
          congr 1
          dsimp [q, v]
          simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
          module
    have hplus_sq := (sq_le_sq₀ (norm_nonneg q) (norm_nonneg (q + d • v))).2 hplus
    have hminus_sq := (sq_le_sq₀ (norm_nonneg q) (norm_nonneg (q - d • v))).2 hminus
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at hplus_sq
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at hminus_sq
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_comm] at hplus_sq hminus_sq
    rw [real_inner_self_eq_norm_sq v, hvnorm, one_pow] at hplus_sq hminus_sq
    rw [real_inner_comm q v] at hplus_sq hminus_sq
    dsimp [a] at hane hda
    rcases lt_or_gt_of_ne hane with ha_neg | ha_pos
    · rw [abs_of_neg ha_neg] at hda
      nlinarith
    · rw [abs_of_pos ha_pos] at hda
      nlinarith
  have realInnerMul (x y : ℝ) : inner ℝ x y = x * y := by
    change RCLike.re (y * (starRingEnd ℝ) x) = x * y
    simp
    ring
  have hdet_sq : (det v q) ^ 2 = ‖q‖ ^ 2 := by
    have hvinner : inner ℝ v v = v 0 * v 0 + v 1 * v 1 := by
      rw [PiLp.inner_apply, Fin.sum_univ_two]
      simp only [realInnerMul]
    have hqinner : inner ℝ q q = q 0 * q 0 + q 1 * q 1 := by
      rw [PiLp.inner_apply, Fin.sum_univ_two]
      simp only [realInnerMul]
    have hqvinner : inner ℝ q v = q 0 * v 0 + q 1 * v 1 := by
      rw [PiLp.inner_apply, Fin.sum_univ_two]
      simp only [realInnerMul]
    have hid : (det v q) ^ 2 + a ^ 2 =
        inner ℝ v v * inner ℝ q q := by
      rw [hvinner, hqinner]
      dsimp [a, det]
      rw [hqvinner]
      ring
    rw [real_inner_self_eq_norm_sq v, real_inner_self_eq_norm_sq q,
      hvnorm, one_pow, one_mul, ha, zero_pow (by norm_num), add_zero] at hid
    exact hid
  have habsdet : |det v q| = ‖q‖ := by
    nlinarith [sq_abs (det v q), abs_nonneg (det v q), norm_nonneg q]
  calc
    n.height o = |det v (o - n.left)| := by
      simp only [height, det, v]
    _ = |det v (-q + s • v)| := by
      congr 2
      dsimp [q, v]
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      module
    _ = |-(det v q)| := by
      rw [det_add_right, det_smul_right, det_self]
      congr 2
      simp only [det, PiLp.neg_apply]
      ring
    _ = ‖q‖ := by rw [abs_neg, habsdet]
    _ = rho := hqnorm

/-- This is the strict inequality actually needed by the inverse-sine shadow.
It follows from the paper's non-strict outside condition together with the
Case-II strict height bound: equality would force tangency and hence
`height = rho`. -/
theorem norm_openSegmentPoint_gt_of_outside
    {rho : ℝ} {o K : Plane} {n : UnitNeedle}
    (hout : n.OutsideBall rho o) (hh : n.height o < rho)
    (hK : K ∈ openSegment ℝ n.left n.right) :
    rho < ‖K - o‖ := by
  have hle : rho ≤ ‖K - o‖ := by
    rw [← dist_eq_norm, dist_comm]
    exact hout K (openSegment_subset_segment ℝ n.left n.right hK)
  refine lt_of_le_of_ne hle ?_
  intro heq
  have htangent := n.height_eq_rho_of_openSegment_eq_dist_of_outside hout hK
    (by rw [dist_comm, dist_eq_norm, heq])
  linarith

/-- Barycentric coordinates for the union-of-rays definition of the triangle. -/
theorem mem_triangleHull_iff_barycentric {o p : Plane} {n : UnitNeedle} :
    p ∈ n.triangleHull o ↔ ∃ l ∈ Set.Icc (0 : ℝ) 1, ∃ s ∈ Set.Icc (0 : ℝ) 1,
      p - o = l • ((n.left - o) + s • (n.right - n.left)) := by
  simp only [triangleHull, mem_iUnion]
  constructor
  · rintro ⟨x, hx, hp⟩
    change x ∈ segment ℝ n.left n.right at hx
    rw [segment_eq_image] at hx hp
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨l, hl, rfl⟩ := hp
    refine ⟨l, hl, s, hs, ?_⟩
    simp only [AffineMap.lineMap_apply]
    module
  · rintro ⟨l, hl, s, hs, hp⟩
    let x := (1 - s) • n.left + s • n.right
    refine ⟨x, ?_, ?_⟩
    · change x ∈ segment ℝ n.left n.right
      rw [segment_eq_image]
      refine ⟨s, hs, ?_⟩
      rfl
    · rw [segment_eq_image]
      refine ⟨l, hl, ?_⟩
      dsimp [x]
      have hp' : p = l • ((n.left - o) + s • (n.right - n.left)) + o := by
        rw [← hp]
        module
      rw [hp']
      module

/-- An interior point's ray from the vertex meets the relative interior of the
base.  All three barycentric coordinates are proved strict from topological
interiority; no ray-control assumption is hidden here. -/
theorem exists_base_openSegment_on_ray_of_mem_triangleInterior
    {o p : Plane} {n : UnitNeedle} (hp : p ∈ n.triangleInterior o)
    (hh : 0 < n.height o) :
    ∃ K ∈ openSegment ℝ n.left n.right, ∃ l : ℝ,
      0 < l ∧ l < 1 ∧ p - o = l • (K - o) := by
  obtain ⟨l, hl, s, hs, hpl⟩ := n.mem_triangleHull_iff_barycentric.mp
    (n.triangleInterior_subset_triangleHull o hp)
  let a : Plane := n.left - o
  let v : Plane := n.right - n.left
  have hD : det v a ≠ 0 := by
    intro hzero
    have hz : n.height o = 0 := by
      rw [show n.height o = |-(det v a)| by
        simp only [height, a, v, det, PiLp.sub_apply]
        congr 1
        ring, hzero]
      norm_num
    linarith
  obtain ⟨e, he0, heball⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp hp)
  have radial (y : Plane) (hy : y ∈ n.triangleHull o) :
      ∃ q ∈ Set.Icc (0 : ℝ) 1, det v (y - o) = q * det v a := by
    obtain ⟨q, hq, r, hr, hyr⟩ := n.mem_triangleHull_iff_barycentric.mp hy
    refine ⟨q, hq, ?_⟩
    rw [hyr]
    change det v (q • (a + r • v)) = q * det v a
    rw [det_smul_right, det_add_right, det_smul_right, det_self]
    ring
  have hl0 : 0 < l := by
    rcases lt_or_eq_of_le hl.1 with h | h
    · exact h
    · subst l
      have hp0 : p = o := sub_eq_zero.mp (by simpa using hpl)
      have ha0 : 0 < ‖a‖ := norm_pos_iff.mpr (fun ha => hD (by simp [ha, det]))
      let d := min (e / (2 * ‖a‖)) (1 / 2)
      have hd0 : 0 < d := lt_min (div_pos he0 (by positivity)) (by norm_num)
      let y := o - d • a
      have hydist : dist y p < e := by
        rw [hp0]
        simp only [y, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
          Real.norm_eq_abs, abs_of_pos hd0]
        calc
          d * ‖a‖ ≤ (e / (2 * ‖a‖)) * ‖a‖ :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)
          _ = e / 2 := by field_simp
          _ < e := half_lt_self he0
      obtain ⟨q, hq, hqdet⟩ := radial y (heball hydist)
      have heq : -d = q := by
        apply mul_right_cancel₀ hD
        rw [← hqdet]
        simp [y, a, v, det]
        ring
      linarith [hq.1]
  have hl1 : l < 1 := by
    rcases lt_or_eq_of_le hl.2 with h | h
    · exact h
    · have hl_eq : l = 1 := h
      have hw : a + s • v ≠ 0 := by
        intro hz
        have hz' : det v (a + s • v) = 0 := by rw [hz]; simp [det]
        rw [det_add_right, det_smul_right, det_self, mul_zero, add_zero] at hz'
        exact hD hz'
      let d := min (e / (2 * ‖a + s • v‖)) (1 / 2)
      have hn : 0 < ‖a + s • v‖ := norm_pos_iff.mpr hw
      have hd0 : 0 < d := lt_min (div_pos he0 (by positivity)) (by norm_num)
      let y := p + d • (a + s • v)
      have hydist : dist y p < e := by
        simp only [y, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs, abs_of_pos hd0]
        calc
          d * ‖a + s • v‖ ≤ (e / (2 * ‖a + s • v‖)) * ‖a + s • v‖ :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)
          _ = e / 2 := by field_simp
          _ < e := half_lt_self he0
      obtain ⟨q, hq, hqdet⟩ := radial y (heball hydist)
      have heq : 1 + d = q := by
        apply mul_right_cancel₀ hD
        rw [← hqdet, show y - o = (p - o) + d • (a + s • v) by dsimp [y]; abel,
          hpl, hl_eq]
        simp [a, v, det]
        ring
      linarith [hq.2]
  have basecoord (y : Plane) (hy : y ∈ n.triangleHull o)
      (hdet : det v (y - o) = l * det v a) :
      ∃ r ∈ Set.Icc (0 : ℝ) 1, det a (y - o) = l * r * det a v := by
    obtain ⟨q, hq, r, hr, hyr⟩ := n.mem_triangleHull_iff_barycentric.mp hy
    have hqeq : q = l := by
      have heq : q * det v a = l * det v a := by
        rw [← hdet, hyr]
        change q * det v a = det v (q • (a + r • v))
        rw [det_smul_right, det_add_right, det_smul_right, det_self]
        ring
      exact mul_right_cancel₀ hD heq
    refine ⟨r, hr, ?_⟩
    rw [hyr, hqeq]
    change det a (l • (a + r • v)) = l * r * det a v
    rw [det_smul_right, det_add_right, det_self, det_smul_right]
    ring
  have hda : det a v ≠ 0 := by
    rw [det_swap]
    exact neg_ne_zero.mpr hD
  have hs0 : 0 < s := by
    rcases lt_or_eq_of_le hs.1 with h | h
    · exact h
    · subst s
      let d := min (e / 2) (l / 2)
      have hd0 : 0 < d := lt_min (half_pos he0) (half_pos hl0)
      let y := p - d • v
      have hydist : dist y p < e := by
        simp only [y, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
          Real.norm_eq_abs, abs_of_pos hd0]
        have hvn : ‖v‖ = 1 := by dsimp [v]; rw [← dist_eq_norm, dist_comm, n.unit_length]
        rw [hvn, mul_one]
        exact (min_le_left _ _).trans_lt (half_lt_self he0)
      have hdet : det v (y - o) = l * det v a := by
        rw [show y - o = (p - o) - d • v by dsimp [y]; abel, hpl]
        simp [a, v, det]
        ring
      obtain ⟨r, hr, hrdet⟩ := basecoord y (heball hydist) hdet
      have heq : -d = l * r := by
        apply mul_right_cancel₀ hda
        rw [← hrdet, show y - o = (p - o) - d • v by dsimp [y]; abel, hpl]
        simp [a, v, det]
        ring
      nlinarith [hr.1]
  have hs1 : s < 1 := by
    rcases lt_or_eq_of_le hs.2 with h | h
    · exact h
    · have hs_eq : s = 1 := h
      let d := min (e / 2) (l / 2)
      have hd0 : 0 < d := lt_min (half_pos he0) (half_pos hl0)
      let y := p + d • v
      have hydist : dist y p < e := by
        simp only [y, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs, abs_of_pos hd0]
        have hvn : ‖v‖ = 1 := by dsimp [v]; rw [← dist_eq_norm, dist_comm, n.unit_length]
        rw [hvn, mul_one]
        exact (min_le_left _ _).trans_lt (half_lt_self he0)
      have hdet : det v (y - o) = l * det v a := by
        rw [show y - o = (p - o) + d • v by dsimp [y]; abel, hpl]
        simp [a, v, det]
        ring
      obtain ⟨r, hr, hrdet⟩ := basecoord y (heball hydist) hdet
      have heq : l + d = l * r := by
        apply mul_right_cancel₀ hda
        rw [← hrdet, show y - o = (p - o) + d • v by dsimp [y]; abel, hpl, hs_eq]
        simp [a, v, det]
        ring
      nlinarith [hr.2]
  let K := (1 - s) • n.left + s • n.right
  refine ⟨K, ?_, l, hl0, hl1, ?_⟩
  · rw [openSegment_eq_image_lineMap]
    refine ⟨s, ⟨hs0, hs1⟩, ?_⟩
    simp only [AffineMap.lineMap_apply]
    dsimp [K]
    module
  · rw [hpl]
    dsimp [K]
    module

end UnitNeedle

/-- The residual radial fan formed from the chosen left endpoints.  For
zero-height needles either endpoint determines the same projective base line;
using `left` avoids an additional orientation choice. -/
def residualFan {E : Set Plane} (K : StarShapedKakeya E)
    (R : Set Direction) : Set Plane :=
  ⋃ θ ∈ R, segment ℝ K.center (K.needleFamily θ).left

namespace StarShapedKakeya

variable {E : Set Plane} (K : StarShapedKakeya E)

/-- The residual fan is unconditionally contained in the Kakeya set. -/
theorem residualFan_subset (R : Set Direction) :
    residualFan K R ⊆ E := by
  intro y hy
  simp only [residualFan, mem_iUnion] at hy
  obtain ⟨θ, hθ, hy⟩ := hy
  exact K.star
    (K.needleFamily_carrier_subset θ
      (left_mem_segment ℝ (K.needleFamily θ).left (K.needleFamily θ).right)) hy

/-- Every zero-height outside-ball residual direction contributes the whole
radial segment through radius `rho` to the residual fan. -/
theorem residualFan_reaches_radius
    {rho : ℝ} (hrho : 0 < rho) (R : Set Direction)
    (_hzero : ∀ θ ∈ R, (K.needleFamily θ).height K.center = 0)
    (hout : ∀ θ ∈ R, (K.needleFamily θ).OutsideBall rho K.center)
    {θ : Direction} (hθ : θ ∈ R) :
    ∃ y, segment ℝ K.center y ⊆ residualFan K R ∧
      dist y K.center = rho := by
  -- The radial point constructed by the theorem used the left endpoint; unfold
  -- that construction directly to retain membership in the declared fan.
  let z := UnitNeedle.radialPoint K.center (K.needleFamily θ).left rho
  have hleft : (K.needleFamily θ).left ∈ (K.needleFamily θ).carrier :=
    left_mem_segment ℝ _ _
  have hrad := hout θ hθ _ hleft
  have hz : z ∈ segment ℝ K.center (K.needleFamily θ).left :=
    UnitNeedle.radialPoint_mem_segment hrho hrad
  refine ⟨z, ?_, UnitNeedle.dist_radialPoint hrho hrad⟩
  intro w hw
  simp only [residualFan, mem_iUnion]
  refine ⟨θ, hθ, ?_⟩
  exact (convex_segment K.center (K.needleFamily θ).left).segment_subset
    (left_mem_segment ℝ _ _) hz hw

end StarShapedKakeya

/-! ## Oriented residual lifts and angular outer measure -/

/-- The quotient from oriented real angles to projective directions. -/
def directionQuotient (t : ℝ) : Direction := (t : Direction)

/-- Metric one-dimensional angular outer measure.  This formulation is useful
for arbitrary (not necessarily Haar measurable) residual direction sets. -/
def directionAngleOuter (A : Set Direction) : ENNReal := μH[1] A

/-- The quotient map from oriented angles to projective directions is
`1`-Lipschitz.  This is the cut-free fact needed for arbitrary residual sets. -/
theorem directionQuotient_lipschitzWith :
    LipschitzWith 1 directionQuotient := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro s t
  change dist (s : Direction) (t : Direction) ≤ (1 : ℝ) * dist s t
  rw [one_mul, dist_eq_norm, ← QuotientAddGroup.mk_sub, Real.dist_eq]
  exact QuotientAddGroup.norm_mk_le_norm

/-- A one-Lipschitz oriented lift controls angular outer measure. -/
theorem directionAngleOuter_image_directionQuotient_le (Theta : Set ℝ) :
    directionAngleOuter (directionQuotient '' Theta) ≤ volume.toOuterMeasure Theta := by
  rw [directionAngleOuter, ← MeasureTheory.hausdorffMeasure_real]
  simpa using directionQuotient_lipschitzWith.hausdorffMeasure_image_le
    (d := (1 : ℝ)) zero_le_one Theta

/-! ### Haar length versus metric Hausdorff length

The normalization in `μH[1]` is the diameter normalization, so on the
projective circle it agrees exactly with Haar length (there is no factor `2`).
We pin down the Haar scalar on a half-period arc, where the quotient has an
isometric real lift. -/

theorem directionQuotient_isometryOn_half :
    ∀ ⦃x⦄, x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) →
      ∀ ⦃y⦄, y ∈ Set.Icc (0 : ℝ) (Real.pi / 2) →
        dist (directionQuotient x) (directionQuotient y) = dist x y := by
  intro x hx y hy
  change dist (x : Direction) (y : Direction) = dist x y
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, Real.dist_eq]
  apply (AddCircle.norm_coe_eq_abs_iff (p := Real.pi) Real.pi_ne_zero).2
  rw [abs_of_pos Real.pi_pos]
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem directionQuotient_image_Icc_half :
    directionQuotient '' Set.Icc (0 : ℝ) (Real.pi / 2) =
      Metric.closedBall ((Real.pi / 4 : ℝ) : Direction) (Real.pi / 4) := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    change dist (x : Direction) ((Real.pi / 4 : ℝ) : Direction) ≤ Real.pi / 4
    rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
    rw [(AddCircle.norm_coe_eq_abs_iff (p := Real.pi) Real.pi_ne_zero).2]
    · rw [abs_le]
      constructor <;> linarith [hx.1, hx.2]
    · rw [abs_of_pos Real.pi_pos, abs_le]
      constructor <;> linarith [hx.1, hx.2, Real.pi_pos]
  · obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    intro hx
    rw [Metric.mem_closedBall, dist_eq_norm, ← QuotientAddGroup.mk_sub,
      AddCircle.norm_eq] at hx
    let z : ℝ := x - Real.pi / 4 -
      (round (Real.pi⁻¹ * (x - Real.pi / 4)) : ℝ) * Real.pi
    refine ⟨Real.pi / 4 + z, ?_, ?_⟩
    · dsimp [z] at hx ⊢
      rw [abs_le] at hx
      constructor <;> linarith [hx.1, hx.2]
    · change ((Real.pi / 4 + z : ℝ) : Direction) = (x : Direction)
      simp only [z, AddCircle.coe_add, AddCircle.coe_sub]
      rw [← zsmul_eq_mul, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero,
        sub_zero, add_sub_cancel]

theorem directionAngleOuter_image_Icc_half :
    directionAngleOuter (directionQuotient '' Set.Icc (0 : ℝ) (Real.pi / 2)) =
      ENNReal.ofReal (Real.pi / 2) := by
  let f : Set.Icc (0 : ℝ) (Real.pi / 2) → Direction := fun x => directionQuotient x
  have hf : Isometry f := by
    rw [isometry_iff_dist_eq]
    exact fun x y => directionQuotient_isometryOn_half x.property y.property
  have hsub : μH[(1 : ℝ)] (Set.univ : Set (Set.Icc (0 : ℝ) (Real.pi / 2))) =
      μH[(1 : ℝ)] (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    rw [← (isometry_subtype_coe : Isometry
      (fun x : Set.Icc (0 : ℝ) (Real.pi / 2) => (x : ℝ))).hausdorffMeasure_image
        (Or.inl zero_le_one) Set.univ]
    congr
    ext x
    simp
  rw [directionAngleOuter]
  rw [show directionQuotient '' Set.Icc (0 : ℝ) (Real.pi / 2) =
      f '' Set.univ by ext x; simp [f]]
  rw [hf.hausdorffMeasure_image (Or.inl zero_le_one), hsub,
    MeasureTheory.hausdorffMeasure_real, Real.volume_Icc]
  congr 1
  ring

theorem directionOuterMeasure_eq_directionAngleOuter (A : Set Direction) :
    StarShapedKakeya.directionOuterMeasure A = directionAngleOuter A := by
  let ν : Measure Direction := μH[(1 : ℝ)]
  have hνuniv : ν Set.univ < ⊤ := by
    calc
      ν Set.univ = directionAngleOuter
          (directionQuotient '' Set.Icc (0 : ℝ) Real.pi) := by
        congr 1
        apply (Set.eq_univ_of_forall _).symm
        intro q
        let x : ℝ := AddCircle.equivIco Real.pi 0 q
        exact ⟨x, ⟨(AddCircle.equivIco Real.pi 0 q).property.1,
          by simpa using (AddCircle.equivIco Real.pi 0 q).property.2.le⟩,
          AddCircle.coe_equivIco⟩
      _ ≤ volume.toOuterMeasure (Set.Icc (0 : ℝ) Real.pi) :=
        directionAngleOuter_image_directionQuotient_le _
      _ = ENNReal.ofReal Real.pi := by
        rw [Measure.toOuterMeasure_apply, Real.volume_Icc]
        congr 1
        ring
      _ < ⊤ := ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure ν := ⟨hνuniv⟩
  have hνscalar := MeasureTheory.Measure.isAddInvariant_eq_smul_of_compactSpace ν volume
  let c : NNReal := ν.addHaarScalarFactor volume
  have hscalar : ν = c • volume := by simpa [c] using hνscalar
  have harcH := directionAngleOuter_image_Icc_half
  have harcV : volume (directionQuotient '' Set.Icc (0 : ℝ) (Real.pi / 2)) =
      ENNReal.ofReal (Real.pi / 2) := by
    rw [directionQuotient_image_Icc_half, AddCircle.volume_closedBall]
    congr 2
    rw [min_eq_right]
    · ring
    · linarith [Real.pi_pos]
  have hc : (c : ENNReal) = 1 := by
    have heq := congrArg (fun μ : Measure Direction =>
      μ (directionQuotient '' Set.Icc (0 : ℝ) (Real.pi / 2))) hscalar
    change directionAngleOuter
      (directionQuotient '' Set.Icc (0 : ℝ) (Real.pi / 2)) =
        (c • volume) (directionQuotient '' Set.Icc (0 : ℝ) (Real.pi / 2)) at heq
    rw [Measure.smul_apply, harcV, harcH] at heq
    have hhalf0 : ENNReal.ofReal (Real.pi / 2) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have heq' : (c : ENNReal) * ENNReal.ofReal (Real.pi / 2) =
        1 * ENNReal.ofReal (Real.pi / 2) := by
      simpa [ENNReal.smul_def] using heq.symm
    exact (ENNReal.mul_left_inj hhalf0 ENNReal.ofReal_ne_top).mp heq'
  have hcNN : c = 1 := by
    apply NNReal.eq
    exact_mod_cast hc
  rw [hcNN, one_smul] at hscalar
  change volume.toOuterMeasure A = ν.toOuterMeasure A
  rw [hscalar]

theorem directionOuterMeasure_le_directionAngleOuter (A : Set Direction) :
    StarShapedKakeya.directionOuterMeasure A ≤ directionAngleOuter A :=
  (directionOuterMeasure_eq_directionAngleOuter A).le

/-- The actual oriented residual lift: use the arguments of the selected left
endpoints, not an externally chosen orientation. -/
def residualAngles {E : Set Plane} (K : StarShapedKakeya E)
    (R : Set Direction) : Set ℝ :=
  vectorAngle '' ((fun theta => (K.needleFamily theta).left - K.center) '' R)

/-! ## Projective-angle kernel -/

/-- On the projective angle circle (period `π`), the sine of metric distance is
the absolute sine of any pair of real lifts. -/
theorem sin_projectiveDist_eq_abs_sin (u t : ℝ) :
    Real.sin (dist (u : Direction) (t : Direction)) = |Real.sin (u - t)| := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, AddCircle.norm_eq]
  let n : ℤ := round (Real.pi⁻¹ * (u - t))
  let z : ℝ := u - t - (n : ℝ) * Real.pi
  change Real.sin |z| = |Real.sin (u - t)|
  have hzhalf : |z| ≤ Real.pi / 2 := by
    have h := AddCircle.norm_le_half_period Real.pi
      (x := ((u - t : ℝ) : Direction)) Real.pi_ne_zero
    rw [AddCircle.norm_eq, abs_of_pos Real.pi_pos] at h
    exact h
  rw [← Real.abs_sin_eq_sin_abs_of_abs_le_pi
    (hzhalf.trans (by linarith [Real.pi_pos]))]
  rw [show z = (u - t) - (n : ℝ) * Real.pi by rfl,
    Real.sin_sub_int_mul_pi, abs_mul]
  simp

/-- A zero-height outside needle has exactly its declared projective direction
as the radial direction of either nonzero endpoint. -/
theorem UnitNeedle.rayDirection_left_eq_of_height_zero
    {theta : Direction} {rho : ℝ} {o : Plane} {n : UnitNeedle}
    (hrho : 0 < rho) (hzero : n.height o = 0)
    (hdir : n.HasDirection theta) (hout : n.OutsideBall rho o) :
    rayDirection o n.left = theta := by
  obtain ⟨t, ht, c, hc, hd⟩ := n.hasDirection_oriented_lift hdir
  have hleft : n.left ∈ n.carrier := left_mem_segment ℝ _ _
  have hlo : n.left ≠ o := by
    intro h
    have hbad := hout n.left hleft
    rw [h, dist_self] at hbad
    linarith
  have hs : Real.sin (dist (rayDirection o n.left) theta) = 0 := by
    rw [rayDirection, ht.symm]
    change Real.sin (dist ((vectorAngle (n.left - o) : ℝ) : Direction)
      ((t : ℝ) : Direction)) = 0
    rw [sin_projectiveDist_eq_abs_sin]
    rw [n.abs_sin_vectorAngle_eq_height_div_norm_supportPoint hc hd
      (by simp [UnitNeedle.OnSupportLine, normalCoord, det]) hlo, hzero, zero_div]
  have hdpi : dist (rayDirection o n.left) theta ≤ Real.pi / 2 := by
    simpa only [dist_eq_norm, abs_of_pos Real.pi_pos] using
      AddCircle.norm_le_half_period Real.pi
        (x := (rayDirection o n.left - theta)) Real.pi_ne_zero
  have heq : Real.arcsin (Real.sin (dist (rayDirection o n.left) theta)) =
      dist (rayDirection o n.left) theta :=
    Real.arcsin_sin ((neg_nonpos.mpr (by positivity)).trans dist_nonneg) hdpi
  rw [hs, Real.arcsin_zero] at heq
  exact dist_eq_zero.mp heq.symm

namespace StarShapedKakeya

variable {E : Set Plane} (K : StarShapedKakeya E)

/-- The oriented residual lift projects onto exactly the residual projective
set.  The zero-height proof uses the actual chosen needle and no measurable
selection or ray-control hypothesis. -/
theorem image_directionQuotient_residualAngles
    {rho : ℝ} (hrho : 0 < rho) (R : Set Direction)
    (hzero : ∀ theta ∈ R, (K.needleFamily theta).height K.center = 0)
    (hout : ∀ theta ∈ R, (K.needleFamily theta).OutsideBall rho K.center) :
    directionQuotient '' residualAngles K R = R := by
  apply Set.Subset.antisymm
  · rintro q ⟨t, ⟨_v, ⟨theta, htheta, rfl⟩, rfl⟩, rfl⟩
    rw [show directionQuotient
      (vectorAngle ((K.needleFamily theta).left - K.center)) =
        rayDirection K.center (K.needleFamily theta).left by rfl]
    rw [(K.needleFamily theta).rayDirection_left_eq_of_height_zero hrho
      (hzero theta htheta) (K.needleFamily_hasDirection theta) (hout theta htheta)]
    exact htheta
  · intro theta htheta
    refine ⟨vectorAngle ((K.needleFamily theta).left - K.center), ?_, ?_⟩
    · exact ⟨_, ⟨theta, htheta, rfl⟩, rfl⟩
    · change rayDirection K.center (K.needleFamily theta).left = theta
      exact (K.needleFamily theta).rayDirection_left_eq_of_height_zero hrho
        (hzero theta htheta) (K.needleFamily_hasDirection theta) (hout theta htheta)

/-- Consequently the real oriented residual lift has at least the angular
outer measure of the projective residual set. -/
theorem directionAngleOuter_le_residualAngles
    {rho : ℝ} (hrho : 0 < rho) (R : Set Direction)
    (hzero : ∀ theta ∈ R, (K.needleFamily theta).height K.center = 0)
    (hout : ∀ theta ∈ R, (K.needleFamily theta).OutsideBall rho K.center) :
    directionAngleOuter R ≤ volume.toOuterMeasure (residualAngles K R) := by
  calc
    directionAngleOuter R = directionAngleOuter (directionQuotient '' residualAngles K R) :=
      congrArg directionAngleOuter (K.image_directionQuotient_residualAngles hrho R hzero hout).symm
    _ ≤ volume.toOuterMeasure (residualAngles K R) :=
      directionAngleOuter_image_directionQuotient_le _

/-- The standard-cut residual-angle sector is contained in the actual fan. -/
theorem polarSector_residualAngles_subset_residualFan
    {rho : ℝ} (hrho : 0 < rho) (R : Set Direction)
    (hout : ∀ theta ∈ R, (K.needleFamily theta).OutsideBall rho K.center) :
    euclideanPolarSector K.center rho (residualAngles K R) ⊆ residualFan K R := by
  rintro z ⟨r, hr, u, ⟨⟨v, ⟨theta, htheta, rfl⟩, rfl⟩, _hcut⟩, rfl⟩
  have hleft : (K.needleFamily theta).left ∈ (K.needleFamily theta).carrier :=
    left_mem_segment ℝ _ _
  have hreach : rho ≤ ‖(K.needleFamily theta).left - K.center‖ := by
    rw [← dist_eq_norm, dist_comm]
    exact hout theta htheta _ hleft
  have hne : (K.needleFamily theta).left - K.center ≠ 0 := by
    intro h
    rw [h, norm_zero] at hreach
    linarith
  let s := r / ‖(K.needleFamily theta).left - K.center‖
  have hnorm : 0 < ‖(K.needleFamily theta).left - K.center‖ := norm_pos_iff.mpr hne
  have hs : s ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hr.1 hnorm.le, (div_le_one hnorm).2 (hr.2.trans hreach)⟩
  simp only [residualFan, mem_iUnion]
  refine ⟨theta, htheta, ?_⟩
  rw [segment_eq_image]
  refine ⟨s, hs, ?_⟩
  let a := angleVector (vectorAngle ((K.needleFamily theta).left - K.center))
  have hrec : ‖(K.needleFamily theta).left - K.center‖ • a =
      (K.needleFamily theta).left - K.center := by
    exact norm_smul_angleVector_vectorAngle hne
  have hsNorm : s * ‖(K.needleFamily theta).left - K.center‖ = r := by
    dsimp [s]
    exact div_mul_cancel₀ r hnorm.ne'
  change (1 - s) • K.center + s • (K.needleFamily theta).left =
    K.center + r • a
  rw [← hsNorm, mul_smul, hrec]
  module

/-- Removing the possible endpoint `π` from canonical complex arguments does
not decrease their Lebesgue outer measure. -/
theorem residualAngles_outerMeasure_le_angleSetOuter (R : Set Direction) :
    volume.toOuterMeasure (residualAngles K R) ≤ angleSetOuter (residualAngles K R) := by
  have hsub : residualAngles K R ⊆
      (residualAngles K R ∩ Set.Ioo (-Real.pi) Real.pi) ∪ {Real.pi} := by
    rintro u ⟨v, hv, rfl⟩
    have hlo : -Real.pi < vectorAngle v := Complex.neg_pi_lt_arg _
    have hhi : vectorAngle v ≤ Real.pi := Complex.arg_le_pi _
    rcases hhi.eq_or_lt with heq | hlt
    · exact Or.inr (Set.mem_singleton_iff.mpr heq)
    · exact Or.inl ⟨⟨v, hv, rfl⟩, hlo, hlt⟩
  calc
    volume.toOuterMeasure (residualAngles K R) ≤
        volume.toOuterMeasure
          ((residualAngles K R ∩ Set.Ioo (-Real.pi) Real.pi) ∪ {Real.pi}) :=
      volume.toOuterMeasure.mono hsub
    _ ≤ volume.toOuterMeasure (residualAngles K R ∩ Set.Ioo (-Real.pi) Real.pi) +
        volume.toOuterMeasure ({Real.pi} : Set ℝ) := measure_union_le _ _
    _ = angleSetOuter (residualAngles K R) := by simp [angleSetOuter]

/-- The residual fan has the expected polar outer-area lower bound. -/
theorem residualFan_outerMeasure_lower
    {rho : ℝ} (hrho : 0 < rho) (R : Set Direction)
    (hzero : ∀ theta ∈ R, (K.needleFamily theta).height K.center = 0)
    (hout : ∀ theta ∈ R, (K.needleFamily theta).OutsideBall rho K.center) :
    ENNReal.ofReal (rho ^ 2 / 2) * directionAngleOuter R ≤
      volume.toOuterMeasure (residualFan K R) := by
  calc
    ENNReal.ofReal (rho ^ 2 / 2) * directionAngleOuter R ≤
        ENNReal.ofReal (rho ^ 2 / 2) * volume.toOuterMeasure (residualAngles K R) :=
      mul_le_mul_left' (K.directionAngleOuter_le_residualAngles hrho R hzero hout) _
    _ ≤ ENNReal.ofReal (rho ^ 2 / 2) * angleSetOuter (residualAngles K R) :=
      mul_le_mul_left' (K.residualAngles_outerMeasure_le_angleSetOuter R) _
    _ ≤ volume.toOuterMeasure (euclideanPolarSector K.center rho (residualAngles K R)) :=
      euclideanPolarSector_outerMeasure_ge K.center hrho.le _
    _ ≤ volume.toOuterMeasure (residualFan K R) :=
      volume.toOuterMeasure.mono
        (K.polarSector_residualAngles_subset_residualFan hrho R hout)

end StarShapedKakeya

/-- The elementary inverse-sine step used after the Euclidean determinant
calculation `sin d = delta / |K|`. -/
theorem angle_lt_arcsin_of_sin_lt
    {d delta rho : ℝ} (hd0 : 0 ≤ d) (hdpi : d ≤ Real.pi / 2)
    (hrho : 0 < rho) (hdelta0 : 0 ≤ delta) (hdeltarho : delta ≤ rho)
    (hsin : Real.sin d < delta / rho) :
    d < Real.arcsin (delta / rho) := by
  have harg0 : 0 ≤ delta / rho := div_nonneg hdelta0 hrho.le
  have harg1 : delta / rho ≤ 1 := (div_le_one hrho).2 hdeltarho
  rw [← Real.arcsin_sin (by linarith [Real.pi_pos]) hdpi]
  exact Real.arcsin_lt_arcsin (Real.neg_one_le_sin d) hsin harg1

/-- Two one-sided sine-coordinate estimates around a common projective ray
imply the desired strict sum bound. -/
theorem projective_distance_lt_arcsin_add_of_common_ray
    {theta₁ theta₂ beta : Direction} {d₁ d₂ delta₁ delta₂ rho : ℝ}
    (hd₁ : dist theta₁ beta = d₁) (hd₂ : dist beta theta₂ = d₂)
    (hd₁0 : 0 ≤ d₁) (hd₁pi : d₁ ≤ Real.pi / 2)
    (hd₂0 : 0 ≤ d₂) (hd₂pi : d₂ ≤ Real.pi / 2)
    (hrho : 0 < rho)
    (hdelta₁0 : 0 ≤ delta₁) (hdelta₁rho : delta₁ ≤ rho)
    (hdelta₂0 : 0 ≤ delta₂) (hdelta₂rho : delta₂ ≤ rho)
    (hsin₁ : Real.sin d₁ < delta₁ / rho)
    (hsin₂ : Real.sin d₂ < delta₂ / rho) :
    dist theta₁ theta₂ <
      Real.arcsin (delta₁ / rho) + Real.arcsin (delta₂ / rho) := by
  have h₁ := angle_lt_arcsin_of_sin_lt hd₁0 hd₁pi hrho
    hdelta₁0 hdelta₁rho hsin₁
  have h₂ := angle_lt_arcsin_of_sin_lt hd₂0 hd₂pi hrho
    hdelta₂0 hdelta₂rho hsin₂
  calc
    dist theta₁ theta₂ ≤ dist theta₁ beta + dist beta theta₂ := dist_triangle _ _ _
    _ = d₁ + d₂ := by rw [hd₁, hd₂]
    _ < _ := add_lt_add h₁ h₂

/-- Exact local Euclidean-to-projective interface still required for a family
of complete triangles: every interior point's radial projective direction lies
in the indicated inverse-sine shadow.  This is deliberately a pointwise
single-triangle predicate, not an assumption of the desired pairwise
conclusion. -/
def TriangleRayControlled (rayDirection : Plane → Direction) (theta : Direction)
    (delta rho : ℝ) (o : Plane) (n : UnitNeedle) : Prop :=
  ∀ p ∈ n.triangleInterior o,
    dist (rayDirection p) theta < Real.arcsin (delta / rho)

/-- The local ray-control predicate instantiated from the actual Euclidean
triangle.  Its strictness comes exactly from the strict outside-closed-ball
hypothesis, not from an assumed angular estimate. -/
theorem UnitNeedle.triangleRayControlled_of_outside
    {theta : Direction} {rho : ℝ} {o : Plane} {n : UnitNeedle}
    (hrho : 0 < rho) (hh : 0 < n.height o) (hhrho : n.height o < rho)
    (hdir : n.HasDirection theta) (hout : n.OutsideBall rho o) :
    TriangleRayControlled (rayDirection o) theta (n.height o) rho o n := by
  obtain ⟨t, ht, c, hc, hd⟩ := n.hasDirection_oriented_lift hdir
  intro p hp
  obtain ⟨K, hK, l, hl0, _hl1, hpK⟩ :=
    n.exists_base_openSegment_on_ray_of_mem_triangleInterior hp hh
  have hKcarrier : K ∈ n.carrier :=
    openSegment_subset_segment ℝ n.left n.right hK
  have hKrho : rho < ‖K - o‖ :=
    n.norm_openSegmentPoint_gt_of_outside hout hhrho hK
  have hKo : K ≠ o := by
    intro h
    subst K
    simp only [sub_self, norm_zero] at hKrho
    linarith
  have hpangle : vectorAngle (p - o) = vectorAngle (K - o) := by
    rw [hpK, vectorAngle_pos_smul hl0]
  have hsine :
      Real.sin (dist (rayDirection o p) theta) = n.height o / ‖K - o‖ := by
    rw [rayDirection, ht.symm]
    change Real.sin (dist ((vectorAngle (p - o) : ℝ) : Direction)
      ((t : ℝ) : Direction)) = _
    rw [sin_projectiveDist_eq_abs_sin, hpangle]
    exact n.abs_sin_vectorAngle_eq_height_div_norm_supportPoint hc hd
      (n.onSupportLine_of_mem_carrier hd hKcarrier) hKo
  have hdpi : dist (rayDirection o p) theta ≤ Real.pi / 2 := by
    simpa only [dist_eq_norm, abs_of_pos Real.pi_pos] using
      AddCircle.norm_le_half_period Real.pi
        (x := (rayDirection o p - theta)) Real.pi_ne_zero
  have hslt : Real.sin (dist (rayDirection o p) theta) < n.height o / rho := by
    rw [hsine]
    exact div_lt_div_of_pos_left hh hrho hKrho
  exact angle_lt_arcsin_of_sin_lt dist_nonneg hdpi hrho hh.le hhrho.le hslt

/-- Disjoint weighted direction intervals force the complete open triangle
interiors to be disjoint, once each triangle's local ray-coordinate estimate
has been established. -/
theorem pairwise_disjoint_triangleInterior
    {ι : Type*} (rayDirection : Plane → Direction)
    (theta : ι → Direction) (delta H : ι → ℝ) (rho : ℝ)
    (o : Plane) (needle : ι → UnitNeedle)
    (hcontrol : ∀ i, TriangleRayControlled rayDirection (theta i)
      (delta i) rho o (needle i))
    (hweight : ∀ i, Real.arcsin (delta i / rho) ≤ H i)
    (harcs : Pairwise (fun i j => Disjoint
      (Metric.ball (theta i) (H i)) (Metric.ball (theta j) (H j)))) :
    Pairwise (fun i j => Disjoint
      ((needle i).triangleInterior o) ((needle j).triangleInterior o)) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro p hp hq
  have hip : rayDirection p ∈ Metric.ball (theta i) (H i) := by
    rw [Metric.mem_ball]
    exact (hcontrol i p hp).trans_le (hweight i)
  have hjp : rayDirection p ∈ Metric.ball (theta j) (H j) := by
    rw [Metric.mem_ball]
    exact (hcontrol j p hq).trans_le (hweight j)
  exact (Set.disjoint_left.mp (harcs hij)) hip hjp

/-- Consequently, weighted direction balls alone imply disjointness of the
actual selected triangle interiors; callers no longer provide a separate
`TriangleRayControlled` support hypothesis. -/
theorem pairwise_disjoint_triangleInterior_of_outside
    {ι : Type*} (theta : ι → Direction) (H : ι → ℝ) (rho : ℝ)
    (o : Plane) (needle : ι → UnitNeedle)
    (hrho : 0 < rho)
    (hh : ∀ i, 0 < (needle i).height o)
    (hhrho : ∀ i, (needle i).height o < rho)
    (hdir : ∀ i, (needle i).HasDirection (theta i))
    (hout : ∀ i, (needle i).OutsideBall rho o)
    (hweight : ∀ i, Real.arcsin ((needle i).height o / rho) ≤ H i)
    (harcs : Pairwise (fun i j => Disjoint
      (Metric.ball (theta i) (H i)) (Metric.ball (theta j) (H j)))) :
    Pairwise (fun i j => Disjoint
      ((needle i).triangleInterior o) ((needle j).triangleInterior o)) := by
  apply pairwise_disjoint_triangleInterior (rayDirection o) theta
    (fun i => (needle i).height o) H rho o needle
  · intro i
    exact (needle i).triangleRayControlled_of_outside hrho (hh i) (hhrho i)
      (hdir i) (hout i)
  · exact hweight
  · exact harcs

/-! ## Epsilon-greedy order and covering interface -/

/-- The paper shadow with oriented centre `t` and angular radius `H`.  Keeping
its real lift in the data makes the countable length estimate cut-free. -/
def paperDeletedShadow (t H : ℝ) : Set Direction :=
  directionQuotient '' Set.Ioo (t - H) (t + H)

/-- Every point of a paper shadow is within its declared projective radius. -/
theorem paperDeletedShadow_subset_ball {t H : ℝ} :
    paperDeletedShadow t H ⊆ Metric.ball (directionQuotient t) H := by
  rintro theta ⟨u, hu, rfl⟩
  rw [Metric.mem_ball]
  calc
    dist (directionQuotient u) (directionQuotient t) ≤ dist u t := by
      simpa using directionQuotient_lipschitzWith.dist_le_mul u t
    _ = |u - t| := Real.dist_eq u t
    _ < H := (abs_lt).2 ⟨by linarith [hu.1], by linarith [hu.2]⟩

/-- Its one-dimensional angular outer length is at most `2H`. -/
theorem directionAngleOuter_paperDeletedShadow_le {t H : ℝ} (hH : 0 ≤ H) :
    directionAngleOuter (paperDeletedShadow t H) ≤ ENNReal.ofReal (2 * H) := by
  calc
    directionAngleOuter (paperDeletedShadow t H) ≤
        volume.toOuterMeasure (Set.Ioo (t - H) (t + H)) :=
      directionAngleOuter_image_directionQuotient_le _
    _ = volume (Set.Ioo (t - H) (t + H)) := by
      rw [Measure.toOuterMeasure_apply]
    _ = ENNReal.ofReal (2 * H) := by
      rw [Real.volume_Ioo]
      congr 1
      ring

/-- The variable-radius projective shadow deleted by the weighted greedy
algorithm.  A direction is in the shadow precisely when its weighted ball
meets the selected weighted ball. -/
def projectiveShadow (weight : Direction → ℝ) (theta : Direction) : Set Direction :=
  {phi | ¬ Disjoint (Metric.ball theta (weight theta))
    (Metric.ball phi (weight phi))}

/-- The elementary obstruction in the previously proposed Case-II covering
argument.  Even for equal weights, intersection of the two weighted balls does
not put the second centre in the ball of radius one weight about the selected
centre.  Thus `projectiveShadow weight theta` cannot in general be covered by
the paper shadow of radius `weight theta`; approximate-maximality of the
heights does not repair the missing summand. -/
theorem intersecting_equal_balls_not_covered_by_one_radius :
    ∃ (theta phi H : ℝ), 0 < H ∧
      ¬ Disjoint (Metric.ball theta H) (Metric.ball phi H) ∧
      phi ∉ Metric.ball theta H := by
  refine ⟨0, 3 / 2, 1, by norm_num, ?_, ?_⟩
  · rw [Set.not_disjoint_iff]
    refine ⟨3 / 4, ?_, ?_⟩ <;> simp [Real.dist_eq] <;> norm_num
  · rw [Metric.mem_ball, Real.dist_eq]
    norm_num

/-- Honest fixed-radius deletion.  The factor two is forced by the preceding
counterexample: it is the triangle inequality loss needed when all later
weighted radii are at most the selected radius. -/
def doubledDeletedBall (theta : Direction) (H : ℝ) : Set Direction :=
  Metric.ball theta (2 * H)

/-- Intersecting balls with dominated current radius are contained in the
honest doubled deletion ball. -/
theorem mem_doubledDeletedBall_of_not_disjoint
    {theta phi : Direction} {H Hphi : ℝ} (hphi : Hphi ≤ H)
    (hinter : ¬ Disjoint (Metric.ball theta H) (Metric.ball phi Hphi)) :
    phi ∈ doubledDeletedBall theta H := by
  rw [Set.not_disjoint_iff] at hinter
  obtain ⟨x, hx, hy⟩ := hinter
  rw [doubledDeletedBall, Metric.mem_ball] at ⊢
  rw [Metric.mem_ball] at hx hy
  calc
    dist phi theta ≤ dist phi x + dist x theta := dist_triangle _ _ _
    _ < Hphi + H := add_lt_add (by simpa [dist_comm] using hy) hx
    _ ≤ 2 * H := by linarith

/-- A direction surviving honest doubled-ball deletion has its weighted ball
disjoint from the selected weighted ball, provided its radius is dominated by
the selected radius. -/
theorem disjoint_of_not_mem_doubledDeletedBall
    {theta phi : Direction} {H Hphi : ℝ} (hphi : Hphi ≤ H)
    (hout : phi ∉ doubledDeletedBall theta H) :
    Disjoint (Metric.ball theta H) (Metric.ball phi Hphi) := by
  by_contra hinter
  exact hout (mem_doubledDeletedBall_of_not_disjoint hphi hinter)

/-- **Negative-control only.** Data for the superseded variable-radius
intersection-shadow proposal.  It is retained solely so the equal-ball
counterexample and the precise failed interface remain regression-tested; the
Case-II final API is `FixedDeletionGreedyData` in `CaseIISelection`. -/
structure IntersectionShadowGreedyNegativeControl (height weight : Direction → ℝ) where
  initial : Set Direction
  remaining : ℕ → Set Direction
  selected : ℕ → Direction
  deleted : ℕ → Set Direction
  multiplier : ℝ
  multiplier_pos : 0 < multiplier
  start : remaining 0 = initial
  selected_mem : ∀ n, selected n ∈ remaining n
  step : ∀ n, remaining (n + 1) = remaining n \ deleted n
  deleted_eq_shadow : ∀ n, deleted n = projectiveShadow weight (selected n)
  dominates : ∀ n x, x ∈ remaining n →
    multiplier * height x ≤ height (selected n)

namespace IntersectionShadowGreedyNegativeControl

variable {height weight : Direction → ℝ} (G : IntersectionShadowGreedyNegativeControl height weight)

/-- Remaining sets decrease with the stage number. -/
theorem antitone_remaining : Antitone G.remaining := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact Subset.rfl
  | succ n hmn ih =>
      rw [G.step n]
      exact (diff_subset.trans ih)

/-- A residual point was present at every finite stage. -/
theorem residual_mem_remaining {x : Direction}
    (hx : x ∈ greedyResidual G.remaining) (n : ℕ) :
    x ∈ G.remaining n :=
  mem_iInter.mp hx n

/-- Set form of `residual_mem_remaining`, made explicit for the geometric
assembly. -/
theorem residual_subset_remaining (n : ℕ) :
    greedyResidual G.remaining ⊆ G.remaining n :=
  fun _ hx => G.residual_mem_remaining hx n

/-- Every stage remains inside the genuine initial direction set. -/
theorem remaining_subset_initial (n : ℕ) : G.remaining n ⊆ G.initial := by
  rw [← G.start]
  exact G.antitone_remaining (Nat.zero_le n)

/-- A residual direction is outside every deleted projective shadow. -/
theorem residual_not_mem_deleted {theta : Direction}
    (htheta : theta ∈ greedyResidual G.remaining) (n : ℕ) :
    theta ∉ G.deleted n := by
  have hnext := G.residual_mem_remaining htheta (n + 1)
  rw [G.step n] at hnext
  exact hnext.2

/-- The selected weighted projective balls are pairwise disjoint, as a theorem
of the actual deletion order rather than an extra assumption. -/
theorem pairwise_disjoint_selected_balls :
    Pairwise (fun i j => Disjoint
      (Metric.ball (G.selected i) (weight (G.selected i)))
      (Metric.ball (G.selected j) (weight (G.selected j)))) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hjremain : G.selected j ∈ G.remaining (i + 1) :=
      G.antitone_remaining (Nat.succ_le_iff.mpr hijlt) (G.selected_mem j)
    rw [G.step i] at hjremain
    have hnot : G.selected j ∉ projectiveShadow weight (G.selected i) := by
      simpa [G.deleted_eq_shadow i] using hjremain.2
    simpa [projectiveShadow] using hnot
  · have hiremain : G.selected i ∈ G.remaining (j + 1) :=
      G.antitone_remaining (Nat.succ_le_iff.mpr hjilt) (G.selected_mem i)
    rw [G.step j] at hiremain
    have hnot : G.selected i ∉ projectiveShadow weight (G.selected j) := by
      simpa [G.deleted_eq_shadow j] using hiremain.2
    exact (by simpa [projectiveShadow] using hnot :
      Disjoint (Metric.ball (G.selected j) (weight (G.selected j)))
        (Metric.ball (G.selected i) (weight (G.selected i)))).symm

/-- Exact covering identity: what survives all stages is the initial set minus
the union of all deleted sets. -/
theorem greedyResidual_eq :
    greedyResidual G.remaining = G.initial \ ⋃ n, G.deleted n := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · simpa [G.start] using mem_iInter.mp hx 0
    · simp only [mem_iUnion, not_exists]
      intro n hdel
      have hnext := mem_iInter.mp hx (n + 1)
      rw [G.step n] at hnext
      exact hnext.2 hdel
  · rintro ⟨hinit, hnotdel⟩
    simp only [mem_iUnion, not_exists] at hnotdel
    rw [greedyResidual, mem_iInter]
    intro n
    induction n with
    | zero => simpa [G.start] using hinit
    | succ n ih =>
        rw [G.step n]
        exact ⟨ih, hnotdel n⟩


/-- The epsilon-greedy domination property is precisely the bound expected by
`GreedyResidual.residual_height_eq_zero_of_tendsto`. -/
theorem residual_height_eq_zero_of_selected_tendsto
    (height_nonneg : ∀ x, 0 ≤ height x)
    (selected_tendsto : Tendsto (fun n => height (G.selected n)) atTop (nhds 0))
    {x : Direction} (hx : x ∈ greedyResidual G.remaining) :
    height x = 0 := by
  exact residual_height_eq_zero_of_tendsto height G.remaining height_nonneg
    G.multiplier_pos
    (fun n x hxres => G.dominates n x (G.residual_mem_remaining hxres n))
    selected_tendsto hx


/-- Set-level version used to turn the residual family into a zero-height fan. -/
theorem residual_subset_zeroHeight
    (height_nonneg : ∀ x, 0 ≤ height x)
    (selected_tendsto : Tendsto (fun n => height (G.selected n)) atTop (nhds 0)) :
    greedyResidual G.remaining ⊆ {x | height x = 0} := by
  intro x hx
  exact G.residual_height_eq_zero_of_selected_tendsto height_nonneg selected_tendsto hx

end IntersectionShadowGreedyNegativeControl

/-- A positive-height outside triangle cannot contain its vertex in its open
interior. -/
theorem UnitNeedle.center_not_mem_triangleInterior_of_outside
    {rho : ℝ} {o : Plane} {n : UnitNeedle}
    (hrho : 0 < rho) (hh : 0 < n.height o) (hout : n.OutsideBall rho o) :
    o ∉ n.triangleInterior o := by
  intro ho
  obtain ⟨x, hx, l, hl, _hl1, hox⟩ :=
    n.exists_base_openSegment_on_ray_of_mem_triangleInterior ho hh
  have hzero : l • (x - o) = 0 := by simpa using hox.symm
  have hxo : x = o := by
    rcases smul_eq_zero.mp hzero with hlzero | hxzero
    · exact False.elim (hl.ne' hlzero)
    · exact sub_eq_zero.mp hxzero
  have hbad := hout x (openSegment_subset_segment ℝ n.left n.right hx)
  rw [hxo, dist_self] at hbad
  linarith

/-- Every nonvertex point on the radial segment to a zero-height residual
needle has the needle's declared projective direction. -/
theorem UnitNeedle.rayDirection_eq_of_mem_segment_left
    {theta : Direction} {rho : ℝ} {o p : Plane} {n : UnitNeedle}
    (hrho : 0 < rho) (hzero : n.height o = 0)
    (hdir : n.HasDirection theta) (hout : n.OutsideBall rho o)
    (hp : p ∈ segment ℝ o n.left) (hpo : p ≠ o) :
    rayDirection o p = theta := by
  rw [segment_eq_image] at hp
  obtain ⟨s, hs, rfl⟩ := hp
  have hspos : 0 < s := by
    rcases hs.1.eq_or_lt with h | h
    · subst s
      simp at hpo
    · exact h
  rw [rayDirection]
  change ((vectorAngle ((1 - s) • o + s • n.left - o) : ℝ) : Direction) = theta
  rw [show (1 - s) • o + s • n.left - o = s • (n.left - o) by module]
  rw [vectorAngle_pos_smul hspos]
  exact n.rayDirection_left_eq_of_height_zero hrho hzero hdir hout

/-- Residual radial rays are disjoint from every selected open triangle.  The
proof uses residual nonmembership in the *actual deleted shadow* and the
Euclidean `triangleRayControlled_of_outside` theorem. -/
theorem IntersectionShadowGreedyNegativeControl.disjoint_residualFan_selectedTriangleUnion
    {E : Set Plane} (K : StarShapedKakeya E) {rho : ℝ}
    (weight : Direction → ℝ)
    (G : IntersectionShadowGreedyNegativeControl
      (fun theta => (K.needleFamily theta).height K.center) weight)
    (hrho : 0 < rho)
    (hzero : ∀ theta ∈ greedyResidual G.remaining,
      (K.needleFamily theta).height K.center = 0)
    (hout : ∀ theta ∈ G.initial,
      (K.needleFamily theta).OutsideBall rho K.center)
    (hselected_pos : ∀ n, 0 < (K.needleFamily (G.selected n)).height K.center)
    (hselected_lt : ∀ n, (K.needleFamily (G.selected n)).height K.center < rho)
    (hweight_pos : ∀ theta ∈ G.initial, 0 < weight theta)
    (hweight : ∀ n, Real.arcsin
      ((K.needleFamily (G.selected n)).height K.center / rho) ≤
        weight (G.selected n)) :
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
    G.remaining_subset_initial 0 (G.residual_mem_remaining htheta 0)
  have hpne : p ≠ K.center := by
    intro h
    subst p
    exact (K.needleFamily (G.selected n)).center_not_mem_triangleInterior_of_outside
      hrho (hselected_pos n) (hout _ hselinit) hpTri
  have hpray : rayDirection K.center p = theta :=
    (K.needleFamily theta).rayDirection_eq_of_mem_segment_left hrho
      (hzero theta htheta) (K.needleFamily_hasDirection theta)
      (hout theta hthetainit) hpseg hpne
  have hpSelected : rayDirection K.center p ∈
      Metric.ball (G.selected n) (weight (G.selected n)) := by
    rw [Metric.mem_ball]
    exact ((K.needleFamily (G.selected n)).triangleRayControlled_of_outside hrho
      (hselected_pos n) (hselected_lt n)
      (K.needleFamily_hasDirection (G.selected n)) (hout _ hselinit) p hpTri).trans_le
        (hweight n)
  have hpResidual : rayDirection K.center p ∈ Metric.ball theta (weight theta) := by
    rw [hpray, Metric.mem_ball, dist_self]
    exact hweight_pos theta hthetainit
  have hnotdeleted := G.residual_not_mem_deleted htheta n
  rw [G.deleted_eq_shadow n] at hnotdeleted
  have hballs : Disjoint
      (Metric.ball (G.selected n) (weight (G.selected n)))
      (Metric.ball theta (weight theta)) := by
    simpa [projectiveShadow] using hnotdeleted
  exact (Set.disjoint_left.mp hballs) hpSelected hpResidual

/-! ## Countable open union and Carathéodory separation -/

/-- The selected countable union of open complete triangles is measurable. -/
theorem measurableSet_selectedTriangleUnion
    (o : Plane) (needle : ℕ → UnitNeedle) :
    MeasurableSet (⋃ n, (needle n).triangleInterior o) :=
  MeasurableSet.iUnion (fun n => (needle n).triangleInterior_measurable o)

/-- Pairwise disjoint selected open triangles have additive area. -/
theorem volume_selectedTriangleUnion
    (o : Plane) (needle : ℕ → UnitNeedle)
    (hdisjoint : Pairwise (fun i j => Disjoint
      ((needle i).triangleInterior o) ((needle j).triangleInterior o))) :
    volume (⋃ n, (needle n).triangleInterior o) =
      ∑' n, volume ((needle n).triangleInterior o) :=
  measure_iUnion hdisjoint (fun n => (needle n).triangleInterior_measurable o)

/-- Carathéodory separation in the exact form needed by Case II: an arbitrary
(possibly nonmeasurable) residual fan and a measurable selected open union add
inside any common ambient set. -/
theorem outerMeasure_add_le_of_disjoint_measurable
    {F G U : Set Plane} (hG : MeasurableSet G) (hdisjoint : Disjoint F G)
    (hF : F ⊆ U) (hGU : G ⊆ U) :
    volume F + volume G ≤ volume U := by
  rw [← measure_union hdisjoint hG]
  exact measure_mono (union_subset hF hGU)

/-- Negative-control assembly for the superseded intersection-shadow data. The
radial-fan estimate, triangle containment, selected pairwise disjointness, and
fan/triangle separation are all discharged internally; no separation support
parameter remains. -/
theorem StarShapedKakeya.intersectionShadow_geometric_negativeControl
    {E : Set Plane} (K : StarShapedKakeya E) {rho : ℝ}
    (weight : Direction → ℝ)
    (G : IntersectionShadowGreedyNegativeControl
      (fun theta => (K.needleFamily theta).height K.center) weight)
    (hrho : 0 < rho)
    (hout : ∀ theta ∈ G.initial,
      (K.needleFamily theta).OutsideBall rho K.center)
    (hselected_pos : ∀ n, 0 < (K.needleFamily (G.selected n)).height K.center)
    (hselected_lt : ∀ n, (K.needleFamily (G.selected n)).height K.center < rho)
    (hweight_pos : ∀ theta ∈ G.initial, 0 < weight theta)
    (hweight : ∀ n, Real.arcsin
      ((K.needleFamily (G.selected n)).height K.center / rho) ≤
        weight (G.selected n))
    (hselected_tendsto : Tendsto
      (fun n => (K.needleFamily (G.selected n)).height K.center) atTop (nhds 0)) :
    ENNReal.ofReal (rho ^ 2 / 2) * directionAngleOuter (greedyResidual G.remaining) +
        ∑' n, volume ((K.needleFamily (G.selected n)).triangleInterior K.center) ≤
      volume.toOuterMeasure E := by
  let R := greedyResidual G.remaining
  let needle : ℕ → UnitNeedle := fun n => K.needleFamily (G.selected n)
  have hzero : ∀ theta ∈ R, (K.needleFamily theta).height K.center = 0 := by
    intro theta htheta
    exact G.residual_height_eq_zero_of_selected_tendsto
      (fun theta => UnitNeedle.height_nonneg K.center (K.needleFamily theta))
      hselected_tendsto htheta
  have hresinitial : R ⊆ G.initial := by
    intro theta htheta
    exact G.remaining_subset_initial 0 (G.residual_mem_remaining htheta 0)
  have hfan : ENNReal.ofReal (rho ^ 2 / 2) * directionAngleOuter R ≤
      volume.toOuterMeasure (residualFan K R) :=
    K.residualFan_outerMeasure_lower hrho R hzero
      (fun theta htheta => hout theta (hresinitial htheta))
  have hneedle : ∀ n, (needle n).triangleInterior K.center ⊆ E := by
    intro n
    exact (UnitNeedle.triangleInterior_subset_triangleHull K.center _).trans
      (K.triangleHull_subset (G.selected n))
  have hselected_out : ∀ n, (needle n).OutsideBall rho K.center := by
    intro n
    exact hout _ (G.remaining_subset_initial n (G.selected_mem n))
  have hpair : Pairwise (fun i j => Disjoint
      ((needle i).triangleInterior K.center)
      ((needle j).triangleInterior K.center)) := by
    apply pairwise_disjoint_triangleInterior_of_outside
      (fun n => G.selected n) (fun n => weight (G.selected n)) rho K.center needle
      hrho hselected_pos hselected_lt
      (fun n => K.needleFamily_hasDirection (G.selected n)) hselected_out hweight
    exact G.pairwise_disjoint_selected_balls
  have hdisjoint : Disjoint (residualFan K R)
      (⋃ n, (needle n).triangleInterior K.center) := by
    exact G.disjoint_residualFan_selectedTriangleUnion K weight hrho hzero hout
      hselected_pos hselected_lt hweight_pos hweight
  let U : Set Plane := ⋃ n, (needle n).triangleInterior K.center
  have hU : MeasurableSet U := measurableSet_selectedTriangleUnion K.center needle
  have hUE : U ⊆ E := iUnion_subset hneedle
  have hadd : volume.toOuterMeasure (residualFan K R) + volume U ≤
      volume.toOuterMeasure E :=
    outerMeasure_add_le_of_disjoint_measurable hU hdisjoint
      (K.residualFan_subset R) hUE
  calc
    ENNReal.ofReal (rho ^ 2 / 2) * directionAngleOuter R +
          ∑' n, volume ((needle n).triangleInterior K.center) =
        ENNReal.ofReal (rho ^ 2 / 2) * directionAngleOuter R + volume U := by
      rw [volume_selectedTriangleUnion K.center needle hpair]
    _ ≤ volume.toOuterMeasure (residualFan K R) + volume U := by
      simpa [add_comm] using add_le_add_right hfan (volume U)
    _ ≤ volume.toOuterMeasure E := hadd

/-- Negative-control bridge for the superseded intersection-shadow assembly.
`caseII_minimax`.  This is deliberately stated for arbitrary ENNReal selected
area `b`; the preceding theorem supplies it as the selected triangle-area sum.
The geometric assembly is stronger than the minimax fan premise because it
contains `+ b` rather than the negative-coefficient correction. -/
theorem intersectionShadow_minimax_negativeControl
    {c kappa rho : ℝ} {L b M : ENNReal}
    (hc0 : 0 < c) (hcrho : c < rho / 2)
    (hk0 : 0 < kappa) (hk1 : kappa ≤ 1)
    (hrho : 1 / 2 < rho) (hM : M ≠ ⊤)
    (hgeom : ENNReal.ofReal (rho ^ 2 / 2) * L + b ≤ M) :
    c * kappa / 4 * L.toReal ≤ M.toReal := by
  have hsumne : ENNReal.ofReal (rho ^ 2 / 2) * L + b ≠ ⊤ :=
    ne_top_of_le_ne_top hM hgeom
  have hAne : ENNReal.ofReal (rho ^ 2 / 2) * L ≠ ⊤ :=
    (ENNReal.add_ne_top.mp hsumne).1
  have hbne : b ≠ ⊤ := (ENNReal.add_ne_top.mp hsumne).2
  have hreal := (ENNReal.toReal_le_toReal hsumne hM).2 hgeom
  rw [ENNReal.toReal_add hAne hbne, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ rho ^ 2 / 2)] at hreal
  have hbM : b.toReal ≤ M.toReal := by
    have hcoef : 0 ≤ rho ^ 2 / 2 * L.toReal :=
      mul_nonneg (by positivity) ENNReal.toReal_nonneg
    linarith
  have hlambda := caseIILambda_neg hc0 hcrho hk0 hk1 hrho
  apply caseII_minimax hc0 hcrho hk0 hk1 hrho hbM
  have hb0 : 0 ≤ b.toReal := ENNReal.toReal_nonneg
  nlinarith

/-- Honest infinite-branch conclusion of the current local geometric chain.
It controls only the angle of the residual set; it is intentionally not stated
as the paper's initial-angle minimax theorem. -/
theorem StarShapedKakeya.intersectionShadow_infinite_negativeControl
    {E : Set Plane} (K : StarShapedKakeya E) {c kappa rho : ℝ}
    (weight : Direction → ℝ)
    (G : IntersectionShadowGreedyNegativeControl
      (fun theta => (K.needleFamily theta).height K.center) weight)
    (hc0 : 0 < c) (hcrho : c < rho / 2)
    (hk0 : 0 < kappa) (hk1 : kappa ≤ 1) (hrhoHalf : 1 / 2 < rho)
    (hout : ∀ theta ∈ G.initial,
      (K.needleFamily theta).OutsideBall rho K.center)
    (hselected_pos : ∀ n, 0 < (K.needleFamily (G.selected n)).height K.center)
    (hselected_lt : ∀ n, (K.needleFamily (G.selected n)).height K.center < rho)
    (hweight_pos : ∀ theta ∈ G.initial, 0 < weight theta)
    (hweight : ∀ n, Real.arcsin
      ((K.needleFamily (G.selected n)).height K.center / rho) ≤
        weight (G.selected n))
    (hselected_tendsto : Tendsto
      (fun n => (K.needleFamily (G.selected n)).height K.center) atTop (nhds 0))
    (hE : volume.toOuterMeasure E ≠ ⊤) :
    c * kappa / 4 * (directionAngleOuter (greedyResidual G.remaining)).toReal ≤
      (volume.toOuterMeasure E).toReal := by
  apply intersectionShadow_minimax_negativeControl hc0 hcrho hk0 hk1 hrhoHalf hE
  exact K.intersectionShadow_geometric_negativeControl weight G (by linarith) hout
    hselected_pos hselected_lt hweight_pos hweight hselected_tendsto

end

end StarKakeyaLower
