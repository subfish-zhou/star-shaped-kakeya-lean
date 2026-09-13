import Mathlib

/-!
# Universal objects for the star-shaped Kakeya lower bound

No measurability is imposed on the Kakeya set or on the family of needles.
The family below is obtained with `Classical.choose`, pointwise in direction;
it is not a measurable-selection assertion.

The geometric-measure statement `TriangleAreaBridge` says that the outer
measure of the filled triangle with unit base is at least half its determinant
height.  It is proved in `TriangleArea.lean`; keeping the statement here avoids
a dependency cycle with the basic Kakeya objects.
-/

open Set MeasureTheory

namespace StarKakeyaLower

noncomputable section

/-- The Euclidean plane, in coordinates convenient for determinants. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Unoriented directions: angles modulo `π`. -/
abbrev Direction := AddCircle Real.pi

instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

/-- The unit vector represented by a real angle. -/
def angleVector (t : ℝ) : Plane :=
  WithLp.toLp 2 ![Real.cos t, Real.sin t]

@[simp] theorem angleVector_zero (t : ℝ) : angleVector t 0 = Real.cos t := by
  simp [angleVector]

@[simp] theorem angleVector_one (t : ℝ) : angleVector t 1 = Real.sin t := by
  simp [angleVector]

/-- The vectors used to orient needles really are unit vectors. -/
@[simp] theorem norm_angleVector (t : ℝ) : ‖angleVector t‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [angleVector, Fin.sum_univ_two, Real.cos_sq_add_sin_sq]

/-- The oriented area form in the coordinate model of the plane. -/
def det (x y : Plane) : ℝ := x 0 * y 1 - x 1 * y 0

theorem det_add_right (x y z : Plane) : det x (y + z) = det x y + det x z := by
  simp only [det, PiLp.add_apply]
  ring

theorem det_smul_right (x y : Plane) (c : ℝ) : det x (c • y) = c * det x y := by
  simp only [det, PiLp.smul_apply, smul_eq_mul]
  ring

theorem det_add_left (x y z : Plane) : det (x + y) z = det x z + det y z := by
  simp only [det, PiLp.add_apply]
  ring

theorem det_smul_left (x y : Plane) (c : ℝ) : det (c • x) y = c * det x y := by
  simp only [det, PiLp.smul_apply, smul_eq_mul]
  ring

@[simp] theorem det_self (x : Plane) : det x x = 0 := by
  simp only [det]
  ring

theorem det_swap (x y : Plane) : det x y = -det y x := by
  simp only [det]
  ring

/-- Signed normal coordinate with respect to the line of angle `t`. -/
def normalCoord (t : ℝ) (x : Plane) : ℝ := det (angleVector t) x

theorem normalCoord_angleVector (t u : ℝ) :
    normalCoord t (angleVector u) = Real.sin (u - t) := by
  simp only [normalCoord, det, angleVector_zero, angleVector_one, Real.sin_sub]
  ring

theorem normalCoord_smul (t c : ℝ) (x : Plane) :
    normalCoord t (c • x) = c * normalCoord t x := by
  simp only [normalCoord, det, PiLp.smul_apply, smul_eq_mul]
  ring

theorem normalCoord_add (t : ℝ) (x y : Plane) :
    normalCoord t (x + y) = normalCoord t x + normalCoord t y := by
  simp only [normalCoord, det, PiLp.add_apply]
  ring

theorem normalCoord_sub (t : ℝ) (x y : Plane) :
    normalCoord t (x - y) = normalCoord t x - normalCoord t y := by
  simp only [normalCoord, det, PiLp.sub_apply]
  ring

/-- Coordinate identification with the complex plane, used only to make a
canonical oriented lift of a nonzero radial vector. -/
def planeComplex (x : Plane) : ℂ := ⟨x 0, x 1⟩

/-- A real argument of a planar vector.  At zero its value is irrelevant. -/
def vectorAngle (x : Plane) : ℝ := Complex.arg (planeComplex x)

/-- The corresponding unoriented radial direction. -/
def rayDirection (o p : Plane) : Direction := (vectorAngle (p - o) : Direction)

theorem norm_planeComplex (x : Plane) : ‖planeComplex x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [planeComplex, Complex.norm_def, Complex.normSq_apply,
    Fin.sum_univ_two]
  congr 1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  ring

theorem planeComplex_ne_zero {x : Plane} (hx : x ≠ 0) : planeComplex x ≠ 0 := by
  intro h
  apply hx
  ext i
  fin_cases i
  · exact congrArg Complex.re h
  · exact congrArg Complex.im h

theorem planeComplex_smul (c : ℝ) (x : Plane) :
    planeComplex (c • x) = c * planeComplex x := by
  apply Complex.ext <;> simp [planeComplex]

/-- Positive radial rescaling does not alter the canonical polar angle. -/
theorem vectorAngle_pos_smul {c : ℝ} (hc : 0 < c) (x : Plane) :
    vectorAngle (c • x) = vectorAngle x := by
  rw [vectorAngle, vectorAngle, planeComplex_smul, Complex.arg_real_mul _ hc]

/-- Polar reconstruction of a nonzero planar vector. -/
theorem norm_smul_angleVector_vectorAngle {x : Plane} (hx : x ≠ 0) :
    ‖x‖ • angleVector (vectorAngle x) = x := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i
  · simp only [PiLp.smul_apply, smul_eq_mul, angleVector, vectorAngle]
    rw [Complex.cos_arg (planeComplex_ne_zero hx), norm_planeComplex]
    simp [planeComplex]
    exact mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hx)
  · simp only [PiLp.smul_apply, smul_eq_mul, angleVector, vectorAngle]
    rw [Complex.sin_arg, norm_planeComplex]
    simp [planeComplex]
    exact mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hx)

/-- A closed segment of length one. -/
structure UnitNeedle where
  left : Plane
  right : Plane
  unit_length : dist left right = 1

namespace UnitNeedle

/-- The points occupied by a needle. -/
def carrier (n : UnitNeedle) : Set Plane := segment ℝ n.left n.right

/-- `n` is parallel to the unoriented direction `θ`.

The existential real lift makes this definition independent of any choice of
an orientation for `AddCircle π`; the nonzero scalar permits either sign. -/
def HasDirection (n : UnitNeedle) (θ : Direction) : Prop :=
  ∃ t : ℝ, (t : Direction) = θ ∧
    ∃ c : ℝ, c ≠ 0 ∧ n.right - n.left = c • angleVector t

/-- The filled triangle swept from `o` to the unit needle.  This union-of-rays
form is definitionally suited to star-shaped sets and equals the usual convex
hull of the three vertices. -/
def triangleHull (o : Plane) (n : UnitNeedle) : Set Plane :=
  ⋃ x ∈ n.carrier, segment ℝ o x

/-- Determinant height above the line of the needle.  Since the base has length
one, this is the ordinary perpendicular height. -/
def height (o : Plane) (n : UnitNeedle) : ℝ :=
  |(n.right - n.left) 0 * (o - n.left) 1 -
    (n.right - n.left) 1 * (o - n.left) 0|

theorem height_nonneg (o : Plane) (n : UnitNeedle) : 0 ≤ n.height o := abs_nonneg _

/-- A direction witness can always be chosen with scalar exactly of absolute
value one.  Thus `HasDirection` contains an orientation choice, but no hidden
scale. -/
theorem hasDirection_oriented_lift {n : UnitNeedle} {θ : Direction}
    (h : n.HasDirection θ) :
    ∃ t : ℝ, (t : Direction) = θ ∧ ∃ c : ℝ, |c| = 1 ∧
      n.right - n.left = c • angleVector t := by
  obtain ⟨t, ht, c, _hc, heq⟩ := h
  refine ⟨t, ht, c, ?_, heq⟩
  have hn : ‖n.right - n.left‖ = 1 := by
    rw [← dist_eq_norm, dist_comm]
    exact n.unit_length
  rw [heq, norm_smul, norm_angleVector, mul_one, Real.norm_eq_abs] at hn
  exact hn

/-- In an oriented lift, determinant height is the absolute normal coordinate
of the centre relative to either endpoint. -/
theorem height_eq_abs_normalCoord {o : Plane} {n : UnitNeedle} {t c : ℝ}
    (hc : |c| = 1) (hd : n.right - n.left = c • angleVector t) :
    n.height o = |normalCoord t (o - n.left)| := by
  rw [height]
  have hdet :
      (n.right - n.left) 0 * (o - n.left) 1 -
          (n.right - n.left) 1 * (o - n.left) 0 =
        c * normalCoord t (o - n.left) := by
    rw [hd]
    simp only [PiLp.smul_apply, smul_eq_mul, normalCoord, det]
    ring
  rw [hdet, abs_mul, hc, one_mul]

end UnitNeedle

/-- A set star-shaped about one point and containing a unit needle in every
unoriented direction.  In particular, `E` is *not* required to be measurable. -/
structure StarShapedKakeya (E : Set Plane) where
  center : Plane
  star : ∀ ⦃x⦄, x ∈ E → segment ℝ center x ⊆ E
  needle_exists : ∀ θ : Direction, ∃ n : UnitNeedle,
    n.HasDirection θ ∧ n.carrier ⊆ E

namespace StarShapedKakeya

variable {E : Set Plane} (K : StarShapedKakeya E)

/-- A completely arbitrary pointwise choice of needles.  This uses choice only;
there is no assertion that the resulting map is measurable. -/
def needleFamily (θ : Direction) : UnitNeedle :=
  Classical.choose (K.needle_exists θ)

theorem needleFamily_hasDirection (θ : Direction) :
    (K.needleFamily θ).HasDirection θ :=
  (Classical.choose_spec (K.needle_exists θ)).1

theorem needleFamily_carrier_subset (θ : Direction) :
    (K.needleFamily θ).carrier ⊆ E :=
  (Classical.choose_spec (K.needle_exists θ)).2

/-- Every chosen triangle lies in `E`, solely by star-shapedness. -/
theorem triangleHull_subset (θ : Direction) :
    (K.needleFamily θ).triangleHull K.center ⊆ E := by
  intro y hy
  simp only [UnitNeedle.triangleHull, mem_iUnion] at hy
  obtain ⟨x, hx, hy⟩ := hy
  exact K.star (K.needleFamily_carrier_subset θ hx) hy

/-- The standard Euclidean triangle-area statement in Mathlib's
`volume.toOuterMeasure` normalization.  See `triangleAreaBridge` for its proof. -/
def TriangleAreaBridge : Prop :=
  ∀ (o : Plane) (n : UnitNeedle),
    ENNReal.ofReal (n.height o / 2) ≤
      volume.toOuterMeasure (n.triangleHull o)

/-- Once the standard triangle-area bridge is supplied, one high chosen needle
forces the corresponding outer-measure lower bound for the possibly
nonmeasurable set `E`. -/
theorem outerMeasure_ge_half_height
    (harea : TriangleAreaBridge) (θ : Direction) :
    ENNReal.ofReal ((K.needleFamily θ).height K.center / 2) ≤
      volume.toOuterMeasure E := by
  exact (harea K.center (K.needleFamily θ)).trans
    (measure_mono (K.triangleHull_subset θ))

/-- Convenient real-threshold form of the preceding statement. -/
theorem outerMeasure_ge_half_of_height
    (harea : TriangleAreaBridge) {θ : Direction} {a : ℝ}
    (hh : a ≤ (K.needleFamily θ).height K.center) :
    ENNReal.ofReal (a / 2) ≤ volume.toOuterMeasure E := by
  refine (ENNReal.ofReal_le_ofReal ?_).trans (K.outerMeasure_ge_half_height harea θ)
  linarith

end StarShapedKakeya

end

end StarKakeyaLower
