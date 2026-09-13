import StarKakeyaLower.QuotientCircle

/-!
# The first Li geometry layer

This file fixes the two angular ambient spaces which are easy to conflate in
Li's Section 3.  Polar angles live in `PolarAngle = AddCircle (2 * π)`, whereas
unoriented needle directions live in `ProjectiveDirection = AddCircle π`.
`polarToProjective` is the genuine quotient induced by the identity on `ℝ`.

We also give a coordinate model of a unit needle on a support line, its triangle
with the origin, and an exact parameterization of its intersection with a radius
circle.  The endpoint part is deliberately set-valued: the length estimates are
used only after proving that the endpoint intervals have the same centre as the
projected polar arc.  Thus no cardinal/length inequality is passed off as a set
containment.
-/

open Set

namespace StarKakeyaLower

noncomputable section

/-! ## Coordinate needles and their polar trace -/

/-- The real Euclidean plane, kept in coordinates for the trigonometric layer. -/
abbrev CoordinatePlane := ℝ × ℝ

/-- Euclidean squared length in the coordinate plane. -/
def planeNormSq (z : CoordinatePlane) : ℝ := z.1 ^ 2 + z.2 ^ 2

/-- The oriented unit vector of angle `θ`. -/
def unitDirection (θ : ℝ) : CoordinatePlane := (Real.cos θ, Real.sin θ)

/-- The left unit normal to `unitDirection θ`. -/
def unitNormal (θ : ℝ) : CoordinatePlane := (-Real.sin θ, Real.cos θ)

/-- Coordinate scalar multiplication, named to avoid depending on a product norm. -/
def scaleCoordinatePlane (c : ℝ) (z : CoordinatePlane) : CoordinatePlane := (c * z.1, c * z.2)

/-- Coordinate addition. -/
def addCoordinatePlane (z w : CoordinatePlane) : CoordinatePlane := (z.1 + w.1, z.2 + w.2)

/-- Coordinate subtraction. -/
def subCoordinatePlane (z w : CoordinatePlane) : CoordinatePlane := (z.1 - w.1, z.2 - w.2)

/-- Euclidean scalar product. -/
def planeDot (z w : CoordinatePlane) : ℝ := z.1 * w.1 + z.2 * w.2

@[simp] theorem planeNormSq_unitDirection (θ : ℝ) :
    planeNormSq (unitDirection θ) = 1 := by
  simp [planeNormSq, unitDirection, Real.cos_sq_add_sin_sq]

@[simp] theorem planeNormSq_unitNormal (θ : ℝ) :
    planeNormSq (unitNormal θ) = 1 := by
  simp [planeNormSq, unitNormal, Real.sin_sq_add_cos_sq]

@[simp] theorem unitDirection_dot_unitNormal (θ : ℝ) :
    planeDot (unitDirection θ) (unitNormal θ) = 0 := by
  simp [planeDot, unitDirection, unitNormal]
  ring

/-- Point with tangential coordinate `x` on the line of signed support height
`δ`, whose direction is `α`. -/
def supportPoint (α δ x : ℝ) : CoordinatePlane :=
  addCoordinatePlane (scaleCoordinatePlane δ (unitNormal α)) (scaleCoordinatePlane x (unitDirection α))

/-- A unit needle, centered at tangential coordinate `c`, on a support line. -/
def supportNeedle (α δ c : ℝ) : Set CoordinatePlane :=
  supportPoint α δ '' Icc (c - 1 / 2) (c + 1 / 2)

/-- Every point in the parameterized needle lies on its support line. -/
theorem supportPoint_dot_normal (α δ x : ℝ) :
    planeDot (supportPoint α δ x) (unitNormal α) = δ := by
  simp [supportPoint, planeDot, scaleCoordinatePlane, addCoordinatePlane, unitDirection, unitNormal]
  linear_combination δ * (Real.sin_sq_add_cos_sq α)

/-- The two endpoint parameters differ by the unit direction vector. -/
theorem supportNeedle_endpoint_sub (α δ c : ℝ) :
    subCoordinatePlane (supportPoint α δ (c + 1 / 2))
      (supportPoint α δ (c - 1 / 2)) = unitDirection α := by
  ext <;> simp [subCoordinatePlane, supportPoint, scaleCoordinatePlane, addCoordinatePlane, unitDirection, unitNormal] <;>
    ring

/-- Consequently the support-line needle has Euclidean squared length one. -/
theorem supportNeedle_unit_length (α δ c : ℝ) :
    planeNormSq
      (subCoordinatePlane (supportPoint α δ (c + 1 / 2))
        (supportPoint α δ (c - 1 / 2))) = 1 := by
  rw [supportNeedle_endpoint_sub]
  exact planeNormSq_unitDirection α

/-- The filled triangle spanned by the origin and a support-line unit needle. -/
def supportNeedleTriangle (α δ c : ℝ) : Set CoordinatePlane :=
  {z | ∃ lam ∈ Icc (0 : ℝ) 1, ∃ x ∈ Icc (c - 1 / 2) (c + 1 / 2),
    z = scaleCoordinatePlane lam (supportPoint α δ x)}

/-- Coordinate rotation.  It is used whenever an angular normalization is made,
so that the triangle is transported together with its polar arcs. -/
def rotateCoordinatePlane (β : ℝ) (z : CoordinatePlane) : CoordinatePlane :=
  (Real.cos β * z.1 - Real.sin β * z.2,
    Real.sin β * z.1 + Real.cos β * z.2)

/-- Rotation commutes with coordinate scaling. -/
theorem rotateCoordinatePlane_scaleCoordinatePlane (β lam : ℝ) (z : CoordinatePlane) :
    rotateCoordinatePlane β (scaleCoordinatePlane lam z) = scaleCoordinatePlane lam (rotateCoordinatePlane β z) := by
  ext <;> simp [rotateCoordinatePlane, scaleCoordinatePlane] <;> ring

/-- Exact covariance of support coordinates.  Notice that both the support line
and its segment parameter are transported; this prevents an invalid WLOG
rotation of angles alone. -/
theorem rotateCoordinatePlane_supportPoint (β α δ x : ℝ) :
    rotateCoordinatePlane β (supportPoint α δ x) = supportPoint (α + β) δ x := by
  ext <;>
    simp [rotateCoordinatePlane, supportPoint, scaleCoordinatePlane, addCoordinatePlane, unitDirection, unitNormal,
      Real.sin_add, Real.cos_add] <;> ring

/-- Rotation transports the entire filled support-needle triangle. -/
theorem supportNeedleTriangle_rotate (β α δ c : ℝ) :
    supportNeedleTriangle (α + β) δ c =
      rotateCoordinatePlane β '' supportNeedleTriangle α δ c := by
  ext z
  constructor
  · rintro ⟨lam, hlam, x, hx, rfl⟩
    refine ⟨scaleCoordinatePlane lam (supportPoint α δ x), ⟨lam, hlam, x, hx, rfl⟩, ?_⟩
    rw [rotateCoordinatePlane_scaleCoordinatePlane, rotateCoordinatePlane_supportPoint]
  · rintro ⟨_, ⟨lam, hlam, x, hx, rfl⟩, rfl⟩
    refine ⟨lam, hlam, x, hx, ?_⟩
    rw [rotateCoordinatePlane_scaleCoordinatePlane, rotateCoordinatePlane_supportPoint]

/-- Polar parameterization of the radius-`r` circle. -/
def polarPoint (r θ : ℝ) : CoordinatePlane := scaleCoordinatePlane r (unitDirection θ)

/-- The radius circle, explicitly parameterized by polar angle. -/
def radiusCircle (r : ℝ) : Set CoordinatePlane := range (polarPoint r)

/-- Real-angle polar trace of a support-needle triangle on a radius circle. -/
def trianglePolarTrace (T : Set CoordinatePlane) (r : ℝ) : Set ℝ :=
  {θ | polarPoint r θ ∈ T}

/-- Every polar point lies on the corresponding parameterized radius circle. -/
theorem polarPoint_mem_radiusCircle (r θ : ℝ) : polarPoint r θ ∈ radiusCircle r :=
  ⟨θ, rfl⟩

/-- Exact barycentric/tangential parameterization of the triangle-circle trace. -/
theorem mem_trianglePolarTrace_iff
    (α δ c r θ : ℝ) :
    θ ∈ trianglePolarTrace (supportNeedleTriangle α δ c) r ↔
      ∃ lam ∈ Icc (0 : ℝ) 1, ∃ x ∈ Icc (c - 1 / 2) (c + 1 / 2),
        polarPoint r θ = scaleCoordinatePlane lam (supportPoint α δ x) := by
  rfl

/-- Normal-coordinate equation for a point of the triangle-circle trace. -/
theorem polar_trace_normal_coordinate
    {α δ c r θ : ℝ}
    (hθ : θ ∈ trianglePolarTrace (supportNeedleTriangle α δ c) r) :
    ∃ lam ∈ Icc (0 : ℝ) 1, ∃ x ∈ Icc (c - 1 / 2) (c + 1 / 2),
      r * Real.sin (θ - α) = lam * δ := by
  rcases (mem_trianglePolarTrace_iff α δ c r θ).mp hθ with ⟨lam, hlam, x, hx, heq⟩
  refine ⟨lam, hlam, x, hx, ?_⟩
  have h1 := congrArg (fun z : CoordinatePlane => planeDot z (unitNormal α)) heq
  dsimp [polarPoint, supportPoint, scaleCoordinatePlane, addCoordinatePlane, planeDot,
    unitDirection, unitNormal] at h1
  rw [Real.sin_sub]
  linear_combination h1 + lam * δ * (Real.sin_sq_add_cos_sq α)

/-- Tangential-coordinate equation for a point of the triangle-circle trace. -/
theorem polar_trace_tangent_coordinate
    {α δ c r θ : ℝ}
    (hθ : θ ∈ trianglePolarTrace (supportNeedleTriangle α δ c) r) :
    ∃ lam ∈ Icc (0 : ℝ) 1, ∃ x ∈ Icc (c - 1 / 2) (c + 1 / 2),
      r * Real.cos (θ - α) = lam * x := by
  rcases (mem_trianglePolarTrace_iff α δ c r θ).mp hθ with ⟨lam, hlam, x, hx, heq⟩
  refine ⟨lam, hlam, x, hx, ?_⟩
  have h1 := congrArg (fun z : CoordinatePlane => planeDot z (unitDirection α)) heq
  dsimp [polarPoint, supportPoint, scaleCoordinatePlane, addCoordinatePlane, planeDot,
    unitDirection, unitNormal] at h1
  rw [Real.cos_sub]
  linear_combination h1 + lam * x * (Real.cos_sq_add_sin_sq α)

/-- Exact support coordinates for the circle trace.  Unlike the two preceding
one-way lemmas, this packages the normal and tangential equations with the
*same* barycentric and segment parameters, and is an iff.  This is the useful
coordinate form of `triangle ∩ S_r`: it remains valid in all degenerate cases
(`r = 0`, `δ = 0`, or `lam = 0`) and therefore does not hide a division. -/
theorem mem_trianglePolarTrace_supportCoordinates_iff
    (α δ c r θ : ℝ) :
    θ ∈ trianglePolarTrace (supportNeedleTriangle α δ c) r ↔
      ∃ lam ∈ Icc (0 : ℝ) 1, ∃ x ∈ Icc (c - 1 / 2) (c + 1 / 2),
        r * Real.sin (θ - α) = lam * δ ∧
        r * Real.cos (θ - α) = lam * x := by
  constructor
  · intro hθ
    rcases (mem_trianglePolarTrace_iff α δ c r θ).mp hθ with
      ⟨lam, hlam, x, hx, heq⟩
    refine ⟨lam, hlam, x, hx, ?_, ?_⟩
    · have h := congrArg (fun z : CoordinatePlane => planeDot z (unitNormal α)) heq
      dsimp [polarPoint, supportPoint, scaleCoordinatePlane, addCoordinatePlane, planeDot,
        unitDirection, unitNormal] at h
      rw [Real.sin_sub]
      linear_combination h + lam * δ * (Real.sin_sq_add_cos_sq α)
    · have h := congrArg (fun z : CoordinatePlane => planeDot z (unitDirection α)) heq
      dsimp [polarPoint, supportPoint, scaleCoordinatePlane, addCoordinatePlane, planeDot,
        unitDirection, unitNormal] at h
      rw [Real.cos_sub]
      linear_combination h + lam * x * (Real.cos_sq_add_sin_sq α)
  · rintro ⟨lam, hlam, x, hx, hnormal, htangent⟩
    rw [mem_trianglePolarTrace_iff]
    refine ⟨lam, hlam, x, hx, ?_⟩
    rw [Real.sin_sub] at hnormal
    rw [Real.cos_sub] at htangent
    ext
    · dsimp [polarPoint, supportPoint, scaleCoordinatePlane, addCoordinatePlane, unitDirection, unitNormal]
      linear_combination
        (Real.cos α) * htangent - (Real.sin α) * hnormal -
          (r * Real.cos θ) * (Real.sin_sq_add_cos_sq α)
    · dsimp [polarPoint, supportPoint, scaleCoordinatePlane, addCoordinatePlane, unitDirection, unitNormal]
      linear_combination
        (Real.sin α) * htangent + (Real.cos α) * hnormal -
          (r * Real.sin θ) * (Real.sin_sq_add_cos_sq α)

/-- Division-free inequality description of the trace for a positive circle
radius.  The barycentric parameter is automatically positive: `lam = 0` would
put a nonzero polar point at the triangle vertex.  Thus the tangential segment
condition is exactly the pair of displayed inequalities. -/
theorem mem_trianglePolarTrace_coordinateInequalities_iff
    (α δ c r θ : ℝ) (hr : 0 < r) :
    θ ∈ trianglePolarTrace (supportNeedleTriangle α δ c) r ↔
      ∃ lam ∈ Ioc (0 : ℝ) 1,
        r * Real.sin (θ - α) = lam * δ ∧
        lam * (c - 1 / 2) ≤ r * Real.cos (θ - α) ∧
        r * Real.cos (θ - α) ≤ lam * (c + 1 / 2) := by
  rw [mem_trianglePolarTrace_supportCoordinates_iff]
  constructor
  · rintro ⟨lam, hlam, x, hx, hnormal, htangent⟩
    have hlam_pos : 0 < lam := by
      rcases lt_or_eq_of_le hlam.1 with hpos | hzero
      · exact hpos
      · subst lam
        simp only [zero_mul] at hnormal htangent
        have hs : Real.sin (θ - α) = 0 := by nlinarith
        have hc : Real.cos (θ - α) = 0 := by nlinarith
        nlinarith [Real.sin_sq_add_cos_sq (θ - α)]
    refine ⟨lam, ⟨hlam_pos, hlam.2⟩, hnormal, ?_, ?_⟩
    · rw [htangent]
      exact mul_le_mul_of_nonneg_left hx.1 (le_of_lt hlam_pos)
    · rw [htangent]
      exact mul_le_mul_of_nonneg_left hx.2 (le_of_lt hlam_pos)
  · rintro ⟨lam, hlam, hnormal, hlower, hupper⟩
    let x := r * Real.cos (θ - α) / lam
    have hxlower : c - 1 / 2 ≤ x := by
      dsimp [x]
      apply (le_div_iff₀ hlam.1).2
      nlinarith
    have hxupper : x ≤ c + 1 / 2 := by
      dsimp [x]
      apply (div_le_iff₀ hlam.1).2
      nlinarith
    refine ⟨lam, ⟨le_of_lt hlam.1, hlam.2⟩, x, ⟨hxlower, hxupper⟩,
      hnormal, ?_⟩
    dsimp [x]
    field_simp [ne_of_gt hlam.1]

/-- After eliminating the barycentric variable, the trace is cut out by the
support-height bound and the two *actual* base-endpoint inequalities.  The first
two inequalities are equivalent to `0 < sin(θ-α) ≤ δ/r`; no endpoint envelope
occurs in this statement. -/
theorem mem_trianglePolarTrace_eliminatedCoordinates_iff
    (α δ c r θ : ℝ) (hr : 0 < r) (hδ : 0 < δ) :
    θ ∈ trianglePolarTrace (supportNeedleTriangle α δ c) r ↔
      0 < r * Real.sin (θ - α) ∧
      r * Real.sin (θ - α) ≤ δ ∧
      (r * Real.sin (θ - α)) * (c - 1 / 2) ≤
        δ * (r * Real.cos (θ - α)) ∧
      δ * (r * Real.cos (θ - α)) ≤
        (r * Real.sin (θ - α)) * (c + 1 / 2) := by
  rw [mem_trianglePolarTrace_coordinateInequalities_iff α δ c r θ hr]
  constructor
  · rintro ⟨lam, hlam, hnormal, hlower, hupper⟩
    have hnormal' : lam * δ = r * Real.sin (θ - α) := hnormal.symm
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hnormal']
      exact mul_pos hlam.1 hδ
    · rw [← hnormal']
      simpa using mul_le_mul_of_nonneg_right hlam.2 (le_of_lt hδ)
    · calc
        (r * Real.sin (θ - α)) * (c - 1 / 2) =
            δ * (lam * (c - 1 / 2)) := by rw [← hnormal']; ring
        _ ≤ δ * (r * Real.cos (θ - α)) :=
          mul_le_mul_of_nonneg_left hlower (le_of_lt hδ)
    · calc
        δ * (r * Real.cos (θ - α)) ≤
            δ * (lam * (c + 1 / 2)) :=
          mul_le_mul_of_nonneg_left hupper (le_of_lt hδ)
        _ = (r * Real.sin (θ - α)) * (c + 1 / 2) := by rw [← hnormal']; ring
  · rintro ⟨hpos, hheight, hlower, hupper⟩
    let lam := r * Real.sin (θ - α) / δ
    have hlam_pos : 0 < lam := div_pos hpos hδ
    have hlam_le : lam ≤ 1 := (div_le_one hδ).2 hheight
    have hnormal : r * Real.sin (θ - α) = lam * δ := by
      dsimp [lam]
      field_simp [ne_of_gt hδ]
    refine ⟨lam, ⟨hlam_pos, hlam_le⟩, hnormal, ?_, ?_⟩
    · apply le_of_mul_le_mul_left _ hδ
      calc
        δ * (lam * (c - 1 / 2)) =
            (r * Real.sin (θ - α)) * (c - 1 / 2) := by rw [hnormal]; ring
        _ ≤ δ * (r * Real.cos (θ - α)) := hlower
    · apply le_of_mul_le_mul_left _ hδ
      calc
        δ * (r * Real.cos (θ - α)) ≤
            (r * Real.sin (θ - α)) * (c + 1 / 2) := hupper
        _ = δ * (lam * (c + 1 / 2)) := by rw [hnormal]; ring

/-! ## One-period classification of the real trace inequalities -/

/-- On the increasing half of the positive sine period, the height inequality
has the expected inverse-sine endpoint. -/
theorem sin_le_iff_le_arcsin_of_mem_left_half
    {k φ : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hφ0 : 0 ≤ φ) (hφhalf : φ ≤ Real.pi / 2) :
    Real.sin φ ≤ k ↔ φ ≤ Real.arcsin k := by
  have hk : k ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, hk1.le⟩
  have hpi : 0 < Real.pi := Real.pi_pos
  have hφ : φ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith, hφhalf⟩
  exact (Real.le_arcsin_iff_sin_le hφ hk).symm

/-- On the decreasing half of the positive sine period, the second endpoint is
`π-arcsin k`. -/
theorem sin_le_iff_pi_sub_arcsin_le_of_mem_right_half
    {k φ : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hφhalf : Real.pi / 2 ≤ φ) (hφpi : φ ≤ Real.pi) :
    Real.sin φ ≤ k ↔ Real.pi - Real.arcsin k ≤ φ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hy0 : 0 ≤ Real.pi - φ := by linarith
  have hyhalf : Real.pi - φ ≤ Real.pi / 2 := by linarith
  rw [← Real.sin_pi_sub φ]
  rw [sin_le_iff_le_arcsin_of_mem_left_half hk0 hk1 hy0 hyhalf]
  constructor <;> intro h <;> linarith

/-- Exact two-interval classification of `sin φ ≤ k` on one positive period.
The two intervals collapse to the endpoints when `k=0`; for `0<k<1` they are
the two closed height windows used in Li's small-radius trace analysis. -/
theorem positivePeriod_sin_le_eq_twoIntervals
    {k φ : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) :
    φ ∈ Icc (0 : ℝ) Real.pi ∧ Real.sin φ ≤ k ↔
      φ ∈ Icc 0 (Real.arcsin k) ∪
        Icc (Real.pi - Real.arcsin k) Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  constructor
  · rintro ⟨hφ, hs⟩
    rcases le_total φ (Real.pi / 2) with hleft | hright
    · exact Or.inl ⟨hφ.1,
        (sin_le_iff_le_arcsin_of_mem_left_half hk0 hk1 hφ.1 hleft).mp hs⟩
    · exact Or.inr ⟨
        (sin_le_iff_pi_sub_arcsin_le_of_mem_right_half hk0 hk1 hright hφ.2).mp hs,
        hφ.2⟩
  · rintro (hφ | hφ)
    · have ha0 : 0 ≤ Real.arcsin k := Real.arcsin_nonneg.mpr hk0
      have hahalf := Real.arcsin_le_pi_div_two k
      exact ⟨⟨hφ.1, hφ.2.trans (hahalf.trans (half_le_self hpi.le))⟩,
        (sin_le_iff_le_arcsin_of_mem_left_half hk0 hk1 hφ.1
          (hφ.2.trans hahalf)).mpr hφ.2⟩
    · have ha0 : 0 ≤ Real.arcsin k := Real.arcsin_nonneg.mpr hk0
      have hahalf := Real.arcsin_le_pi_div_two k
      refine ⟨⟨by linarith [hφ.1], hφ.2⟩, ?_⟩
      exact (sin_le_iff_pi_sub_arcsin_le_of_mem_right_half hk0 hk1
        (by linarith [hφ.1]) hφ.2).mpr hφ.1

/-- The zero-height threshold is the endpoint-degenerate case of the same exact
classification. -/
theorem positivePeriod_sin_le_zero_eq_endpoints (φ : ℝ) :
    φ ∈ Icc (0 : ℝ) Real.pi ∧ Real.sin φ ≤ 0 ↔
      φ ∈ Icc 0 0 ∪ Icc Real.pi Real.pi := by
  simpa using (positivePeriod_sin_le_eq_twoIntervals (φ := φ) (k := 0)
    (by norm_num) (by norm_num))

/-- At the boundary `δ=r` the height inequality no longer cuts a middle gap:
`sin φ ≤ 1` throughout the complete positive half-period. -/
theorem positivePeriod_sin_le_one (φ : ℝ) :
    φ ∈ Icc (0 : ℝ) Real.pi ∧ Real.sin φ ≤ 1 ↔
      φ ∈ Icc (0 : ℝ) Real.pi := by
  exact and_iff_left_of_imp (fun _ => Real.sin_le_one φ)

/-- The two base-endpoint inequalities form one order-convex angular window
inside `(0,π)`.  This is the division-free cotangent monotonicity argument:
cross multiplication is justified by positivity of sine, and no endpoint
envelope is introduced. -/
theorem tangential_inequalities_between
    {δ a b x y z : ℝ} (hδ : 0 ≤ δ)
    (hx0 : 0 < x) (hzpi : z < Real.pi) (hxy : x ≤ y) (hyz : y ≤ z)
    (hxupper : δ * Real.cos x ≤ b * Real.sin x)
    (hzlower : a * Real.sin z ≤ δ * Real.cos z) :
    a * Real.sin y ≤ δ * Real.cos y ∧
      δ * Real.cos y ≤ b * Real.sin y := by
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hypi : y < Real.pi := lt_of_le_of_lt hyz hzpi
  have hxpi : x < Real.pi := lt_of_le_of_lt (hxy.trans hyz) hzpi
  have hzp : 0 < Real.sin z :=
    Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hx0 (hxy.trans hyz)) hzpi
  have hyp : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi hy0 hypi
  have hxp : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
  have hzy : 0 ≤ Real.sin (z - y) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hyz) (by linarith [Real.pi_pos])
  have hyx : 0 ≤ Real.sin (y - x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hxy) (by linarith [Real.pi_pos])
  have hanti_yz :
      δ * Real.cos z * Real.sin y ≤ δ * Real.cos y * Real.sin z := by
    rw [Real.sin_sub] at hzy
    nlinarith
  have hanti_xy :
      δ * Real.cos y * Real.sin x ≤ δ * Real.cos x * Real.sin y := by
    rw [Real.sin_sub] at hyx
    nlinarith
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hzlower hyp.le]
  · nlinarith [mul_le_mul_of_nonneg_right hxupper hyp.le]

/-- The principal positive-period trace predicate after dividing the eliminated
coordinate inequalities by the positive factors `r` and `δ`. -/
def principalTraceWindow (δ a b k : ℝ) : Set ℝ :=
  {φ | 0 < φ ∧ φ < Real.pi ∧ Real.sin φ ≤ k ∧
    a * Real.sin φ ≤ δ * Real.cos φ ∧
    δ * Real.cos φ ≤ b * Real.sin φ}

/-- On a specified positive half-period chart, the raw triangle trace is
*exactly* the translate of `principalTraceWindow`.  This is the missing
two-way bridge: neither side is an endpoint envelope or merely a necessary
condition. -/
theorem mem_trianglePolarTrace_iff_shifted_principalTraceWindow
    {α δ c r θ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hδr : δ < r)
    (hchart0 : 0 ≤ θ - α) (hchartπ : θ - α ≤ Real.pi) :
    θ ∈ trianglePolarTrace (supportNeedleTriangle α δ c) r ↔
      θ - α ∈ principalTraceWindow δ (c - 1 / 2) (c + 1 / 2) (δ / r) := by
  have hk1 : δ / r < 1 := (div_lt_one hr).2 hδr
  rw [mem_trianglePolarTrace_eliminatedCoordinates_iff α δ c r θ hr hδ]
  change _ ↔ 0 < θ - α ∧ θ - α < Real.pi ∧
    Real.sin (θ - α) ≤ δ / r ∧
    (c - 1 / 2) * Real.sin (θ - α) ≤ δ * Real.cos (θ - α) ∧
    δ * Real.cos (θ - α) ≤ (c + 1 / 2) * Real.sin (θ - α)
  have hsin_nonneg : 0 ≤ Real.sin (θ - α) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hchart0 hchartπ
  constructor
  · rintro ⟨hpos, hheight, hlower, hupper⟩
    have hsinpos : 0 < Real.sin (θ - α) := by nlinarith
    have hφ0 : 0 < θ - α := by
      exact lt_of_le_of_ne hchart0 (fun h => by
        rw [← h] at hsinpos; simp at hsinpos)
    have hφπ : θ - α < Real.pi := by
      exact lt_of_le_of_ne hchartπ (fun h => by
        rw [h] at hsinpos; simp at hsinpos)
    refine ⟨hφ0, hφπ, ?_, ?_, ?_⟩
    · exact (le_div_iff₀ hr).2 (by nlinarith [hk1])
    · nlinarith
    · nlinarith
  · rintro ⟨hφ0, hφπ, hheight, hlower, hupper⟩
    have hsinpos : 0 < Real.sin (θ - α) :=
      Real.sin_pos_of_pos_of_lt_pi hφ0 hφπ
    refine ⟨mul_pos hr hsinpos, ?_, ?_, ?_⟩
    · have := (le_div_iff₀ hr).1 hheight
      nlinarith
    · nlinarith
    · nlinarith

/-- The same bridge as a literal equality of the charted raw trace with the
shifted principal window.  Stating the chart in the set avoids accidentally
claiming that a periodic real-angle trace is bounded on all of `ℝ`. -/
theorem trianglePolarTrace_inter_positiveChart_eq_shift_principalTraceWindow
    {α δ c r : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hδr : δ < r) :
    trianglePolarTrace (supportNeedleTriangle α δ c) r ∩ Icc α (α + Real.pi) =
      {θ | θ - α ∈ principalTraceWindow δ (c - 1 / 2) (c + 1 / 2) (δ / r)} := by
  ext θ
  constructor
  · rintro ⟨htrace, hchart⟩
    exact (mem_trianglePolarTrace_iff_shifted_principalTraceWindow hr hδ hδr
      (by linarith [hchart.1]) (by linarith [hchart.2])).1 htrace
  · intro hw
    have hφ := hw
    change 0 < θ - α ∧ θ - α < Real.pi ∧ _ at hφ
    refine ⟨(mem_trianglePolarTrace_iff_shifted_principalTraceWindow hr hδ hδr
      hφ.1.le hφ.2.1.le).2 hw, ⟨by linarith, by linarith⟩⟩

/-- At zero support height the charted trace degenerates to at most the two
radial endpoint contacts.  Each disjunct is a genuine singleton condition; no
positive-height division or principal-window theorem is reused. -/
theorem mem_trianglePolarTrace_zeroHeight_iff
    {α c r θ : ℝ} (hr : 0 < r)
    (hchart0 : 0 ≤ θ - α) (hchartπ : θ - α ≤ Real.pi) :
    θ ∈ trianglePolarTrace (supportNeedleTriangle α 0 c) r ↔
      (θ = α ∧ r ≤ c + 1 / 2) ∨
        (θ = α + Real.pi ∧ r ≤ 1 / 2 - c) := by
  rw [mem_trianglePolarTrace_coordinateInequalities_iff α 0 c r θ hr]
  constructor
  · rintro ⟨lam, hlam, hnormal, hlower, hupper⟩
    have hs : Real.sin (θ - α) = 0 := by nlinarith
    by_cases hpi : θ - α = Real.pi
    · right
      have hθ : θ = α + Real.pi := by linarith
      refine ⟨hθ, ?_⟩
      rw [hpi] at hlower hupper
      simp at hlower hupper
      have ha_neg : c - 1 / 2 < 0 := by
        by_contra hn
        have : 0 ≤ lam * (c - 1 / 2) := mul_nonneg hlam.1.le (le_of_not_gt hn)
        linarith
      have hscale : c - 1 / 2 ≤ lam * (c - 1 / 2) := by
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlam.2) ha_neg.le]
      linarith
    · have hlt : θ - α < Real.pi := lt_of_le_of_ne hchartπ hpi
      have hzero : θ - α = 0 :=
        (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [Real.pi_pos]) hlt).1 hs
      left
      refine ⟨by linarith, ?_⟩
      rw [hzero] at hlower hupper
      simp at hlower hupper
      have hb_pos : 0 < c + 1 / 2 := by
        by_contra hn
        have : lam * (c + 1 / 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam.1.le (le_of_not_gt hn)
        linarith
      have hscale : lam * (c + 1 / 2) ≤ c + 1 / 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hlam.2) hb_pos.le]
      linarith
  · rintro (⟨rfl, hb⟩ | ⟨rfl, ha⟩)
    · let b := c + 1 / 2
      have hbpos : 0 < b := lt_of_lt_of_le hr hb
      let lam := r / b
      have hlam : lam ∈ Ioc (0 : ℝ) 1 :=
        ⟨div_pos hr hbpos, (div_le_one hbpos).2 hb⟩
      refine ⟨lam, hlam, by simp, ?_, ?_⟩
      · simp only [sub_self, Real.cos_zero, mul_one]
        have hab : c - 1 / 2 ≤ b := by dsimp [b]; linarith
        have hm := mul_le_mul_of_nonneg_left hab hlam.1.le
        have heq : lam * b = r := by
          dsimp [lam]
          exact div_mul_cancel₀ r hbpos.ne'
        change lam * (c - 1 / 2) ≤ r
        linarith
      · simp only [sub_self, Real.cos_zero, mul_one]
        change r ≤ lam * b
        have heq : lam * b = r := by
          dsimp [lam]
          exact div_mul_cancel₀ r hbpos.ne'
        linarith
    · let d := 1 / 2 - c
      have hdpos : 0 < d := lt_of_lt_of_le hr ha
      let lam := r / d
      have hlam : lam ∈ Ioc (0 : ℝ) 1 :=
        ⟨div_pos hr hdpos, (div_le_one hdpos).2 ha⟩
      refine ⟨lam, hlam, by simp, ?_, ?_⟩
      · rw [show α + Real.pi - α = Real.pi by ring]
        simp only [Real.cos_pi, mul_neg, mul_one]
        have heq : lam * (-d) = -r := by
          have hp : lam * d = r := by
            dsimp [lam]
            exact div_mul_cancel₀ r hdpos.ne'
          linarith
        change lam * (c - 1 / 2) ≤ -r
        have hcd : c - 1 / 2 = -d := by dsimp [d]; ring
        rw [hcd, heq]
      · rw [show α + Real.pi - α = Real.pi by ring]
        simp only [Real.cos_pi, mul_neg, mul_one]
        have hab : -(d) ≤ c + 1 / 2 := by dsimp [d]; linarith
        have hm := mul_le_mul_of_nonneg_left hab hlam.1.le
        have heq : lam * (-d) = -r := by
          have hp : lam * d = r := by
            dsimp [lam]
            exact div_mul_cancel₀ r hdpos.ne'
          linarith
        linarith

/-- At `δ = r`, the same exact coordinate bridge holds but the height
inequality is redundant (`sin φ ≤ 1`).  This boundary case is deliberately
separate from the strict small-radius theorem. -/
theorem mem_trianglePolarTrace_iff_principalTraceWindow_height_one
    {α c r θ : ℝ} (hr : 0 < r)
    (hchart0 : 0 ≤ θ - α) (hchartπ : θ - α ≤ Real.pi) :
    θ ∈ trianglePolarTrace (supportNeedleTriangle α r c) r ↔
      θ - α ∈ principalTraceWindow r (c - 1 / 2) (c + 1 / 2) 1 := by
  rw [mem_trianglePolarTrace_eliminatedCoordinates_iff α r c r θ hr hr]
  change _ ↔ 0 < θ - α ∧ θ - α < Real.pi ∧ Real.sin (θ - α) ≤ 1 ∧ _
  have hs := Real.sin_le_one (θ - α)
  have hsin_nonneg : 0 ≤ Real.sin (θ - α) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hchart0 hchartπ
  constructor
  · rintro ⟨hpos, hheight, hlower, hupper⟩
    have hsinpos : 0 < Real.sin (θ - α) := by nlinarith
    have hφ0 : 0 < θ - α := lt_of_le_of_ne hchart0 (fun he => by
      rw [← he] at hsinpos; simp at hsinpos)
    have hφπ : θ - α < Real.pi := lt_of_le_of_ne hchartπ (fun he => by
      rw [he] at hsinpos; simp at hsinpos)
    exact ⟨hφ0, hφπ, hs, by nlinarith, by nlinarith⟩
  · rintro ⟨hφ0, hφπ, _, hlower, hupper⟩
    have hsinpos := Real.sin_pos_of_pos_of_lt_pi hφ0 hφπ
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- In the regime `0 ≤ δ` and `0 ≤ k < 1`, each half-period piece of the real
trace is order-convex.  Together with
`positivePeriod_sin_le_eq_twoIntervals`, this is the promised at-most-two
interval classification before quotienting: base-endpoint tangencies are kept
because all tangential inequalities are non-strict. -/
theorem principalTraceWindow_half_ordConnected
    {δ a b k : ℝ} (hδ : 0 ≤ δ) (_hk0 : 0 ≤ k) (_hk1 : k < 1) :
    (principalTraceWindow δ a b k ∩ Iic (Real.pi / 2)).OrdConnected ∧
      (principalTraceWindow δ a b k ∩ Ici (Real.pi / 2)).OrdConnected := by
  rw [ordConnected_iff, ordConnected_iff]
  constructor
  · intro x hx z hz hxz y hy
    rcases hx with ⟨⟨hx0, hxpi, hxheight, hxlower, hxupper⟩, hxhalf⟩
    rcases hz with ⟨⟨hz0, hzpi, hzheight, hzlower, hzupper⟩, hzhalf⟩
    have hy0 : 0 < y := lt_of_lt_of_le hx0 hy.1
    have hypi : y < Real.pi := lt_of_le_of_lt hy.2 hzpi
    have hsin : Real.sin y ≤ Real.sin z :=
      Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [Real.pi_pos]) hzhalf hy.2
    have htang := tangential_inequalities_between hδ hx0 hzpi hy.1 hy.2 hxupper hzlower
    exact ⟨⟨hy0, hypi, hsin.trans hzheight, htang.1, htang.2⟩,
      hy.2.trans hzhalf⟩
  · intro x hx z hz hxz y hy
    rcases hx with ⟨⟨hx0, hxpi, hxheight, hxlower, hxupper⟩, hxhalf⟩
    rcases hz with ⟨⟨hz0, hzpi, hzheight, hzlower, hzupper⟩, hzhalf⟩
    have hy0 : 0 < y := lt_of_lt_of_le hx0 hy.1
    have hypi : y < Real.pi := lt_of_le_of_lt hy.2 hzpi
    have hsubmono : Real.sin (Real.pi - y) ≤ Real.sin (Real.pi - x) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two
        (calc
          -(Real.pi / 2) ≤ 0 := neg_nonpos.mpr (div_nonneg Real.pi_pos.le (by norm_num))
          _ ≤ Real.pi - y := sub_nonneg.mpr hypi.le)
        (calc
          Real.pi - x ≤ Real.pi - Real.pi / 2 := sub_le_sub_left hxhalf Real.pi
          _ = Real.pi / 2 := by ring)
        (sub_le_sub_left hy.1 Real.pi)
    have hsin : Real.sin y ≤ Real.sin x := by
      simpa only [Real.sin_pi_sub] using hsubmono
    have htang := tangential_inequalities_between hδ hx0 hzpi hy.1 hy.2 hxupper hzlower
    exact ⟨⟨hy0, hypi, hsin.trans hxheight, htang.1, htang.2⟩,
      hxhalf.trans hy.1⟩

/-! ### Explicit closed pieces -/

def principalTraceLeftPiece (δ a b k : ℝ) : Set ℝ :=
  Icc 0 (Real.arcsin k) ∩
    {φ | a * Real.sin φ ≤ δ * Real.cos φ ∧
      δ * Real.cos φ ≤ b * Real.sin φ}

def principalTraceRightPiece (δ a b k : ℝ) : Set ℝ :=
  Icc (Real.pi - Real.arcsin k) Real.pi ∩
    {φ | a * Real.sin φ ≤ δ * Real.cos φ ∧
      δ * Real.cos φ ≤ b * Real.sin φ}

theorem isClosed_principalTraceTangential (δ a b : ℝ) :
    IsClosed {φ : ℝ | a * Real.sin φ ≤ δ * Real.cos φ ∧
      δ * Real.cos φ ≤ b * Real.sin φ} := by
  apply IsClosed.inter
  · exact isClosed_le
      (continuous_const.mul Real.continuous_sin)
      (continuous_const.mul Real.continuous_cos)
  · exact isClosed_le
      (continuous_const.mul Real.continuous_cos)
      (continuous_const.mul Real.continuous_sin)

theorem isCompact_principalTraceLeftPiece (δ a b k : ℝ) :
    IsCompact (principalTraceLeftPiece δ a b k) := by
  exact isCompact_Icc.inter_right (isClosed_principalTraceTangential δ a b)

theorem isCompact_principalTraceRightPiece (δ a b k : ℝ) :
    IsCompact (principalTraceRightPiece δ a b k) := by
  exact isCompact_Icc.inter_right (isClosed_principalTraceTangential δ a b)

theorem principalTraceWindow_left_eq_closedPiece
    {δ a b k : ℝ} (hδ : 0 < δ) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    principalTraceWindow δ a b k ∩ Iic (Real.pi / 2) =
      principalTraceLeftPiece δ a b k := by
  ext φ
  constructor
  · rintro ⟨⟨hφ0, hφpi, hs, hlo, hhi⟩, hhalf⟩
    exact ⟨⟨hφ0.le,
      (sin_le_iff_le_arcsin_of_mem_left_half hk0 hk1 hφ0.le hhalf).mp hs⟩,
      hlo, hhi⟩
  · rintro ⟨hI, hlo, hhi⟩
    have hahalf : Real.arcsin k ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two k
    have hhalf : φ ≤ Real.pi / 2 := hI.2.trans hahalf
    have hφ0 : 0 < φ := lt_of_le_of_ne hI.1 (fun he => by
      rw [← he] at hhi; simp at hhi; linarith)
    have hφpi : φ < Real.pi := lt_of_le_of_lt hhalf (by linarith [Real.pi_pos])
    have hs := (sin_le_iff_le_arcsin_of_mem_left_half hk0 hk1 hI.1 hhalf).2 hI.2
    exact ⟨⟨hφ0, hφpi, hs, hlo, hhi⟩, hhalf⟩

theorem principalTraceWindow_right_eq_closedPiece
    {δ a b k : ℝ} (hδ : 0 < δ) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    principalTraceWindow δ a b k ∩ Ici (Real.pi / 2) =
      principalTraceRightPiece δ a b k := by
  ext φ
  constructor
  · rintro ⟨⟨hφ0, hφpi, hs, hlo, hhi⟩, hhalf⟩
    exact ⟨⟨(sin_le_iff_pi_sub_arcsin_le_of_mem_right_half
      hk0 hk1 hhalf hφpi.le).mp hs, hφpi.le⟩, hlo, hhi⟩
  · rintro ⟨hI, hlo, hhi⟩
    have hahalf : Real.arcsin k ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two k
    have hhalf : Real.pi / 2 ≤ φ := by linarith [hI.1]
    have hφ0 : 0 < φ := lt_of_lt_of_le (by linarith [Real.pi_pos]) hhalf
    have hφpi : φ < Real.pi := lt_of_le_of_ne hI.2 (fun he => by
      rw [he] at hlo; simp at hlo; linarith)
    have hs := (sin_le_iff_pi_sub_arcsin_le_of_mem_right_half
      hk0 hk1 hhalf hI.2).2 hI.1
    exact ⟨⟨hφ0, hφpi, hs, hlo, hhi⟩, hhalf⟩

/-- Explicit empty/Icc/singleton normal form for a compact order-connected set. -/
inductive ClosedIccPresentation (s : Set ℝ) : Type where
  | empty (cover : s = ∅)
  | interval (lo hi : ℝ) (le_endpoints : lo ≤ hi) (cover : s = Icc lo hi)

noncomputable def closedIccPresentationOfCompactOrdConnected
    (s : Set ℝ) (hcompact : IsCompact s) (hord : s.OrdConnected) :
    ClosedIccPresentation s := by
  by_cases hempty : s = ∅
  · exact .empty hempty
  · have hne : s.Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
    have hlo : sInf s ∈ s := hcompact.isClosed.csInf_mem hne hcompact.bddBelow
    have hhi : sSup s ∈ s := hcompact.isClosed.csSup_mem hne hcompact.bddAbove
    refine .interval (sInf s) (sSup s)
      (csInf_le hcompact.bddBelow hhi) ?_
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨csInf_le hcompact.bddBelow hx, le_csSup hcompact.bddAbove hx⟩
    · exact hord.out hlo hhi

/-- Attained extrema of one nonempty fundamental-chart piece.  This is the
correct bounded replacement for extrema of the periodic trace on all of `ℝ`. -/
structure FundamentalChartExtrema (s : Set ℝ) where
  lo : ℝ
  hi : ℝ
  least : IsLeast s lo
  greatest : IsGreatest s hi

def ClosedIccPresentation.extrema?
    {s : Set ℝ} : ClosedIccPresentation s → Option (FundamentalChartExtrema s)
  | .empty _ => none
  | .interval lo hi hle hcover => some {
      lo := lo
      hi := hi
      least := hcover.symm ▸ ⟨⟨le_rfl, hle⟩, fun _ hx => hx.1⟩
      greatest := hcover.symm ▸ ⟨⟨hle, le_rfl⟩, fun _ hx => hx.2⟩ }

/-- At an endpoint of a nonempty closed principal piece, one of the three
 defining inequalities is active. -/
def PrincipalTraceEndpointActive (δ a b k φ : ℝ) : Prop :=
  Real.sin φ = k ∨ a * Real.sin φ = δ * Real.cos φ ∨
    δ * Real.cos φ = b * Real.sin φ

/-- The lower endpoint of an actual closed left-piece presentation is active.
If all inequalities were strict, continuity would allow a smaller point. -/
theorem principalTraceLeftPiece_interval_lo_active
    {δ a b k lo hi : ℝ} (hδ : 0 < δ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hle : lo ≤ hi)
    (hcover : principalTraceLeftPiece δ a b k = Icc lo hi) :
    PrincipalTraceEndpointActive δ a b k lo := by
  have hlo : lo ∈ principalTraceLeftPiece δ a b k :=
    hcover.symm ▸ ⟨le_rfl, hle⟩
  rcases hlo with ⟨hloI, hloLower, hloUpper⟩
  unfold PrincipalTraceEndpointActive
  by_contra hn
  push Not at hn
  have hlohalf : lo ≤ Real.pi / 2 :=
    hloI.2.trans (Real.arcsin_le_pi_div_two k)
  have hsle : Real.sin lo ≤ k :=
    (sin_le_iff_le_arcsin_of_mem_left_half hk0 hk1 hloI.1 hlohalf).2 hloI.2
  have hs : Real.sin lo < k := lt_of_le_of_ne hsle hn.1
  have hLower : a * Real.sin lo < δ * Real.cos lo :=
    lt_of_le_of_ne hloLower hn.2.1
  have hUpper : δ * Real.cos lo < b * Real.sin lo :=
    lt_of_le_of_ne hloUpper hn.2.2
  have hopen : IsOpen {x : ℝ | Real.sin x < k ∧
      a * Real.sin x < δ * Real.cos x ∧ δ * Real.cos x < b * Real.sin x} := by
    exact (isOpen_lt Real.continuous_sin continuous_const).inter
      ((isOpen_lt (continuous_const.mul Real.continuous_sin)
        (continuous_const.mul Real.continuous_cos)).inter
      (isOpen_lt (continuous_const.mul Real.continuous_cos)
        (continuous_const.mul Real.continuous_sin)))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen lo ⟨hs, hLower, hUpper⟩
  have hlo0 : 0 < lo := by
    by_contra hnot
    have heq : lo = 0 := le_antisymm (le_of_not_gt hnot) hloI.1
    rw [heq] at hUpper
    simp at hUpper
    linarith
  let x := lo - min ε lo / 2
  have hmin : 0 < min ε lo := lt_min hε hlo0
  have hxball : x ∈ Metric.ball lo ε := by
    rw [Metric.mem_ball]
    simp only [Real.dist_eq, x]
    have hm : min ε lo ≤ ε := min_le_left _ _
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hxstrict := hball hxball
  have hxpiece : x ∈ principalTraceLeftPiece δ a b k := by
    exact ⟨⟨by dsimp [x]; have := min_le_right ε lo; linarith,
      by dsimp [x]; nlinarith [hmin, hloI.2]⟩, hxstrict.2.1.le, hxstrict.2.2.le⟩
  have hxI : x ∈ Icc lo hi := hcover ▸ hxpiece
  exact (not_lt_of_ge hxI.1) (by dsimp [x]; linarith)

/-- The upper endpoint of an actual closed left-piece presentation is active. -/
theorem principalTraceLeftPiece_interval_hi_active
    {δ a b k lo hi : ℝ} (hδ : 0 < δ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hle : lo ≤ hi)
    (hcover : principalTraceLeftPiece δ a b k = Icc lo hi) :
    PrincipalTraceEndpointActive δ a b k hi := by
  have hhi : hi ∈ principalTraceLeftPiece δ a b k :=
    hcover.symm ▸ ⟨hle, le_rfl⟩
  rcases hhi with ⟨hhiI, hhiLower, hhiUpper⟩
  unfold PrincipalTraceEndpointActive
  by_contra hn
  push Not at hn
  have hhihalf : hi ≤ Real.pi / 2 :=
    hhiI.2.trans (Real.arcsin_le_pi_div_two k)
  have hsle : Real.sin hi ≤ k :=
    (sin_le_iff_le_arcsin_of_mem_left_half hk0 hk1 hhiI.1 hhihalf).2 hhiI.2
  have hs : Real.sin hi < k := lt_of_le_of_ne hsle hn.1
  have hLower : a * Real.sin hi < δ * Real.cos hi :=
    lt_of_le_of_ne hhiLower hn.2.1
  have hUpper : δ * Real.cos hi < b * Real.sin hi :=
    lt_of_le_of_ne hhiUpper hn.2.2
  have hopen : IsOpen {x : ℝ | Real.sin x < k ∧
      a * Real.sin x < δ * Real.cos x ∧ δ * Real.cos x < b * Real.sin x} := by
    exact (isOpen_lt Real.continuous_sin continuous_const).inter
      ((isOpen_lt (continuous_const.mul Real.continuous_sin)
        (continuous_const.mul Real.continuous_cos)).inter
      (isOpen_lt (continuous_const.mul Real.continuous_cos)
        (continuous_const.mul Real.continuous_sin)))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen hi ⟨hs, hLower, hUpper⟩
  have hhiAsin : hi < Real.arcsin k := by
    apply lt_of_le_of_ne hhiI.2
    intro he
    apply hn.1
    rw [he]
    exact Real.sin_arcsin (by linarith) hk1.le
  let x := hi + min ε (Real.arcsin k - hi) / 2
  have hmin : 0 < min ε (Real.arcsin k - hi) :=
    lt_min hε (sub_pos.mpr hhiAsin)
  have hxball : x ∈ Metric.ball hi ε := by
    rw [Metric.mem_ball]
    simp only [Real.dist_eq, x]
    have hm : min ε (Real.arcsin k - hi) ≤ ε := min_le_left _ _
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hxstrict := hball hxball
  have hxpiece : x ∈ principalTraceLeftPiece δ a b k := by
    exact ⟨⟨hhiI.1.trans (by dsimp [x]; linarith),
      by dsimp [x]; have := min_le_right ε (Real.arcsin k - hi); linarith⟩,
      hxstrict.2.1.le, hxstrict.2.2.le⟩
  have hxI : x ∈ Icc lo hi := hcover ▸ hxpiece
  exact (not_lt_of_ge hxI.2) (by dsimp [x]; linarith)

/-- The symmetric endpoint-extremum argument for the right closed piece. -/
theorem principalTraceRightPiece_interval_hi_active
    {δ a b k lo hi : ℝ} (hδ : 0 < δ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hle : lo ≤ hi)
    (hcover : principalTraceRightPiece δ a b k = Icc lo hi) :
    PrincipalTraceEndpointActive δ a b k hi := by
  have hhi : hi ∈ principalTraceRightPiece δ a b k :=
    hcover.symm ▸ ⟨hle, le_rfl⟩
  rcases hhi with ⟨hhiI, hhiLower, hhiUpper⟩
  unfold PrincipalTraceEndpointActive
  by_contra hn
  push Not at hn
  have hhihalf : Real.pi / 2 ≤ hi := by
    linarith [hhiI.1, Real.arcsin_le_pi_div_two k]
  have hsle : Real.sin hi ≤ k :=
    (sin_le_iff_pi_sub_arcsin_le_of_mem_right_half hk0 hk1 hhihalf hhiI.2).2 hhiI.1
  have hs : Real.sin hi < k := lt_of_le_of_ne hsle hn.1
  have hLower : a * Real.sin hi < δ * Real.cos hi :=
    lt_of_le_of_ne hhiLower hn.2.1
  have hUpper : δ * Real.cos hi < b * Real.sin hi :=
    lt_of_le_of_ne hhiUpper hn.2.2
  have hopen : IsOpen {x : ℝ | Real.sin x < k ∧
      a * Real.sin x < δ * Real.cos x ∧ δ * Real.cos x < b * Real.sin x} := by
    exact (isOpen_lt Real.continuous_sin continuous_const).inter
      ((isOpen_lt (continuous_const.mul Real.continuous_sin)
        (continuous_const.mul Real.continuous_cos)).inter
      (isOpen_lt (continuous_const.mul Real.continuous_cos)
        (continuous_const.mul Real.continuous_sin)))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen hi ⟨hs, hLower, hUpper⟩
  have hhipi : hi < Real.pi := by
    by_contra hnot
    have heq : hi = Real.pi := le_antisymm hhiI.2 (le_of_not_gt hnot)
    rw [heq] at hLower
    simp at hLower
    linarith
  let x := hi + min ε (Real.pi - hi) / 2
  have hmin : 0 < min ε (Real.pi - hi) := lt_min hε (sub_pos.mpr hhipi)
  have hxball : x ∈ Metric.ball hi ε := by
    rw [Metric.mem_ball]
    simp only [Real.dist_eq, x]
    have hm : min ε (Real.pi - hi) ≤ ε := min_le_left _ _
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hxstrict := hball hxball
  have hxpiece : x ∈ principalTraceRightPiece δ a b k := by
    exact ⟨⟨hhiI.1.trans (by dsimp [x]; linarith),
      by dsimp [x]; have := min_le_right ε (Real.pi - hi); linarith⟩,
      hxstrict.2.1.le, hxstrict.2.2.le⟩
  have hxI : x ∈ Icc lo hi := hcover ▸ hxpiece
  exact (not_lt_of_ge hxI.2) (by dsimp [x]; linarith)

/-- The lower endpoint of an actual closed right-piece presentation is active. -/
theorem principalTraceRightPiece_interval_lo_active
    {δ a b k lo hi : ℝ} (hδ : 0 < δ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hle : lo ≤ hi)
    (hcover : principalTraceRightPiece δ a b k = Icc lo hi) :
    PrincipalTraceEndpointActive δ a b k lo := by
  have hlo : lo ∈ principalTraceRightPiece δ a b k :=
    hcover.symm ▸ ⟨le_rfl, hle⟩
  rcases hlo with ⟨hloI, hloLower, hloUpper⟩
  unfold PrincipalTraceEndpointActive
  by_contra hn
  push Not at hn
  have hlohalf : Real.pi / 2 ≤ lo := by
    linarith [hloI.1, Real.arcsin_le_pi_div_two k]
  have hsle : Real.sin lo ≤ k :=
    (sin_le_iff_pi_sub_arcsin_le_of_mem_right_half hk0 hk1 hlohalf hloI.2).2 hloI.1
  have hs : Real.sin lo < k := lt_of_le_of_ne hsle hn.1
  have hLower : a * Real.sin lo < δ * Real.cos lo :=
    lt_of_le_of_ne hloLower hn.2.1
  have hUpper : δ * Real.cos lo < b * Real.sin lo :=
    lt_of_le_of_ne hloUpper hn.2.2
  have hopen : IsOpen {x : ℝ | Real.sin x < k ∧
      a * Real.sin x < δ * Real.cos x ∧ δ * Real.cos x < b * Real.sin x} := by
    exact (isOpen_lt Real.continuous_sin continuous_const).inter
      ((isOpen_lt (continuous_const.mul Real.continuous_sin)
        (continuous_const.mul Real.continuous_cos)).inter
      (isOpen_lt (continuous_const.mul Real.continuous_cos)
        (continuous_const.mul Real.continuous_sin)))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen lo ⟨hs, hLower, hUpper⟩
  have hloBound : Real.pi - Real.arcsin k < lo := by
    apply lt_of_le_of_ne hloI.1
    intro he
    apply hn.1
    rw [← he, Real.sin_pi_sub]
    exact Real.sin_arcsin (by linarith) hk1.le
  let x := lo - min ε (lo - (Real.pi - Real.arcsin k)) / 2
  have hmin : 0 < min ε (lo - (Real.pi - Real.arcsin k)) :=
    lt_min hε (sub_pos.mpr hloBound)
  have hxball : x ∈ Metric.ball lo ε := by
    rw [Metric.mem_ball]
    simp only [Real.dist_eq, x]
    have hm : min ε (lo - (Real.pi - Real.arcsin k)) ≤ ε := min_le_left _ _
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hxstrict := hball hxball
  have hxpiece : x ∈ principalTraceRightPiece δ a b k := by
    refine ⟨⟨?_, ?_⟩, hxstrict.2.1.le, hxstrict.2.2.le⟩
    · dsimp [x]
      have hm := min_le_right ε (lo - (Real.pi - Real.arcsin k))
      linarith
    · dsimp [x]
      linarith [hloI.2]
  have hxI : x ∈ Icc lo hi := hcover ▸ hxpiece
  exact (not_lt_of_ge hxI.1) (by dsimp [x]; linarith)

/-- The strict-small-radius pieces now have actual closed presentations. -/
noncomputable def principalTraceClosedPresentations
    {δ a b k : ℝ} (hδ : 0 < δ) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    ClosedIccPresentation (principalTraceLeftPiece δ a b k) ×
      ClosedIccPresentation (principalTraceRightPiece δ a b k) :=
  ⟨closedIccPresentationOfCompactOrdConnected _
      (isCompact_principalTraceLeftPiece δ a b k)
      ((principalTraceWindow_left_eq_closedPiece hδ hk0 hk1) ▸
        (principalTraceWindow_half_ordConnected hδ.le hk0 hk1).1),
    closedIccPresentationOfCompactOrdConnected _
      (isCompact_principalTraceRightPiece δ a b k)
      ((principalTraceWindow_right_eq_closedPiece hδ hk0 hk1) ▸
        (principalTraceWindow_half_ordConnected hδ.le hk0 hk1).2)⟩

/-! ## The two circles and the quotient `q` -/

abbrev ProjectiveDirection := AddCircle Real.pi
abbrev PolarAngle := AddCircle (2 * Real.pi)

instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩
instance : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩

/-- Reduction of an oriented polar angle modulo `2π` to an unoriented direction
modulo `π`.  This is induced by the identity map on real angles. -/
def polarToProjective : PolarAngle →+ ProjectiveDirection :=
  QuotientAddGroup.map (AddSubgroup.zmultiples (2 * Real.pi))
    (AddSubgroup.zmultiples Real.pi) (AddMonoidHom.id ℝ) (by
      intro x hx
      rw [AddSubgroup.mem_comap]
      rw [AddSubgroup.mem_zmultiples_iff] at hx ⊢
      obtain ⟨n, rfl⟩ := hx
      refine ⟨2 * n, ?_⟩
      simp
      ring)

@[simp] theorem polarToProjective_coe (θ : ℝ) :
    polarToProjective (θ : PolarAngle) = (θ : ProjectiveDirection) := rfl

/-- A closed circle interval, saturated once its nominal length reaches the
positive period.  Closed intervals are used here because endpoint containment
is geometric rather than almost-everywhere. -/
def quotientClosedInterval (p a b : ℝ) [Fact (0 < p)] : Set (AddCircle p) :=
  if p ≤ b - a then Set.univ else (fun t : ℝ => (t : AddCircle p)) '' Icc a b

/-- Closed centered arc. -/
def quotientClosedCenteredArc (p x r : ℝ) [Fact (0 < p)] : Set (AddCircle p) :=
  quotientClosedInterval p (x - r) (x + r)

/-- Closed same-centre dilation, with saturation. -/
def quotientClosedCenteredDilate (g p x r : ℝ) [Fact (0 < p)] : Set (AddCircle p) :=
  quotientClosedInterval p (x - g * r) (x + g * r)

/-- Polar arc represented by the closed lift `[a,b]`. -/
def polarArc (a b : ℝ) : Set PolarAngle := quotientClosedInterval (2 * Real.pi) a b

/-- Projective direction interval represented by the closed lift `[a,b]`. -/
def directionInterval (a b : ℝ) : Set ProjectiveDirection :=
  quotientClosedInterval Real.pi a b

/-- A polar arc of length at most `π` projects to the identically lifted
projective interval. -/
theorem polarToProjective_image_polarArc
    {a b : ℝ} (h0 : 0 ≤ b - a) (hπ : b - a < Real.pi) :
    polarToProjective '' polarArc a b = directionInterval a b := by
  have h2π : b - a < 2 * Real.pi := by linarith [Real.pi_pos]
  simp only [polarArc, directionInterval, quotientClosedInterval,
    if_neg (not_le.mpr h2π), if_neg (not_le.mpr hπ)]
  ext q
  constructor
  · rintro ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩
    exact ⟨θ, hθ, polarToProjective_coe θ⟩
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨(θ : PolarAngle), ⟨θ, hθ, rfl⟩, polarToProjective_coe θ⟩

/-- The projected normalized polar arc `[0,t]` is centered at `t/2`. -/
theorem polarToProjective_image_polarArc_zero
    {t : ℝ} (ht0 : 0 ≤ t) (htπ : t < Real.pi) :
    polarToProjective '' polarArc 0 t =
      quotientClosedCenteredArc Real.pi (t / 2) (t / 2) := by
  rw [polarToProjective_image_polarArc (by linarith) (by linarith)]
  congr 1 <;> ring

/-! ## Li endpoint reconstruction, with centres retained -/

/-- Directions between two lifted critical endpoints. -/
def directionsBetween (α₂ α₁ : ℝ) : Set ProjectiveDirection :=
  directionInterval α₂ α₁

/-- First small-angle endpoint configuration: `α₁=s` and
`α₁-α₂=2s-t` reconstruct the actual direction interval `[t-s,s]`. -/
theorem first_endpoint_configuration
    {t s α₁ α₂ : ℝ} (h₁ : α₁ = s) (hgap : α₁ - α₂ = 2 * s - t) :
    directionsBetween α₂ α₁ = directionInterval (t - s) s := by
  have h₂ : α₂ = t - s := by linarith
  simp [directionsBetween, h₁, h₂]

/-- Exterior/bounded endpoint configuration, with the same algebra and endpoint
parameter `S` (in Li's application `S = arcsin (R₁ sin t)`). -/
theorem exterior_endpoint_configuration
    {t S α₁ α₂ : ℝ} (h₁ : α₁ = S) (hgap : α₁ - α₂ = 2 * S - t) :
    directionsBetween α₂ α₁ = directionInterval (t - S) S := by
  have h₂ : α₂ = t - S := by linarith
  simp [directionsBetween, h₁, h₂]

/-- Both endpoint intervals have midpoint `t/2`; this is an equality of sets,
not merely an equality of printed lengths. -/
theorem directionInterval_endpoint_eq_centered
    {t u : ℝ} :
    directionInterval (t - u) u =
      quotientClosedCenteredArc Real.pi (t / 2) (u - t / 2) := by
  congr 1 <;> ring

/-- A same-centre endpoint interval whose half-length is bounded by `g` times
the polar half-length is contained in the corresponding dilation. -/
theorem endpointEnvelope_subset_sameCentre_dilate
    {g t u : ℝ} (ht : 0 ≤ t) (hu : t / 2 ≤ u)
    (hlen : 2 * u - t ≤ g * t) :
    directionInterval (t - u) u ⊆
      quotientClosedCenteredDilate g Real.pi (t / 2) (t / 2) := by
  rw [directionInterval_endpoint_eq_centered]
  by_cases hsat : Real.pi ≤
      (t / 2 + g * (t / 2)) - (t / 2 - g * (t / 2))
  · have hsat' : Real.pi ≤ g * (t / 2) + g * (t / 2) := by
      nlinarith
    simp [quotientClosedCenteredDilate, quotientClosedInterval, hsat']
  · have htarget :
        (t / 2 + g * (t / 2)) - (t / 2 - g * (t / 2)) < Real.pi :=
      lt_of_not_ge hsat
    have hsource :
        (t / 2 + (u - t / 2)) - (t / 2 - (u - t / 2)) < Real.pi := by
      nlinarith [ht, hu, hlen]
    simp only [quotientClosedCenteredArc, quotientClosedCenteredDilate,
      quotientClosedInterval, if_neg (not_le.mpr hsource),
      if_neg (not_le.mpr htarget)]
    apply image_mono
    apply Icc_subset_Icc <;> nlinarith

/-- Large-angle branch: once `g*t ≥ π`, the projective same-centre dilation is
literally the whole direction circle. -/
theorem large_angle_sameCentre_dilate_eq_univ
    {g t : ℝ} (hlarge : Real.pi ≤ g * t) :
    quotientClosedCenteredDilate g Real.pi (t / 2) (t / 2) = Set.univ := by
  have hlarge' : Real.pi ≤ g * (t / 2) + g * (t / 2) := by
    nlinarith
  simp [quotientClosedCenteredDilate, quotientClosedInterval, hlarge']

/-- First endpoint subcase, promoted from endpoint arithmetic and a length bound
to an actual same-centre set containment. -/
theorem first_endpoint_subset_sameCentre_dilate
    {g t s α₁ α₂ : ℝ} (ht : 0 ≤ t) (hs : t / 2 ≤ s)
    (h₁ : α₁ = s) (hgap : α₁ - α₂ = 2 * s - t)
    (hlen : 2 * s - t ≤ g * t) :
    directionsBetween α₂ α₁ ⊆
      quotientClosedCenteredDilate g Real.pi (t / 2) (t / 2) := by
  rw [first_endpoint_configuration h₁ hgap]
  exact endpointEnvelope_subset_sameCentre_dilate ht hs hlen

/-- Exterior endpoint subcase (including `S = arcsin (R₁ sin t)`). -/
theorem exterior_endpoint_subset_sameCentre_dilate
    {g t S α₁ α₂ : ℝ} (ht : 0 ≤ t) (hS : t / 2 ≤ S)
    (h₁ : α₁ = S) (hgap : α₁ - α₂ = 2 * S - t)
    (hlen : 2 * S - t ≤ g * t) :
    directionsBetween α₂ α₁ ⊆
      quotientClosedCenteredDilate g Real.pi (t / 2) (t / 2) := by
  rw [exterior_endpoint_configuration h₁ hgap]
  exact endpointEnvelope_subset_sameCentre_dilate ht hS hlen

/-- The two Li small-angle endpoint forms. -/
inductive LiEndpointConfiguration (t : ℝ) where
  | interior (s : ℝ)
  | exterior (S : ℝ)

/-- Its explicit direction envelope. -/
def LiEndpointConfiguration.envelope {t : ℝ} :
    LiEndpointConfiguration t → Set ProjectiveDirection
  | .interior s => directionInterval (t - s) s
  | .exterior S => directionInterval (t - S) S

/-- Endpoint half-parameter (`s` or `S`). -/
def LiEndpointConfiguration.upper {t : ℝ} : LiEndpointConfiguration t → ℝ
  | .interior s => s
  | .exterior S => S

/-- Containment for data which is *already* an endpoint configuration.  This is
an interval-algebra scaffold, not a theorem constructing Li's selected arc from
a triangle family. -/
theorem endpointConfiguration_envelope_subset_sameCentre_dilate
    {g t : ℝ} (cfg : LiEndpointConfiguration t)
    (ht0 : 0 ≤ t) (htπ : t < Real.pi)
    (hbranch :
      (t / 2 ≤ cfg.upper ∧ 2 * cfg.upper - t ≤ g * t) ∨
      Real.pi ≤ g * t) :
    cfg.envelope ⊆ quotientClosedCenteredDilate g Real.pi (t / 2) (t / 2) ∧
    polarToProjective '' polarArc 0 t =
      quotientClosedCenteredArc Real.pi (t / 2) (t / 2) := by
  constructor
  · rcases hbranch with hsmall | hlarge
    · cases cfg <;>
        exact endpointEnvelope_subset_sameCentre_dilate ht0 hsmall.1 hsmall.2
    · rw [large_angle_sameCentre_dilate_eq_univ hlarge]
      exact subset_univ _
  · exact polarToProjective_image_polarArc_zero ht0 htπ

/-! ## Direction-indexed families and an honest selected-arc bridge -/

/-- A triangle indexed by its unoriented needle direction.  The real angle is
part of the data, but `direction_eq` prevents silently confusing that lift with
the projective index. -/
structure DirectionNeedle (d : ProjectiveDirection) where
  angle : ℝ
  height : ℝ
  centre : ℝ
  direction_eq : (angle : ProjectiveDirection) = d

/-- The geometric triangle carried by a direction-indexed needle. -/
def DirectionNeedle.triangle {d : ProjectiveDirection} (N : DirectionNeedle d) :
    Set CoordinatePlane := supportNeedleTriangle N.angle N.height N.centre

/-- A normalized closed polar arc.  The strict `π` bound makes projection to
unoriented directions injective on the chosen lift. -/
structure NormalizedPolarArc where
  lo : ℝ
  hi : ℝ
  le_endpoints : lo ≤ hi
  short : hi - lo < Real.pi

namespace NormalizedPolarArc

/-- Carrier of a normalized arc on the polar circle. -/
def carrier (A : NormalizedPolarArc) : Set PolarAngle := polarArc A.lo A.hi

/-- Length of the chosen real lift. -/
def span (A : NormalizedPolarArc) : ℝ := A.hi - A.lo

/-- Rotation transport of a normalized lifted arc. -/
def rotate (β : ℝ) (A : NormalizedPolarArc) : NormalizedPolarArc where
  lo := A.lo + β
  hi := A.hi + β
  le_endpoints := by linarith [A.le_endpoints]
  short := by linarith [A.short]

/-- Reversal transport; endpoints are swapped as well as negated. -/
def reverse (A : NormalizedPolarArc) : NormalizedPolarArc where
  lo := -A.hi
  hi := -A.lo
  le_endpoints := by linarith [A.le_endpoints]
  short := by linarith [A.short]

/-- Change of polar lift by an integral number of full turns. -/
def changeLift (n : ℤ) (A : NormalizedPolarArc) : NormalizedPolarArc :=
  A.rotate ((n : ℝ) * (2 * Real.pi))

@[simp] theorem rotate_lo (β : ℝ) (A : NormalizedPolarArc) :
    (A.rotate β).lo = A.lo + β := rfl

@[simp] theorem rotate_hi (β : ℝ) (A : NormalizedPolarArc) :
    (A.rotate β).hi = A.hi + β := rfl

@[simp] theorem rotate_span (β : ℝ) (A : NormalizedPolarArc) :
    (A.rotate β).span = A.span := by simp [span, rotate]

@[simp] theorem reverse_lo (A : NormalizedPolarArc) : A.reverse.lo = -A.hi := rfl
@[simp] theorem reverse_hi (A : NormalizedPolarArc) : A.reverse.hi = -A.lo := rfl

@[simp] theorem reverse_span (A : NormalizedPolarArc) : A.reverse.span = A.span := by
  simp [span, reverse]
  ring

/-- Rotation transports the polar-circle carrier by circle addition. -/
theorem rotate_carrier (β : ℝ) (A : NormalizedPolarArc) :
    (A.rotate β).carrier = (fun q : PolarAngle => (β : PolarAngle) + q) '' A.carrier := by
  have h2 : A.hi - A.lo < 2 * Real.pi := by linarith [A.short, Real.pi_pos]
  have h2' : (A.hi + β) - (A.lo + β) < 2 * Real.pi := by linarith
  simp only [carrier, rotate_lo, rotate_hi, polarArc, quotientClosedInterval,
    if_neg (not_le.mpr h2), if_neg (not_le.mpr h2')]
  ext q
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(y - β : PolarAngle), ⟨y - β, ?_, rfl⟩, ?_⟩
    · constructor <;> linarith [hy.1, hy.2]
    · change (β : PolarAngle) + ((y : PolarAngle) - (β : PolarAngle)) = (y : PolarAngle)
      abel
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨β + y, ?_, ?_⟩
    · constructor <;> linarith [hy.1, hy.2]
    · change ((β + y : ℝ) : PolarAngle) = (β : PolarAngle) + (y : PolarAngle)
      exact AddCircle.coe_add (2 * Real.pi) β y

/-- Reversal transports the carrier by negation and swaps its lifted endpoints. -/
theorem reverse_carrier (A : NormalizedPolarArc) :
    A.reverse.carrier = (fun q : PolarAngle => -q) '' A.carrier := by
  have h2 : A.hi - A.lo < 2 * Real.pi := by linarith [A.short, Real.pi_pos]
  have h2' : (-A.lo) - (-A.hi) < 2 * Real.pi := by linarith
  simp only [carrier, reverse_lo, reverse_hi, polarArc, quotientClosedInterval,
    if_neg (not_le.mpr h2), if_neg (not_le.mpr h2')]
  ext q
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(-y : PolarAngle), ⟨-y, ?_, rfl⟩, ?_⟩
    · constructor <;> linarith [hy.1, hy.2]
    · simp
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨-y, ?_, ?_⟩
    · constructor <;> linarith [hy.1, hy.2]
    · simp

@[simp] theorem changeLift_span (n : ℤ) (A : NormalizedPolarArc) :
    (A.changeLift n).span = A.span := rotate_span _ _

/-- Integral full-turn lift transport preserves the actual polar-circle arc. -/
theorem changeLift_carrier (n : ℤ) (A : NormalizedPolarArc) :
    (A.changeLift n).carrier = A.carrier := by
  have h2 : A.hi - A.lo < 2 * Real.pi := by linarith [A.short, Real.pi_pos]
  have h2' :
      (A.hi + (n : ℝ) * (2 * Real.pi)) -
        (A.lo + (n : ℝ) * (2 * Real.pi)) < 2 * Real.pi := by
    linarith
  simp only [carrier, changeLift, rotate, polarArc, quotientClosedInterval,
    if_neg (not_le.mpr h2), if_neg (not_le.mpr h2')]
  ext q
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y - (n : ℝ) * (2 * Real.pi), ?_, ?_⟩
    · constructor <;> linarith [hy.1, hy.2]
    · change (↑(y - (n : ℝ) * (2 * Real.pi)) : AddCircle (2 * Real.pi)) =
        (y : AddCircle (2 * Real.pi))
      rw [AddCircle.coe_sub, ← zsmul_eq_mul, AddCircle.coe_zsmul,
        AddCircle.coe_period, smul_zero, sub_zero]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y + (n : ℝ) * (2 * Real.pi), ?_, ?_⟩
    · constructor <;> linarith [hy.1, hy.2]
    · change (↑(y + (n : ℝ) * (2 * Real.pi)) : AddCircle (2 * Real.pi)) =
        (y : AddCircle (2 * Real.pi))
      rw [AddCircle.coe_add, ← zsmul_eq_mul, AddCircle.coe_zsmul,
        AddCircle.coe_period, smul_zero, add_zero]

/-- Projection of a normalized polar arc is exactly its lifted projective
interval.  This is the set-level lift transport used below. -/
theorem project_carrier (A : NormalizedPolarArc) :
    polarToProjective '' A.carrier = directionInterval A.lo A.hi := by
  exact polarToProjective_image_polarArc (sub_nonneg.mpr A.le_endpoints) A.short

/-- Both lifted endpoints belong to the honest closed polar carrier, including
the degenerate tangent case `lo = hi`. -/
theorem endpoints_mem_carrier (A : NormalizedPolarArc) :
    (A.lo : PolarAngle) ∈ A.carrier ∧ (A.hi : PolarAngle) ∈ A.carrier := by
  have h2 : A.hi - A.lo < 2 * Real.pi := by
    linarith [A.short, Real.pi_pos]
  simp only [carrier, polarArc, quotientClosedInterval,
    if_neg (not_le.mpr h2), mem_image]
  constructor
  · exact ⟨A.lo, ⟨le_rfl, A.le_endpoints⟩, rfl⟩
  · exact ⟨A.hi, ⟨A.le_endpoints, le_rfl⟩, rfl⟩

/-- Real representatives in one half-open full-turn chart are faithful.  This is
stated independently of any bounds on a stored normalized lift. -/
theorem polar_coe_injective_on_fullChart {a x y : ℝ}
    (hx : x ∈ Ico a (a + 2 * Real.pi))
    (hy : y ∈ Ico a (a + 2 * Real.pi))
    (hxy : (x : PolarAngle) = (y : PolarAngle)) : x = y := by
  have he := congrArg (AddCircle.equivIco (2 * Real.pi) a) hxy
  rw [AddCircle.equivIco_coe_eq hx, AddCircle.equivIco_coe_eq hy] at he
  exact congrArg Subtype.val he

/-- **Common faithful chart for a contained normalized arc.**  If the quotient
carrier of `A` lies in the normalized target `[0,t]`, with `t < π`, then one
integral full-turn change of lift puts the *whole selected lift* in that same
real interval.  Moreover quotient equality with either original endpoint can
then be reflected back to literal real equality in the target chart.

No bounds on `A.lo` or `A.hi` are premises.  Thus this applies unchanged to an
arc wrapping across a conventional `0/2π` cut and to a singleton (`span = 0`). -/
theorem exists_changeLift_subset_targetChart
    (A : NormalizedPolarArc) {t : ℝ} (ht0 : 0 ≤ t) (htπ : t < Real.pi)
    (hcarrier : A.carrier ⊆ polarArc 0 t) :
    ∃ n : ℤ,
      (A.changeLift n).carrier = A.carrier ∧
      Icc (A.changeLift n).lo (A.changeLift n).hi ⊆ Icc 0 t ∧
      (∀ x : ℝ, x ∈ Icc 0 t →
        ((x : PolarAngle) = (A.lo : PolarAngle) ↔ x = (A.changeLift n).lo)) ∧
      (∀ x : ℝ, x ∈ Icc 0 t →
        ((x : PolarAngle) = (A.hi : PolarAngle) ↔ x = (A.changeLift n).hi)) := by
  have ht2π : t < 2 * Real.pi := by linarith [Real.pi_pos]
  have hloTarget := hcarrier A.endpoints_mem_carrier.1
  have hhiTarget := hcarrier A.endpoints_mem_carrier.2
  simp only [polarArc, quotientClosedInterval, sub_zero,
    if_neg (not_le.mpr ht2π)] at hloTarget hhiTarget
  rcases hloTarget with ⟨x, hx, hxcoe⟩
  rcases hhiTarget with ⟨y, hy, hycoe⟩
  have hxperiod : (x - A.lo) ∈ AddSubgroup.zmultiples (2 * Real.pi) := by
    rw [← QuotientAddGroup.eq_iff_sub_mem]
    exact hxcoe
  rw [AddSubgroup.mem_zmultiples_iff] at hxperiod
  obtain ⟨n, hn⟩ := hxperiod
  have hn' : x = A.lo + (n : ℝ) * (2 * Real.pi) := by
    rw [zsmul_eq_mul] at hn
    linarith
  have hloEq : (A.changeLift n).lo = x := by
    simp only [changeLift, rotate_lo]
    linarith
  have hshiftLo : 0 ≤ (A.changeLift n).lo := by rw [hloEq]; exact hx.1
  have hshiftHiLt : (A.changeLift n).hi < 2 * Real.pi := by
    simp only [changeLift, rotate_hi]
    linarith [A.short, hx.2]
  have hshiftHiCoe :
      ((A.changeLift n).hi : PolarAngle) = (A.hi : PolarAngle) := by
    simp only [changeLift, rotate_hi]
    rw [AddCircle.coe_add, ← zsmul_eq_mul, AddCircle.coe_zsmul,
      AddCircle.coe_period, smul_zero, add_zero]
  have hhiEq : (A.changeLift n).hi = y := by
    apply polar_coe_injective_on_fullChart (a := 0)
    · exact ⟨hshiftLo.trans (A.changeLift n).le_endpoints, by simpa using hshiftHiLt⟩
    · exact ⟨hy.1, by linarith [hy.2, ht2π]⟩
    · exact hshiftHiCoe.trans hycoe.symm
  have hsubset : Icc (A.changeLift n).lo (A.changeLift n).hi ⊆ Icc 0 t := by
    intro z hz
    rw [hloEq, hhiEq] at hz
    exact ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩
  have hloCoe : ((A.changeLift n).lo : PolarAngle) = (A.lo : PolarAngle) := by
    rw [hloEq]
    exact hxcoe
  have hhiCoe : ((A.changeLift n).hi : PolarAngle) = (A.hi : PolarAngle) :=
    hshiftHiCoe
  have target_mem_fullChart {z : ℝ} (hz : z ∈ Icc 0 t) :
      z ∈ Ico 0 (0 + 2 * Real.pi) := ⟨hz.1, by linarith [hz.2, ht2π]⟩
  refine ⟨n, A.changeLift_carrier n, hsubset, ?_, ?_⟩
  · intro z hz
    have hloMem : (A.changeLift n).lo ∈ Icc 0 t :=
      hsubset ⟨le_rfl, (A.changeLift n).le_endpoints⟩
    constructor
    · intro hzcoe
      exact polar_coe_injective_on_fullChart
        (target_mem_fullChart hz) (target_mem_fullChart hloMem)
        (hzcoe.trans hloCoe.symm)
    · rintro rfl
      exact hloCoe
  · intro z hz
    have hhiMem : (A.changeLift n).hi ∈ Icc 0 t :=
      hsubset ⟨(A.changeLift n).le_endpoints, le_rfl⟩
    constructor
    · intro hzcoe
      exact polar_coe_injective_on_fullChart
        (target_mem_fullChart hz) (target_mem_fullChart hhiMem)
        (hzcoe.trans hhiCoe.symm)
    · rintro rfl
      exact hhiCoe

end NormalizedPolarArc

/-- The polar-circle trace at a radius. -/
def polarCircleTrace (T : Set CoordinatePlane) (r : ℝ) : Set PolarAngle :=
  (fun θ : ℝ => (θ : PolarAngle)) '' trianglePolarTrace T r

/-- A normalized arc is a maximal connected arc in `trace`.  Maximality is
only among normalized connected arcs contained in the same trace; no claim is
made here that such components exist for an arbitrary triangle and radius. -/
def IsMaximalConnectedTraceArc (trace : Set PolarAngle) (A : NormalizedPolarArc) : Prop :=
  IsConnected A.carrier ∧ A.carrier ⊆ trace ∧
    ∀ B : NormalizedPolarArc, IsConnected B.carrier → B.carrier ⊆ trace →
      A.carrier ⊆ B.carrier → B.carrier ⊆ A.carrier

/-- Candidate trace arcs before deterministic length ordering.  A trace may
have only one component, represented by `componentOne = none`.  The fields say
that all present arcs are connected and maximal, pairwise disjoint, and that
their union is the complete trace. -/
structure FirstArcData (T : Set CoordinatePlane) (r : ℝ) where
  componentZero : NormalizedPolarArc
  componentOne : Option NormalizedPolarArc
  zero_component : IsMaximalConnectedTraceArc (polarCircleTrace T r) componentZero
  one_component : ∀ A, componentOne = some A →
    IsMaximalConnectedTraceArc (polarCircleTrace T r) A
  disjoint_components : Disjoint componentZero.carrier
    (componentOne.elim ∅ NormalizedPolarArc.carrier)
  union_components : componentZero.carrier ∪
    (componentOne.elim ∅ NormalizedPolarArc.carrier) = polarCircleTrace T r

namespace FirstArcData

/-- Build `FirstArcData` when the trace has one connected normalized component.
The absent component is represented by `none`, rather than by a fabricated
empty normalized arc. -/
def ofOneComponent {T : Set CoordinatePlane} {r : ℝ} (A : NormalizedPolarArc)
    (hmax : IsMaximalConnectedTraceArc (polarCircleTrace T r) A)
    (hcover : A.carrier = polarCircleTrace T r) : FirstArcData T r where
  componentZero := A
  componentOne := none
  zero_component := hmax
  one_component := by simp
  disjoint_components := by simp
  union_components := by simpa using hcover

/-- Build `FirstArcData` from exactly two normalized connected components.
All geometric work is exposed as hypotheses; in particular this constructor
cannot manufacture maximality or a missing endpoint witness. -/
def ofTwoComponents {T : Set CoordinatePlane} {r : ℝ} (A B : NormalizedPolarArc)
    (hA : IsMaximalConnectedTraceArc (polarCircleTrace T r) A)
    (hB : IsMaximalConnectedTraceArc (polarCircleTrace T r) B)
    (hdisj : Disjoint A.carrier B.carrier)
    (hcover : A.carrier ∪ B.carrier = polarCircleTrace T r) : FirstArcData T r where
  componentZero := A
  componentOne := some B
  zero_component := hA
  one_component := by
    intro C hC
    cases Option.some.inj hC
    exact hB
  disjoint_components := by simpa using hdisj
  union_components := by simpa using hcover

/-- A one-closed-arc trace automatically satisfies the maximal-component
contract.  A tangent trace (`A.lo = A.hi`) is represented by its honest
degenerate closed arc. -/
def ofOneClosedArc {T : Set CoordinatePlane} {r : ℝ} (A : NormalizedPolarArc)
    (hconn : IsConnected A.carrier)
    (hcover : A.carrier = polarCircleTrace T r) : FirstArcData T r :=
  ofOneComponent A (by
    refine ⟨hconn, hcover.subset, ?_⟩
    intro B _ hB _
    rw [← hcover] at hB
    exact hB) hcover

/-- Gap certificate for two closed trace arcs: the two no-crossing implications
needed to check maximality against every normalized connected subarc. -/
structure TwoClosedArcGap (A B : NormalizedPolarArc) : Prop where
  left : ∀ C : NormalizedPolarArc, IsConnected C.carrier →
    C.carrier ⊆ A.carrier ∪ B.carrier → A.carrier ⊆ C.carrier →
    C.carrier ⊆ A.carrier
  right : ∀ C : NormalizedPolarArc, IsConnected C.carrier →
    C.carrier ⊆ A.carrier ∪ B.carrier → B.carrier ⊆ C.carrier →
    C.carrier ⊆ B.carrier

/-- Two disjoint closed arcs with a proved gap give `FirstArcData`; the
maximal-connected-arc fields are proved here.  Equal-span ties are allowed. -/
def ofTwoClosedArcs {T : Set CoordinatePlane} {r : ℝ} (A B : NormalizedPolarArc)
    (hAconn : IsConnected A.carrier) (hBconn : IsConnected B.carrier)
    (hdisj : Disjoint A.carrier B.carrier) (hgap : TwoClosedArcGap A B)
    (hcover : A.carrier ∪ B.carrier = polarCircleTrace T r) : FirstArcData T r :=
  ofTwoComponents A B
    (by
      refine ⟨hAconn, ?_, ?_⟩
      · rw [← hcover]
        exact subset_union_left
      · intro C hCconn hC hAC
        apply hgap.left C hCconn
        · rwa [hcover]
        · exact hAC)
    (by
      refine ⟨hBconn, ?_, ?_⟩
      · rw [← hcover]
        exact subset_union_right
      · intro C hCconn hC hBC
        apply hgap.right C hCconn
        · rwa [hcover]
        · exact hBC)
    hdisj hcover

/-- The first arc is the longer present component.  Exact ties choose
`componentZero`; if there is no second component, zero is the first arc. -/
def firstArc {T : Set CoordinatePlane} {r : ℝ} (D : FirstArcData T r) : NormalizedPolarArc :=
  match D.componentOne with
  | none => D.componentZero
  | some A => if A.span ≤ D.componentZero.span then D.componentZero else A

/-- The remaining component; it is empty exactly when the trace has only one
component. -/
def secondArc {T : Set CoordinatePlane} {r : ℝ} (D : FirstArcData T r) :
    Option NormalizedPolarArc :=
  match D.componentOne with
  | none => none
  | some A => if A.span ≤ D.componentZero.span then some A else some D.componentZero

/-- The empty second arc has length zero. -/
def secondSpan {T : Set CoordinatePlane} {r : ℝ} (D : FirstArcData T r) : ℝ :=
  (D.secondArc.map NormalizedPolarArc.span).getD 0

theorem secondSpan_le_firstArc_span {T : Set CoordinatePlane} {r : ℝ} (D : FirstArcData T r) :
    D.secondSpan ≤ D.firstArc.span := by
  cases h : D.componentOne with
  | none =>
      simp [secondSpan, secondArc, firstArc, h, NormalizedPolarArc.span,
        D.componentZero.le_endpoints]
  | some A =>
      by_cases hle : A.span ≤ D.componentZero.span
      · simp [secondSpan, secondArc, firstArc, h, hle]
      · simp [secondSpan, secondArc, firstArc, h, hle, le_of_not_ge hle]

theorem firstArc_eq_componentZero_of_tie {T : Set CoordinatePlane} {r : ℝ}
    (D : FirstArcData T r) {A : NormalizedPolarArc}
    (hone : D.componentOne = some A) (htie : A.span = D.componentZero.span) :
    D.firstArc = D.componentZero := by
  simp [firstArc, hone, htie]

/-- The length-selected component is still one of the proved maximal trace
components.  This statement covers the one-component case, both strict
length-order branches, and the documented component-zero tie. -/
theorem firstArc_isMaximalConnectedTraceArc {T : Set CoordinatePlane} {r : ℝ}
    (D : FirstArcData T r) :
    IsMaximalConnectedTraceArc (polarCircleTrace T r) D.firstArc := by
  cases hone : D.componentOne with
  | none =>
      simpa [firstArc, hone] using D.zero_component
  | some A =>
      by_cases hle : A.span ≤ D.componentZero.span
      · simpa [firstArc, hone, hle] using D.zero_component
      · have hA := D.one_component A hone
        simpa [firstArc, hone, hle] using hA

/-- Consequently the selected first arc, including a winner from a genuine
two-component trace, is contained in the raw circle trace. -/
theorem firstArc_carrier_subset_trace {T : Set CoordinatePlane} {r : ℝ}
    (D : FirstArcData T r) : D.firstArc.carrier ⊆ polarCircleTrace T r :=
  D.firstArc_isMaximalConnectedTraceArc.2.1

/-- The selected lift itself is a closed interval.  This is the extrema domain
used below; unlike an endpoint-envelope hypothesis it is defined only after
length selection from the proved trace components. -/
def selectedLift {T : Set CoordinatePlane} {r : ℝ} (D : FirstArcData T r) : Set ℝ :=
  Icc D.firstArc.lo D.firstArc.hi

/-- The selected component has genuine attained least/greatest lifted
endpoints, also when it is a singleton tangent component. -/
theorem selectedLift_isLeast_isGreatest {T : Set CoordinatePlane} {r : ℝ}
    (D : FirstArcData T r) :
    IsLeast D.selectedLift D.firstArc.lo ∧
      IsGreatest D.selectedLift D.firstArc.hi := by
  exact ⟨⟨⟨le_rfl, D.firstArc.le_endpoints⟩, fun _ h => h.1⟩,
    ⟨⟨D.firstArc.le_endpoints, le_rfl⟩, fun _ h => h.2⟩⟩

/-- Exterior endpoint extrema are actual trace contacts for whichever component
wins the length comparison.  No balance identity or endpoint envelope is an
input. -/
theorem firstArc_endpoints_mem_trace {T : Set CoordinatePlane} {r : ℝ}
    (D : FirstArcData T r) :
    (D.firstArc.lo : PolarAngle) ∈ polarCircleTrace T r ∧
      (D.firstArc.hi : PolarAngle) ∈ polarCircleTrace T r := by
  exact ⟨D.firstArc_carrier_subset_trace D.firstArc.endpoints_mem_carrier.1,
    D.firstArc_carrier_subset_trace D.firstArc.endpoints_mem_carrier.2⟩

/-- Selected-component form of the common-chart theorem.  It is independent of
whether `D` records one component or two, of which component wins, and of
whether the selected span is zero.  In particular these are derived bounds on
a changed lift, not hypotheses about the lift stored in `D`. -/
theorem exists_firstArc_changeLift_endpoint_inequalities
    {T : Set CoordinatePlane} {r t : ℝ} (D : FirstArcData T r)
    (ht0 : 0 ≤ t) (htπ : t < Real.pi)
    (hcarrier : D.firstArc.carrier ⊆ polarArc 0 t) :
    ∃ n : ℤ,
      (D.firstArc.changeLift n).carrier = D.firstArc.carrier ∧
      0 ≤ (D.firstArc.changeLift n).lo ∧
      (D.firstArc.changeLift n).lo ≤ (D.firstArc.changeLift n).hi ∧
      (D.firstArc.changeLift n).hi ≤ t := by
  rcases D.firstArc.exists_changeLift_subset_targetChart ht0 htπ hcarrier with
    ⟨n, hcarrierEq, hsubset, _, _⟩
  have hlo := hsubset ⟨le_rfl, (D.firstArc.changeLift n).le_endpoints⟩
  have hhi := hsubset ⟨(D.firstArc.changeLift n).le_endpoints, le_rfl⟩
  exact ⟨n, hcarrierEq, hlo.1, (D.firstArc.changeLift n).le_endpoints, hhi.2⟩

end FirstArcData

/-- Complete case split for a trace known to have at most two closed arcs.
Unlike `FirstArcData`, this certificate can represent the genuinely empty
trace.  Tangencies are `one` with equal endpoints; two equal-span components
are retained and the downstream selector's documented tie rule applies. -/
inductive ClosedTraceDecomposition (T : Set CoordinatePlane) (r : ℝ) where
  | empty (cover : polarCircleTrace T r = ∅)
  | one (A : NormalizedPolarArc) (connected : IsConnected A.carrier)
      (cover : A.carrier = polarCircleTrace T r)
  | two (A B : NormalizedPolarArc)
      (connectedA : IsConnected A.carrier) (connectedB : IsConnected B.carrier)
      (disjoint : Disjoint A.carrier B.carrier)
      (gap : FirstArcData.TwoClosedArcGap A B)
      (cover : A.carrier ∪ B.carrier = polarCircleTrace T r)

namespace ClosedTraceDecomposition

/-- Empty traces produce no selected arc data; the one/two cases produce data
whose maximality contract was proved by the corresponding constructor. -/
def toFirstArcData? {T : Set CoordinatePlane} {r : ℝ}
    (D : ClosedTraceDecomposition T r) : Option (FirstArcData T r) :=
  match D with
  | .empty _ => none
  | .one A hconn hcover => some (FirstArcData.ofOneClosedArc A hconn hcover)
  | .two A B hA hB hd hg hc =>
      some (FirstArcData.ofTwoClosedArcs A B hA hB hd hg hc)

@[simp] theorem toFirstArcData?_empty {T : Set CoordinatePlane} {r : ℝ}
    (h : polarCircleTrace T r = ∅) :
    (ClosedTraceDecomposition.empty h).toFirstArcData? = none := rfl

end ClosedTraceDecomposition

/-- A direction-indexed needle family cut at one common radius `r`. -/
structure DirectionNeedleFamily (r : ℝ) where
  needle : (d : ProjectiveDirection) → DirectionNeedle d
  arcData : (d : ProjectiveDirection) → FirstArcData (needle d).triangle r

namespace DirectionNeedleFamily

def firstArc {r : ℝ} (F : DirectionNeedleFamily r) (d : ProjectiveDirection) :
    NormalizedPolarArc := (F.arcData d).firstArc

def secondArc {r : ℝ} (F : DirectionNeedleFamily r) (d : ProjectiveDirection) :
    Option NormalizedPolarArc := (F.arcData d).secondArc

/-- Centre of the chosen real lift of the selected first arc. -/
def firstCenter {r : ℝ} (F : DirectionNeedleFamily r) (d : ProjectiveDirection) : ℝ :=
  ((F.firstArc d).lo + (F.firstArc d).hi) / 2

/-- Half-span of the chosen real lift of the selected first arc. -/
def firstRadius {r : ℝ} (F : DirectionNeedleFamily r) (d : ProjectiveDirection) : ℝ :=
  ((F.firstArc d).hi - (F.firstArc d).lo) / 2

theorem firstRadius_nonneg {r : ℝ} (F : DirectionNeedleFamily r)
    (d : ProjectiveDirection) : 0 ≤ F.firstRadius d := by
  exact div_nonneg (sub_nonneg.mpr (F.firstArc d).le_endpoints) (by norm_num)

/-- The open quotient-centred base arc is contained in the projection of the
actual selected (closed) polar arc.  Notice the direction of the map: polar
angles modulo `2π` are sent to projective directions modulo `π`. -/
theorem quotient_firstArc_subset_projected_carrier {r : ℝ}
    (F : DirectionNeedleFamily r) (d : ProjectiveDirection) :
    quotientCenteredArc Real.pi (F.firstCenter d) (F.firstRadius d) ⊆
      polarToProjective '' (F.firstArc d).carrier := by
  rw [NormalizedPolarArc.project_carrier]
  have hspan : (F.firstArc d).hi - (F.firstArc d).lo < Real.pi :=
    (F.firstArc d).short
  rw [directionInterval, quotientClosedInterval, if_neg (not_le.mpr hspan)]
  rw [quotientCenteredArc, quotientInterval_of_lt (by
    dsimp [firstCenter, firstRadius]
    linarith)]
  apply image_mono
  dsimp [firstCenter, firstRadius]
  intro y hy
  constructor <;> linarith [hy.1, hy.2]

/-- The selected first arc is one of the recorded maximal trace components and
therefore really lies in the triangle/radius-circle trace. -/
theorem firstArc_carrier_subset_polarCircleTrace {r : ℝ}
    (F : DirectionNeedleFamily r) (d : ProjectiveDirection) :
    (F.firstArc d).carrier ⊆ polarCircleTrace (F.needle d).triangle r := by
  cases h : (F.arcData d).componentOne with
  | none =>
      simpa [firstArc, FirstArcData.firstArc, h] using
        (F.arcData d).zero_component.2.1
  | some A =>
      by_cases hle : A.span ≤ (F.arcData d).componentZero.span
      · simpa [firstArc, FirstArcData.firstArc, h, hle] using
          (F.arcData d).zero_component.2.1
      · simpa [firstArc, FirstArcData.firstArc, h, hle] using
          ((F.arcData d).one_component A h).2.1

theorem firstArc_span_ge_secondArc_span {r : ℝ} (F : DirectionNeedleFamily r)
    (d : ProjectiveDirection) :
    (F.arcData d).secondSpan ≤ (F.firstArc d).span :=
  (F.arcData d).secondSpan_le_firstArc_span

theorem firstArc_eq_componentZero_of_tie {r : ℝ} (F : DirectionNeedleFamily r)
    (d : ProjectiveDirection) {A : NormalizedPolarArc}
    (hone : (F.arcData d).componentOne = some A)
    (htie : A.span = (F.arcData d).componentZero.span) :
    F.firstArc d = (F.arcData d).componentZero :=
  (F.arcData d).firstArc_eq_componentZero_of_tie hone htie

/-- `JΓ` consists of exactly those needle directions whose selected first arc
is contained in the fixed target polar arc `Γ`. -/
def JGamma {r : ℝ} (F : DirectionNeedleFamily r) (Γ : Set PolarAngle) :
    Set ProjectiveDirection := {d | (F.firstArc d).carrier ⊆ Γ}

@[simp] theorem mem_JGamma_iff {r : ℝ} (F : DirectionNeedleFamily r)
    (Γ : Set PolarAngle) (d : ProjectiveDirection) :
    d ∈ F.JGamma Γ ↔ (F.firstArc d).carrier ⊆ Γ := Iff.rfl

/-- Lifted-coordinate form of membership in `JΓ`.  The inequalities are the
actual endpoint inequalities of the selected normalized lift; no endpoint
identity is stored in a witness. -/
theorem mem_JGamma_liftedCoordinate_iff {r : ℝ} (F : DirectionNeedleFamily r)
    (Γ : Set PolarAngle) (d : ProjectiveDirection) :
    d ∈ F.JGamma Γ ↔
      ∀ θ : ℝ, (F.firstArc d).lo ≤ θ → θ ≤ (F.firstArc d).hi →
        (θ : PolarAngle) ∈ Γ := by
  let A := F.firstArc d
  have hshort : A.hi - A.lo < 2 * Real.pi := by
    linarith [A.short, Real.pi_pos]
  change A.carrier ⊆ Γ ↔ _
  simp only [NormalizedPolarArc.carrier, polarArc, quotientClosedInterval,
    if_neg (not_le.mpr hshort)]
  constructor
  · intro h θ hlo hhi
    exact h ⟨θ, ⟨hlo, hhi⟩, rfl⟩
  · intro h q hq
    rcases hq with ⟨θ, hθ, rfl⟩
    exact h θ hθ.1 hθ.2

/-- In the one-component case, `JΓ` membership has a complete support-coordinate
inequality characterization.  This is the direct bridge from the raw triangle
trace to the direction selector. -/
theorem mem_JGamma_coordinateInequalities_iff_of_componentOne_eq_none
    {r : ℝ} (hr : 0 < r) (F : DirectionNeedleFamily r)
    (Γ : Set PolarAngle) (d : ProjectiveDirection)
    (hone : (F.arcData d).componentOne = none) :
    d ∈ F.JGamma Γ ↔
      ∀ θ : ℝ,
        (∃ lam ∈ Ioc (0 : ℝ) 1,
          r * Real.sin (θ - (F.needle d).angle) = lam * (F.needle d).height ∧
          lam * ((F.needle d).centre - 1 / 2) ≤
            r * Real.cos (θ - (F.needle d).angle) ∧
          r * Real.cos (θ - (F.needle d).angle) ≤
            lam * ((F.needle d).centre + 1 / 2)) →
        (θ : PolarAngle) ∈ Γ := by
  have hfirst : F.firstArc d = (F.arcData d).componentZero := by
    simp [firstArc, FirstArcData.firstArc, hone]
  have hcover : (F.firstArc d).carrier =
      polarCircleTrace (F.needle d).triangle r := by
    rw [hfirst]
    have hu := (F.arcData d).union_components
    simpa [hone] using hu
  rw [mem_JGamma_iff, hcover]
  constructor
  · intro h θ hcoord
    apply h
    refine ⟨θ, ?_, rfl⟩
    exact (mem_trianglePolarTrace_coordinateInequalities_iff
      (F.needle d).angle (F.needle d).height (F.needle d).centre r θ hr).2 hcoord
  · intro h q hq
    rcases hq with ⟨θ, htrace, rfl⟩
    apply h θ
    exact (mem_trianglePolarTrace_coordinateInequalities_iff
      (F.needle d).angle (F.needle d).height (F.needle d).centre r θ hr).1 htrace

/-- In the one-component regime and a fixed faithful target lift, `JΓ` is
*exactly* the pair of endpoint inequalities imposed on every angle satisfying
the real support/tangential trace inequalities.  `hchart` only fixes the lift
of the already fixed target `Γ`; it contains no assertion about extrema of the
trace. -/
theorem mem_JGamma_supportTangentialEndpoint_iff_of_componentOne_eq_none
    {r γlo γhi : ℝ} (hr : 0 < r) (F : DirectionNeedleFamily r)
    (Γ : Set PolarAngle) (d : ProjectiveDirection)
    (hone : (F.arcData d).componentOne = none)
    (hchart : ∀ θ : ℝ,
      (∃ lam ∈ Ioc (0 : ℝ) 1,
        r * Real.sin (θ - (F.needle d).angle) = lam * (F.needle d).height ∧
        lam * ((F.needle d).centre - 1 / 2) ≤
          r * Real.cos (θ - (F.needle d).angle) ∧
        r * Real.cos (θ - (F.needle d).angle) ≤
          lam * ((F.needle d).centre + 1 / 2)) →
      ((θ : PolarAngle) ∈ Γ ↔ γlo ≤ θ ∧ θ ≤ γhi)) :
    d ∈ F.JGamma Γ ↔
      ∀ θ : ℝ,
        (∃ lam ∈ Ioc (0 : ℝ) 1,
          r * Real.sin (θ - (F.needle d).angle) = lam * (F.needle d).height ∧
          lam * ((F.needle d).centre - 1 / 2) ≤
            r * Real.cos (θ - (F.needle d).angle) ∧
          r * Real.cos (θ - (F.needle d).angle) ≤
            lam * ((F.needle d).centre + 1 / 2)) →
        γlo ≤ θ ∧ θ ≤ γhi := by
  rw [mem_JGamma_coordinateInequalities_iff_of_componentOne_eq_none hr F Γ d hone]
  constructor
  · intro h θ hθ
    exact (hchart θ hθ).mp (h θ hθ)
  · intro h θ hθ
    exact (hchart θ hθ).mpr (h θ hθ)

theorem firstArc_subset_target_of_mem_JGamma {r : ℝ} {F : DirectionNeedleFamily r}
    {Γ : Set PolarAngle} {d : ProjectiveDirection} (hd : d ∈ F.JGamma Γ) :
    (F.firstArc d).carrier ⊆ Γ := hd

end DirectionNeedleFamily

/-! ## Closed real presentations on the polar quotient

This section is the quotient packaging layer.  It is intentionally independent
of the formula which produced the real closed pieces: an `Icc` presentation is
sent to its honest closed carrier in `AddCircle (2π)`, while an empty
presentation remains empty.  Thus singleton tangencies are never discarded.
-/

namespace NormalizedPolarArc

/-- A normalized closed arc is compact. -/
theorem isCompact_carrier (A : NormalizedPolarArc) : IsCompact A.carrier := by
  have h2 : A.hi - A.lo < 2 * Real.pi := by
    linarith [A.short, Real.pi_pos]
  rw [carrier, polarArc, quotientClosedInterval, if_neg (not_le.mpr h2)]
  exact isCompact_Icc.image QuotientAddGroup.continuous_mk

/-- A normalized closed arc, including a singleton, is connected. -/
theorem isConnected_carrier (A : NormalizedPolarArc) : IsConnected A.carrier := by
  have h2 : A.hi - A.lo < 2 * Real.pi := by
    linarith [A.short, Real.pi_pos]
  rw [carrier, polarArc, quotientClosedInterval, if_neg (not_le.mpr h2)]
  exact (isConnected_Icc A.le_endpoints).image _ QuotientAddGroup.continuous_mk.continuousOn

end NormalizedPolarArc

/-- Disjoint compact closed arcs automatically have the no-crossing property
needed by `FirstArcData`.  This removes the former extra `gap` obligation from
the concrete quotient packaging. -/
theorem twoClosedArcGap_of_disjoint (A B : NormalizedPolarArc)
    (hdisj : Disjoint A.carrier B.carrier) : FirstArcData.TwoClosedArcGap A B := by
  have hAc : IsClosed A.carrier := A.isCompact_carrier.isClosed
  have hBc : IsClosed B.carrier := B.isCompact_carrier.isClosed
  have hAB : A.carrier ⊆ B.carrierᶜ := Set.disjoint_left.1 hdisj
  obtain ⟨u, huopen, hAu, huB⟩ :=
    normal_exists_closure_subset hAc hBc.isOpen_compl hAB
  let v : Set PolarAngle := (closure u)ᶜ
  have hvopen : IsOpen v := isClosed_closure.isOpen_compl
  have hBv : B.carrier ⊆ v := by
    intro x hx
    intro hxu
    exact huB hxu hx
  have huv : Disjoint u v := by
    rw [Set.disjoint_left]
    intro x hxu hxv
    exact hxv (subset_closure hxu)
  have gapLeft : ∀ C : NormalizedPolarArc, IsConnected C.carrier →
      C.carrier ⊆ A.carrier ∪ B.carrier → A.carrier ⊆ C.carrier →
      C.carrier ⊆ A.carrier := by
    intro C hCconn hC hAC
    have hCuv : C.carrier ⊆ u ∪ v := hC.trans (Set.union_subset_union hAu hBv)
    have hnon : (C.carrier ∩ u).Nonempty := by
      refine ⟨(A.lo : PolarAngle), ?_, hAu A.endpoints_mem_carrier.1⟩
      exact hAC A.endpoints_mem_carrier.1
    have hCu : C.carrier ⊆ u :=
      hCconn.isPreconnected.subset_left_of_subset_union huopen hvopen huv hCuv hnon
    intro x hx
    rcases hC hx with hxA | hxB
    · exact hxA
    · exact False.elim (Set.disjoint_left.1 huv (hCu hx) (hBv hxB))
  have gapRight : ∀ C : NormalizedPolarArc, IsConnected C.carrier →
      C.carrier ⊆ A.carrier ∪ B.carrier → B.carrier ⊆ C.carrier →
      C.carrier ⊆ B.carrier := by
    intro C hCconn hC hBC
    have hCuv : C.carrier ⊆ u ∪ v := hC.trans (Set.union_subset_union hAu hBv)
    have hnon : (C.carrier ∩ v).Nonempty := by
      refine ⟨(B.lo : PolarAngle), ?_, hBv B.endpoints_mem_carrier.1⟩
      exact hBC B.endpoints_mem_carrier.1
    have hCv : C.carrier ⊆ v := by
      have := hCconn.isPreconnected.subset_left_of_subset_union
        hvopen huopen huv.symm (by simpa [union_comm] using hCuv)
        (by simpa [inter_comm] using hnon)
      exact this
    intro x hx
    rcases hC hx with hxA | hxB
    · exact False.elim (Set.disjoint_left.1 huv (hAu hxA) (hCv hx))
    · exact hxB
  exact ⟨gapLeft, gapRight⟩

/-- Empty or one closed polar arc obtained from a real `Icc` presentation. -/
structure ClosedPolarPresentation (s : Set ℝ) where
  arc : Option NormalizedPolarArc
  carrier : Set PolarAngle
  carrier_eq : carrier = (fun θ : ℝ => (θ : PolarAngle)) '' s
  carrier_of_none : arc = none → carrier = ∅
  carrier_of_some : ∀ A, arc = some A → carrier = A.carrier

/-- Map an empty/closed-interval presentation into `AddCircle (2π)`.  The
strict-span premise is only consulted in the interval branch. -/
noncomputable def ClosedIccPresentation.toClosedPolarPresentation
    {s : Set ℝ} (P : ClosedIccPresentation s)
    (hshort : ∀ lo hi, s = Icc lo hi → hi - lo < Real.pi) :
    ClosedPolarPresentation s := by
  cases P with
  | empty h =>
      refine ⟨none, ∅, ?_, ?_, ?_⟩
      · rw [h]
        simp
      · intro
        rfl
      · simp
  | interval lo hi hle h =>
      let A : NormalizedPolarArc :=
        { lo := lo, hi := hi, le_endpoints := hle, short := hshort lo hi h }
      refine ⟨some A, A.carrier, ?_, ?_, ?_⟩
      · have h2 : hi - lo < 2 * Real.pi := by
          linarith [hshort lo hi h, Real.pi_pos]
        rw [h, NormalizedPolarArc.carrier, polarArc, quotientClosedInterval,
          if_neg (not_le.mpr h2)]
      · simp
      · intro B hB
        cases Option.some.inj hB
        rfl

/-- Uniform empty/one/two quotient decomposition.  Exact carrier coverage and
pairwise disjointness are the only set-theoretic inputs; connectedness,
no-crossing, maximality, singleton tangencies, and tie handling are discharged
by the package. -/
noncomputable def closedTraceDecompositionOfPolarPresentations
    {T : Set CoordinatePlane} {r : ℝ} {s t : Set ℝ}
    (P : ClosedPolarPresentation s) (Q : ClosedPolarPresentation t)
    (hcover : P.carrier ∪ Q.carrier = polarCircleTrace T r)
    (hdisj : Disjoint P.carrier Q.carrier) : ClosedTraceDecomposition T r := by
  cases hP : P.arc with
  | none =>
      have hPe : P.carrier = ∅ := P.carrier_of_none hP
      cases hQ : Q.arc with
      | none =>
          exact .empty (by
            have hQe : Q.carrier = ∅ := Q.carrier_of_none hQ
            simpa [hPe, hQe] using hcover.symm)
      | some B =>
          have hQB : Q.carrier = B.carrier := Q.carrier_of_some B hQ
          exact .one B B.isConnected_carrier (by simpa [hPe, hQB] using hcover)
  | some A =>
      have hPA : P.carrier = A.carrier := P.carrier_of_some A hP
      cases hQ : Q.arc with
      | none =>
          have hQe : Q.carrier = ∅ := Q.carrier_of_none hQ
          exact .one A A.isConnected_carrier (by simpa [hPA, hQe] using hcover)
      | some B =>
          have hQB : Q.carrier = B.carrier := Q.carrier_of_some B hQ
          have hdAB : Disjoint A.carrier B.carrier := by simpa [hPA, hQB] using hdisj
          exact .two A B A.isConnected_carrier B.isConnected_carrier hdAB
            (twoClosedArcGap_of_disjoint A B hdAB) (by simpa [hPA, hQB] using hcover)

/-- One-presentation specialization, used when the two principal pieces meet
at height one and have already been merged. -/
noncomputable def closedTraceDecompositionOfPolarPresentation
    {T : Set CoordinatePlane} {r : ℝ} {s : Set ℝ}
    (P : ClosedPolarPresentation s)
    (hcover : P.carrier = polarCircleTrace T r) : ClosedTraceDecomposition T r := by
  cases hA : P.arc with
  | none => exact .empty (by rw [← hcover, P.carrier_of_none hA])
  | some A =>
      exact .one A A.isConnected_carrier (by
        rw [← hcover, P.carrier_of_some A hA])

/-- The selected arc of the one-presentation packager is literally its optional
presented arc. -/
theorem closedTraceDecompositionOfPolarPresentation_firstArc
    {T : Set CoordinatePlane} {r : ℝ} {s : Set ℝ}
    (P : ClosedPolarPresentation s)
    (hcover : P.carrier = polarCircleTrace T r) :
    (closedTraceDecompositionOfPolarPresentation P hcover).toFirstArcData?.map
        FirstArcData.firstArc = P.arc := by
  rcases P with ⟨PArc, PCarrier, PCarrierEq, PNone, PSome⟩
  cases PArc <;>
    simp [closedTraceDecompositionOfPolarPresentation,
      ClosedTraceDecomposition.toFirstArcData?, FirstArcData.firstArc,
      FirstArcData.ofOneClosedArc, FirstArcData.ofOneComponent]

/-- The corresponding genuine `FirstArcData`, absent exactly for an empty
trace.  In the two-component case the established selector keeps both arcs and
chooses the longer one, with `componentZero` winning a tie. -/
noncomputable def firstArcDataOfPolarPresentations?
    {T : Set CoordinatePlane} {r : ℝ} {s t : Set ℝ}
    (P : ClosedPolarPresentation s) (Q : ClosedPolarPresentation t)
    (hcover : P.carrier ∪ Q.carrier = polarCircleTrace T r)
    (hdisj : Disjoint P.carrier Q.carrier) : Option (FirstArcData T r) :=
  (closedTraceDecompositionOfPolarPresentations P Q hcover hdisj).toFirstArcData?

/-- When both concrete presentations are present, the packager records them in
principal order: component zero is the left presentation and component one is
the right presentation. -/
theorem closedTraceDecompositionOfPolarPresentations_components_of_some
    {T : Set CoordinatePlane} {r : ℝ} {s t : Set ℝ}
    (P : ClosedPolarPresentation s) (Q : ClosedPolarPresentation t)
    (hcover : P.carrier ∪ Q.carrier = polarCircleTrace T r)
    (hdisj : Disjoint P.carrier Q.carrier)
    {L R : NormalizedPolarArc} (hL : P.arc = some L) (hR : Q.arc = some R) :
    ∃ D, (closedTraceDecompositionOfPolarPresentations P Q hcover hdisj).toFirstArcData? =
        some D ∧ D.componentZero = L ∧ D.componentOne = some R := by
  rcases P with ⟨PArc, PCarrier, PCarrierEq, PNone, PSome⟩
  rcases Q with ⟨QArc, QCarrier, QCarrierEq, QNone, QSome⟩
  simp only at hL hR
  subst PArc
  subst QArc
  refine ⟨_, rfl, rfl, rfl⟩

/-- Complete winner/tie split for the actual two-presentation ordering.  A
strictly longer right component wins; otherwise (including equality) the left
component-zero presentation wins. -/
theorem closedTraceDecompositionOfPolarPresentations_firstArc_cases_of_some
    {T : Set CoordinatePlane} {r : ℝ} {s t : Set ℝ}
    (P : ClosedPolarPresentation s) (Q : ClosedPolarPresentation t)
    (hcover : P.carrier ∪ Q.carrier = polarCircleTrace T r)
    (hdisj : Disjoint P.carrier Q.carrier)
    {L R : NormalizedPolarArc} (hL : P.arc = some L) (hR : Q.arc = some R) :
    ((R.span ≤ L.span ∧
        (closedTraceDecompositionOfPolarPresentations P Q hcover hdisj).toFirstArcData?.map
          FirstArcData.firstArc = some L) ∨
      (L.span < R.span ∧
        (closedTraceDecompositionOfPolarPresentations P Q hcover hdisj).toFirstArcData?.map
          FirstArcData.firstArc = some R)) := by
  obtain ⟨D, hD, hzero, hone⟩ :=
    closedTraceDecompositionOfPolarPresentations_components_of_some
      P Q hcover hdisj hL hR
  rw [hD]
  simp only [Option.map_some, Option.some.injEq]
  by_cases hle : R.span ≤ L.span
  · left
    refine ⟨hle, ?_⟩
    simp [FirstArcData.firstArc, hone, hzero, hle]
  · right
    refine ⟨lt_of_not_ge hle, ?_⟩
    simp [FirstArcData.firstArc, hone, hzero, hle]

/-- The selected arc computed from two optional presented components.  This
proof-free normal form is useful when comparing presentations in two rotated
charts: coverage, connectedness and gap certificates are propositions and do
not affect the deterministic length selector. -/
def selectedArcOfOptions? (A B : Option NormalizedPolarArc) :
    Option NormalizedPolarArc :=
  match A, B with
  | none, none => none
  | some A, none => some A
  | none, some B => some B
  | some A, some B => some (if B.span ≤ A.span then A else B)

/-- The proof-free selector commutes exactly with a common angular rotation.
Spans, winner order and the component-zero tie rule are therefore all
preserved; no continuity argument is involved. -/
theorem selectedArcOfOptions?_rotate (β : ℝ)
    (A B : Option NormalizedPolarArc) :
    selectedArcOfOptions? (A.map (NormalizedPolarArc.rotate β))
        (B.map (NormalizedPolarArc.rotate β)) =
      (selectedArcOfOptions? A B).map (NormalizedPolarArc.rotate β) := by
  cases A with
  | none => cases B <;> rfl
  | some A =>
      cases B with
      | none => rfl
      | some B =>
          simp only [Option.map_some, selectedArcOfOptions?,
            NormalizedPolarArc.rotate_span]
          by_cases h : B.span ≤ A.span <;> simp [h]

/-- Erasing the proof fields of the presentation packager leaves exactly the
proof-free optional-arc selector.  This is the bridge which lets covariance of
the concrete presentations pass through `FirstArcData`. -/
theorem closedTraceDecomposition_firstArc_eq_selectedArcOfOptions
    {T : Set CoordinatePlane} {r : ℝ} {s t : Set ℝ}
    (P : ClosedPolarPresentation s) (Q : ClosedPolarPresentation t)
    (hcover : P.carrier ∪ Q.carrier = polarCircleTrace T r)
    (hdisj : Disjoint P.carrier Q.carrier) :
    (closedTraceDecompositionOfPolarPresentations P Q hcover hdisj).toFirstArcData?.map
        FirstArcData.firstArc = selectedArcOfOptions? P.arc Q.arc := by
  rcases P with ⟨PArc, PCarrier, PCarrierEq, PNone, PSome⟩
  rcases Q with ⟨QArc, QCarrier, QCarrierEq, QNone, QSome⟩
  cases PArc <;> cases QArc <;>
    simp [closedTraceDecompositionOfPolarPresentations,
      ClosedTraceDecomposition.toFirstArcData?, FirstArcData.firstArc,
      FirstArcData.ofOneClosedArc, FirstArcData.ofOneComponent,
      FirstArcData.ofTwoClosedArcs, FirstArcData.ofTwoComponents,
      selectedArcOfOptions?]

/-- Real translation of a chart piece. -/
def shiftRealSet (α : ℝ) (s : Set ℝ) : Set ℝ := {θ | θ - α ∈ s}

/-- Real polar points depend only on the class modulo a full turn.  Keeping this
as a separate lemma makes the subsequent passage from an arbitrary raw lift to
the canonical positive-half-period lift explicit. -/
theorem polarPoint_eq_of_polar_coe_eq {r θ φ : ℝ}
    (h : (θ : PolarAngle) = (φ : PolarAngle)) : polarPoint r θ = polarPoint r φ := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff] at h
  obtain ⟨n, hn⟩ := h
  have hθ : θ = φ + (n : ℝ) * (2 * Real.pi) := by
    rw [zsmul_eq_mul] at hn
    linarith
  ext <;>
    simp [polarPoint, scaleCoordinatePlane, unitDirection, hθ,
      Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- The raw real trace is invariant under changing the full-turn lift. -/
theorem trianglePolarTrace_iff_of_polar_coe_eq {T : Set CoordinatePlane} {r θ φ : ℝ}
    (h : (θ : PolarAngle) = (φ : PolarAngle)) :
    θ ∈ trianglePolarTrace T r ↔ φ ∈ trianglePolarTrace T r := by
  change polarPoint r θ ∈ T ↔ polarPoint r φ ∈ T
  rw [polarPoint_eq_of_polar_coe_eq h]

/-- Shifting the chosen chart by an integral full turn does not change the
quotient carrier of any real set. -/
theorem shiftedPolarImage_add_fullTurn (s : Set ℝ) (α : ℝ) (n : ℤ) :
    (fun θ : ℝ => (θ : PolarAngle)) ''
        shiftRealSet (α + (n : ℝ) * (2 * Real.pi)) s =
      (fun θ : ℝ => (θ : PolarAngle)) '' shiftRealSet α s := by
  ext q
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨θ - (n : ℝ) * (2 * Real.pi), ?_, ?_⟩
    · change θ - (n : ℝ) * (2 * Real.pi) - α ∈ s
      change θ - (α + (n : ℝ) * (2 * Real.pi)) ∈ s at hθ
      convert hθ using 1 <;> ring
    · change (↑(θ - (n : ℝ) * (2 * Real.pi)) : PolarAngle) = (θ : PolarAngle)
      rw [AddCircle.coe_sub, ← zsmul_eq_mul, AddCircle.coe_zsmul,
        AddCircle.coe_period, smul_zero, sub_zero]
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨θ + (n : ℝ) * (2 * Real.pi), ?_, ?_⟩
    · change θ + (n : ℝ) * (2 * Real.pi) -
        (α + (n : ℝ) * (2 * Real.pi)) ∈ s
      simpa only [add_sub_add_right_eq_sub] using hθ
    · change (↑(θ + (n : ℝ) * (2 * Real.pi)) : PolarAngle) = (θ : PolarAngle)
      rw [AddCircle.coe_add, ← zsmul_eq_mul, AddCircle.coe_zsmul,
        AddCircle.coe_period, smul_zero, add_zero]

/-- Every quotient trace point of a positive-height support triangle has a raw
representative in the positive half-period chart. -/
theorem polarCircleTrace_supportNeedleTriangle_eq_positiveChart_image
    {α δ c r : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    polarCircleTrace (supportNeedleTriangle α δ c) r =
      (fun θ : ℝ => (θ : PolarAngle)) ''
        (trianglePolarTrace (supportNeedleTriangle α δ c) r ∩ Icc α (α + Real.pi)) := by
  apply Set.Subset.antisymm
  · rintro q ⟨θ, hθ, rfl⟩
    let e := AddCircle.equivIco (2 * Real.pi) α
    let φ : ℝ := (e (θ : PolarAngle)).1
    have hφI : φ ∈ Ico α (α + 2 * Real.pi) := (e (θ : PolarAngle)).2
    have hcoe : (φ : PolarAngle) = (θ : PolarAngle) := by
      apply e.injective
      rw [AddCircle.equivIco_coe_eq hφI]
    have hφtrace : φ ∈ trianglePolarTrace (supportNeedleTriangle α δ c) r :=
      (trianglePolarTrace_iff_of_polar_coe_eq hcoe).2 hθ
    rcases (mem_trianglePolarTrace_coordinateInequalities_iff α δ c r φ hr).1 hφtrace with
      ⟨lam, hlam, hn, _, _⟩
    have hp : 0 < r * Real.sin (φ - α) := by
      rw [hn]
      exact mul_pos hlam.1 hδ
    have hspos : 0 < Real.sin (φ - α) := by
      rcases (mul_pos_iff.mp hp) with h | h
      · exact h.2
      · exact False.elim (not_lt_of_ge hr.le h.1)
    have hφlt : φ - α < Real.pi := by
      by_contra hnot
      have hpi : Real.pi ≤ φ - α := le_of_not_gt hnot
      have h0 : 0 ≤ φ - α - Real.pi := by linarith
      have hle : φ - α - Real.pi ≤ Real.pi := by linarith [hφI.2]
      have hsnonneg := Real.sin_nonneg_of_nonneg_of_le_pi h0 hle
      rw [Real.sin_sub_pi] at hsnonneg
      linarith
    exact ⟨φ, ⟨hφtrace, ⟨by linarith [hφI.1], by linarith⟩⟩, hcoe⟩
  · rintro q ⟨θ, ⟨hθ, _⟩, rfl⟩
    exact ⟨θ, hθ, rfl⟩

/-- The quotient map is injective on any closed interval of width `π` inside a
`2π` fundamental chart.  This is the wrapped/lift fact used to separate the
left and right trace pieces. -/
theorem polar_coe_injective_on_halfChart {α x y : ℝ}
    (hx : x ∈ Icc α (α + Real.pi)) (hy : y ∈ Icc α (α + Real.pi))
    (hxy : (x : PolarAngle) = (y : PolarAngle)) : x = y := by
  have hxI : x ∈ Ico α (α + 2 * Real.pi) :=
    ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hyI : y ∈ Ico α (α + 2 * Real.pi) :=
    ⟨hy.1, by linarith [hy.2, Real.pi_pos]⟩
  have he := congrArg (AddCircle.equivIco (2 * Real.pi) α) hxy
  rw [AddCircle.equivIco_coe_eq hxI, AddCircle.equivIco_coe_eq hyI] at he
  exact congrArg Subtype.val he

/-- Shift a real `empty`/`Icc` presentation before quotienting.  Full-turn
changes of `α` therefore alter only the chosen lift, not the carrier. -/
noncomputable def ClosedIccPresentation.toShiftedClosedPolarPresentation
    {s : Set ℝ} (P : ClosedIccPresentation s) (α : ℝ)
    (hshort : ∀ lo hi, s = Icc lo hi → hi - lo < Real.pi) :
    ClosedPolarPresentation (shiftRealSet α s) := by
  cases P with
  | empty h =>
      refine ⟨none, ∅, ?_, ?_, ?_⟩
      · ext q
        simp [shiftRealSet, h]
      · intro
        rfl
      · simp
  | interval lo hi hle h =>
      let A : NormalizedPolarArc :=
        { lo := α + lo, hi := α + hi, le_endpoints := by linarith,
          short := by simpa only [add_sub_add_left_eq_sub] using hshort lo hi h }
      refine ⟨some A, A.carrier, ?_, ?_, ?_⟩
      · have h2 : (α + hi) - (α + lo) < 2 * Real.pi := by
          linarith [hshort lo hi h, Real.pi_pos]
        rw [NormalizedPolarArc.carrier, polarArc, quotientClosedInterval,
          if_neg (not_le.mpr h2)]
        ext q
        constructor
        · rintro ⟨θ, hθ, rfl⟩
          refine ⟨θ, ?_, rfl⟩
          change θ - α ∈ s
          rw [h]
          constructor <;> linarith [hθ.1, hθ.2]
        · rintro ⟨θ, hθ, rfl⟩
          refine ⟨θ, ?_, rfl⟩
          change θ - α ∈ s at hθ
          rw [h] at hθ
          constructor <;> linarith [hθ.1, hθ.2]
      · simp
      · intro B hB
        cases Option.some.inj hB
        rfl

/-- Shifting the chart angle rotates every presented component literally. -/
theorem ClosedIccPresentation.toShiftedClosedPolarPresentation_arc_add
    {s : Set ℝ} (P : ClosedIccPresentation s) (α β : ℝ)
    (hshort : ∀ lo hi, s = Icc lo hi → hi - lo < Real.pi) :
    (P.toShiftedClosedPolarPresentation (α + β) hshort).arc =
      (P.toShiftedClosedPolarPresentation α hshort).arc.map
        (NormalizedPolarArc.rotate β) := by
  cases P with
  | empty h => rfl
  | interval lo hi hle h =>
      simp only [ClosedIccPresentation.toShiftedClosedPolarPresentation,
        Option.map_some, Option.some.injEq]
      rw [NormalizedPolarArc.mk.injEq]
      simp only [NormalizedPolarArc.rotate_lo, NormalizedPolarArc.rotate_hi]
      constructor <;> ring

/-- Strict left/right half pieces remain disjoint after quotienting.  The proof
uses one faithful `2π` chart, so it also covers pieces which wrap across a
different conventional cut. -/
theorem disjoint_shifted_halfPieces_on_polarCircle
    {α : ℝ} {s t : Set ℝ}
    (hs : ∀ x ∈ s, 0 ≤ x ∧ x < Real.pi / 2)
    (ht : ∀ x ∈ t, Real.pi / 2 < x ∧ x ≤ Real.pi) :
    Disjoint ((fun θ : ℝ => (θ : PolarAngle)) '' shiftRealSet α s)
      ((fun θ : ℝ => (θ : PolarAngle)) '' shiftRealSet α t) := by
  rw [Set.disjoint_left]
  rintro q ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  have hxs := hs (x - α) hx
  have hyt := ht (y - α) hy
  have hxchart : x ∈ Icc α (α + Real.pi) := by constructor <;> linarith
  have hychart : y ∈ Icc α (α + Real.pi) := by constructor <;> linarith
  have heq : x = y := polar_coe_injective_on_halfChart hxchart hychart hxy.symm
  linarith

/-- The two strict-small-radius closed pieces are pairwise disjoint on the
polar circle, including empty and singleton branches. -/
theorem disjoint_principalTraceClosedPresentations
    {α δ a b k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (P : ClosedPolarPresentation (shiftRealSet α (principalTraceLeftPiece δ a b k)))
    (Q : ClosedPolarPresentation (shiftRealSet α (principalTraceRightPiece δ a b k))) :
    Disjoint P.carrier Q.carrier := by
  rw [P.carrier_eq, Q.carrier_eq]
  apply disjoint_shifted_halfPieces_on_polarCircle
  · intro x hx
    have ha : Real.arcsin k < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hk1
    rcases hx with ⟨hxI, _⟩
    constructor
    · exact hxI.1
    · exact hxI.2.trans_lt ha
  · intro x hx
    have ha : Real.arcsin k < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hk1
    rcases hx with ⟨hxI, _⟩
    constructor
    · linarith [hxI.1]
    · exact hxI.2

/-- Any closed-interval presentation of the left strict piece has span `< π`. -/
theorem principalTraceLeftPiece_icc_span_lt
    {δ a b k lo hi : ℝ} (hk1 : k < 1)
    (h : principalTraceLeftPiece δ a b k = Icc lo hi) : hi - lo < Real.pi := by
  by_cases hle : lo ≤ hi
  · have hlo : lo ∈ principalTraceLeftPiece δ a b k := h.symm ▸ ⟨le_rfl, hle⟩
    have hhi : hi ∈ principalTraceLeftPiece δ a b k := h.symm ▸ ⟨hle, le_rfl⟩
    have ha : Real.arcsin k < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hk1
    rcases hlo with ⟨hloI, _⟩
    rcases hhi with ⟨hhiI, _⟩
    linarith [hloI.1, hloI.2, hhiI.1, hhiI.2, Real.pi_pos]
  · linarith [Real.pi_pos]

/-- Any closed-interval presentation of the right strict piece has span `< π`. -/
theorem principalTraceRightPiece_icc_span_lt
    {δ a b k lo hi : ℝ} (hk1 : k < 1)
    (h : principalTraceRightPiece δ a b k = Icc lo hi) : hi - lo < Real.pi := by
  by_cases hle : lo ≤ hi
  · have hlo : lo ∈ principalTraceRightPiece δ a b k := h.symm ▸ ⟨le_rfl, hle⟩
    have hhi : hi ∈ principalTraceRightPiece δ a b k := h.symm ▸ ⟨hle, le_rfl⟩
    have ha : Real.arcsin k < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hk1
    rcases hlo with ⟨hloI, _⟩
    rcases hhi with ⟨hhiI, _⟩
    linarith [hloI.1, hloI.2, hhiI.1, hhiI.2, Real.pi_pos]
  · linarith [Real.pi_pos]

/-- The actual shifted quotient presentations produced by the strict-radius
left/right compact order-connected pieces. -/
noncomputable def principalTraceShiftedClosedPolarPresentations
    {δ a b k : ℝ} (α : ℝ) (hδ : 0 < δ) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    ClosedPolarPresentation (shiftRealSet α (principalTraceLeftPiece δ a b k)) ×
      ClosedPolarPresentation (shiftRealSet α (principalTraceRightPiece δ a b k)) :=
  let P := principalTraceClosedPresentations hδ hk0 hk1
  ⟨P.1.toShiftedClosedPolarPresentation α
      (fun lo hi h => principalTraceLeftPiece_icc_span_lt hk1 h),
    P.2.toShiftedClosedPolarPresentation α
      (fun lo hi h => principalTraceRightPiece_icc_span_lt hk1 h)⟩

/-- The two closed height pieces are exactly the principal window. -/
theorem principalTraceLeftPiece_union_rightPiece
    {δ a b k : ℝ} (hδ : 0 < δ) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    principalTraceLeftPiece δ a b k ∪ principalTraceRightPiece δ a b k =
      principalTraceWindow δ a b k := by
  rw [← principalTraceWindow_left_eq_closedPiece hδ hk0 hk1,
    ← principalTraceWindow_right_eq_closedPiece hδ hk0 hk1]
  ext φ
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h
    rcases le_total φ (Real.pi / 2) with hl | hr
    · exact Or.inl ⟨h, hl⟩
    · exact Or.inr ⟨h, hr⟩

/-- For an actual support-needle triangle, raw-trace periodicity and the exact
positive-chart iff discharge quotient coverage automatically. -/
theorem principalTraceShiftedClosedPolarPresentations_cover
    {α δ c r : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hδr : δ < r) :
    (principalTraceShiftedClosedPolarPresentations (a := c - 1 / 2)
        (b := c + 1 / 2) α hδ (div_nonneg hδ.le hr.le) ((div_lt_one hr).2 hδr)).1.carrier ∪
      (principalTraceShiftedClosedPolarPresentations (a := c - 1 / 2)
        (b := c + 1 / 2) α hδ (div_nonneg hδ.le hr.le) ((div_lt_one hr).2 hδr)).2.carrier =
        polarCircleTrace (supportNeedleTriangle α δ c) r := by
  let hk0 : 0 ≤ δ / r := div_nonneg hδ.le hr.le
  let hk1 : δ / r < 1 := (div_lt_one hr).2 hδr
  let P := principalTraceShiftedClosedPolarPresentations (a := c - 1 / 2)
    (b := c + 1 / 2) α hδ hk0 hk1
  change P.1.carrier ∪ P.2.carrier = _
  rw [P.1.carrier_eq, P.2.carrier_eq, ← Set.image_union]
  have hshift :
      shiftRealSet α (principalTraceLeftPiece δ (c - 1 / 2) (c + 1 / 2) (δ / r)) ∪
        shiftRealSet α (principalTraceRightPiece δ (c - 1 / 2) (c + 1 / 2) (δ / r)) =
      shiftRealSet α
        (principalTraceLeftPiece δ (c - 1 / 2) (c + 1 / 2) (δ / r) ∪
          principalTraceRightPiece δ (c - 1 / 2) (c + 1 / 2) (δ / r)) := by
    ext θ
    rfl
  rw [hshift, principalTraceLeftPiece_union_rightPiece hδ hk0 hk1]
  rw [polarCircleTrace_supportNeedleTriangle_eq_positiveChart_image hr hδ,
    trianglePolarTrace_inter_positiveChart_eq_shift_principalTraceWindow hr hδ hδr]
  rfl

/-- At height one the strict-radius left/right disjointness statement is false:
for the centred needle the two closed pieces both contain `π/2`.  Thus the
`δ = r` API must merge touching halves into one component rather than feed them
to the disjoint two-presentation packager. -/
theorem heightOne_principalTracePieces_touch_counterexample :
    Real.pi / 2 ∈
      principalTraceLeftPiece 1 (-1 / 2) (1 / 2) 1 ∩
        principalTraceRightPiece 1 (-1 / 2) (1 / 2) 1 := by
  have hp : 0 < Real.pi := Real.pi_pos
  constructor
  · refine ⟨⟨by linarith, ?_⟩, ?_, ?_⟩
    · simp
    · norm_num
    · norm_num
  · refine ⟨⟨?_, by linarith⟩, ?_, ?_⟩
    · simp
    · norm_num
    · norm_num

/-! ### The two boundary heights -/

/-- A normalized singleton polar arc. -/
def singletonPolarArc (x : ℝ) : NormalizedPolarArc where
  lo := x
  hi := x
  le_endpoints := le_rfl
  short := by linarith [Real.pi_pos]

@[simp] theorem singletonPolarArc_carrier (x : ℝ) :
    (singletonPolarArc x).carrier = {(x : PolarAngle)} := by
  have h2 : ¬2 * Real.pi ≤ (0 : ℝ) := by linarith [Real.pi_pos]
  simp [singletonPolarArc, NormalizedPolarArc.carrier, polarArc,
    quotientClosedInterval, h2]

/-- At zero height every quotient trace point is one of the two radial classes,
and each class occurs exactly when the corresponding actual segment endpoint
reaches the circle. -/
theorem mem_polarCircleTrace_zeroHeight_iff
    {α c r : ℝ} (hr : 0 < r) (q : PolarAngle) :
    q ∈ polarCircleTrace (supportNeedleTriangle α 0 c) r ↔
      (q = (α : PolarAngle) ∧ r ≤ c + 1 / 2) ∨
        (q = ((α + Real.pi : ℝ) : PolarAngle) ∧ r ≤ 1 / 2 - c) := by
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    rcases (mem_trianglePolarTrace_coordinateInequalities_iff α 0 c r θ hr).1 hθ with
      ⟨lam, hlam, hn, _, _⟩
    have hs : Real.sin (θ - α) = 0 := by nlinarith
    rcases Real.sin_eq_zero_iff.mp hs with ⟨n, hnπ⟩
    rcases Int.even_or_odd' n with ⟨k, hk | hk⟩
    · have hcoe : (θ : PolarAngle) = (α : PolarAngle) := by
        have hθeq : θ = α + (k : ℝ) * (2 * Real.pi) := by
          rw [hk] at hnπ
          push_cast at hnπ
          linarith
        rw [hθeq, AddCircle.coe_add, ← zsmul_eq_mul, AddCircle.coe_zsmul,
          AddCircle.coe_period, smul_zero, add_zero]
      left
      refine ⟨hcoe, ?_⟩
      have hα : α ∈ trianglePolarTrace (supportNeedleTriangle α 0 c) r :=
        (trianglePolarTrace_iff_of_polar_coe_eq hcoe).1 hθ
      rcases (mem_trianglePolarTrace_zeroHeight_iff hr (by simp)
        (by linarith [Real.pi_pos])).1 hα with h | h
      · exact h.2
      · linarith [h.1, Real.pi_pos]
    · have hcoe : (θ : PolarAngle) = ((α + Real.pi : ℝ) : PolarAngle) := by
        have hθeq : θ = α + Real.pi + (k : ℝ) * (2 * Real.pi) := by
          rw [hk] at hnπ
          push_cast at hnπ
          linarith
        rw [hθeq, AddCircle.coe_add, AddCircle.coe_add, ← zsmul_eq_mul,
          AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, add_zero]
      right
      refine ⟨hcoe, ?_⟩
      have hα : α + Real.pi ∈ trianglePolarTrace (supportNeedleTriangle α 0 c) r :=
        (trianglePolarTrace_iff_of_polar_coe_eq hcoe).1 hθ
      rcases (mem_trianglePolarTrace_zeroHeight_iff hr
        (by linarith [Real.pi_pos]) (by ring_nf; exact le_rfl)).1 hα with h | h
      · linarith [h.1, Real.pi_pos]
      · exact h.2
  · rintro (⟨rfl, hplus⟩ | ⟨rfl, hminus⟩)
    · exact ⟨α, (mem_trianglePolarTrace_zeroHeight_iff hr (by simp)
        (by linarith [Real.pi_pos])).2 (Or.inl ⟨rfl, hplus⟩), rfl⟩
    · exact ⟨α + Real.pi, (mem_trianglePolarTrace_zeroHeight_iff hr
        (by linarith [Real.pi_pos]) (by ring_nf; exact le_rfl)).2
          (Or.inr ⟨rfl, hminus⟩), rfl⟩

/-- Complete zero-height quotient decomposition: empty, either radial singleton,
or the two antipodal singleton contacts. -/
noncomputable def zeroHeightTraceClosedDecomposition
    {r α c : ℝ} (hr : 0 < r) :
    ClosedTraceDecomposition (supportNeedleTriangle α 0 c) r := by
  let A := singletonPolarArc α
  let B := singletonPolarArc (α + Real.pi)
  by_cases hp : r ≤ c + 1 / 2
  · by_cases hm : r ≤ 1 / 2 - c
    · have hd : Disjoint A.carrier B.carrier := by
        rw [Set.disjoint_left]
        intro q hA hB
        rw [show A.carrier = {(α : PolarAngle)} by simp [A]] at hA
        rw [show B.carrier = {((α + Real.pi : ℝ) : PolarAngle)} by simp [B]] at hB
        simp only [Set.mem_singleton_iff] at hA hB
        have h : (α : PolarAngle) = ((α + Real.pi : ℝ) : PolarAngle) := hA.symm.trans hB
        have heq := polar_coe_injective_on_halfChart
          (show α ∈ Icc α (α + Real.pi) from ⟨le_rfl, by linarith [Real.pi_pos]⟩)
          (show α + Real.pi ∈ Icc α (α + Real.pi) from
            ⟨by linarith [Real.pi_pos], le_rfl⟩) h
        exact Real.pi_pos.ne' (by linarith [heq])
      exact .two A B A.isConnected_carrier B.isConnected_carrier hd
        (twoClosedArcGap_of_disjoint A B hd) (by
          ext q
          rw [mem_polarCircleTrace_zeroHeight_iff hr q]
          constructor
          · intro h
            rcases h with h | h
            · exact Or.inl ⟨by simpa [A] using h, hp⟩
            · exact Or.inr ⟨by simpa [B] using h, hm⟩
          · rintro (⟨h, _⟩ | ⟨h, _⟩)
            · exact Or.inl (by simpa [A] using h)
            · exact Or.inr (by simpa [B] using h))
    · exact .one A A.isConnected_carrier (by
        ext q
        rw [mem_polarCircleTrace_zeroHeight_iff hr q]
        constructor
        · intro h; exact Or.inl ⟨by simpa [A] using h, hp⟩
        · rintro (⟨h, _⟩ | ⟨_, h⟩)
          · simpa [A] using h
          · exact False.elim (hm h))
  · by_cases hm : r ≤ 1 / 2 - c
    · exact .one B B.isConnected_carrier (by
        ext q
        rw [mem_polarCircleTrace_zeroHeight_iff hr q]
        constructor
        · intro h; exact Or.inr ⟨by simpa [B] using h, hm⟩
        · rintro (⟨_, h⟩ | ⟨h, _⟩)
          · exact False.elim (hp h)
          · simpa [B] using h)
    · exact .empty (by
        ext q
        rw [mem_polarCircleTrace_zeroHeight_iff hr q]
        constructor
        · rintro (⟨_, h⟩ | ⟨_, h⟩)
          · exact hp h
          · exact hm h
        · intro h; exact False.elim h)

/-- The height-one trace is a single compact order-convex real piece. -/
def principalTraceHeightOnePiece (r a b : ℝ) : Set ℝ :=
  Icc 0 Real.pi ∩ {φ | a * Real.sin φ ≤ r * Real.cos φ ∧
    r * Real.cos φ ≤ b * Real.sin φ}

theorem isCompact_principalTraceHeightOnePiece (r a b : ℝ) :
    IsCompact (principalTraceHeightOnePiece r a b) :=
  isCompact_Icc.inter_right (isClosed_principalTraceTangential r a b)

theorem principalTraceHeightOnePiece_ordConnected {r a b : ℝ} (hr : 0 < r) :
    (principalTraceHeightOnePiece r a b).OrdConnected := by
  rw [ordConnected_iff]
  intro x hx z hz hxz y hy
  rcases hx with ⟨hxI, hxlo, hxhi⟩
  rcases hz with ⟨hzI, hzlo, hzhi⟩
  have hx0 : 0 < x := lt_of_le_of_ne hxI.1 (fun h => by
    rw [← h] at hxhi; simp at hxhi; linarith)
  have hzpi : z < Real.pi := lt_of_le_of_ne hzI.2 (fun h => by
    rw [h] at hzlo; simp at hzlo; linarith)
  exact ⟨⟨hxI.1.trans hy.1, hy.2.trans hzI.2⟩,
    tangential_inequalities_between hr.le hx0 hzpi hy.1 hy.2 hxhi hzlo⟩

noncomputable def principalTraceHeightOneClosedPresentation
    {r a b : ℝ} (hr : 0 < r) : ClosedIccPresentation (principalTraceHeightOnePiece r a b) :=
  closedIccPresentationOfCompactOrdConnected _
    (isCompact_principalTraceHeightOnePiece r a b)
    (principalTraceHeightOnePiece_ordConnected hr)

/-- Any nonempty height-one presentation is strictly shorter than `π`: the
actual tangential contact inequalities exclude both endpoints. -/
theorem principalTraceHeightOnePiece_icc_span_lt
    {r a b lo hi : ℝ} (hr : 0 < r)
    (h : principalTraceHeightOnePiece r a b = Icc lo hi) : hi - lo < Real.pi := by
  by_cases hle : lo ≤ hi
  · have hlo : lo ∈ principalTraceHeightOnePiece r a b := h.symm ▸ ⟨le_rfl, hle⟩
    have hhi : hi ∈ principalTraceHeightOnePiece r a b := h.symm ▸ ⟨hle, le_rfl⟩
    rcases hlo with ⟨hloI, _, hloUpper⟩
    rcases hhi with ⟨hhiI, hhiLower, _⟩
    have hlo0 : 0 < lo := lt_of_le_of_ne hloI.1 (fun he => by
      rw [← he] at hloUpper; simp at hloUpper; linarith)
    have hhipi : hi < Real.pi := lt_of_le_of_ne hhiI.2 (fun he => by
      rw [he] at hhiLower; simp at hhiLower; linarith)
    linarith
  · linarith [Real.pi_pos]

/-- Exact chart equality at `δ=r`; the two touching half-pieces have been merged
before quotienting. -/
theorem trianglePolarTrace_inter_positiveChart_eq_shift_heightOnePiece
    {α c r : ℝ} (hr : 0 < r) :
    trianglePolarTrace (supportNeedleTriangle α r c) r ∩ Icc α (α + Real.pi) =
      shiftRealSet α (principalTraceHeightOnePiece r (c - 1 / 2) (c + 1 / 2)) := by
  ext θ
  constructor
  · rintro ⟨htrace, hchart⟩
    have hw := (mem_trianglePolarTrace_iff_principalTraceWindow_height_one hr
      (by linarith [hchart.1]) (by linarith [hchart.2])).1 htrace
    rcases hw with ⟨h0, hpi, _, hlo, hhi⟩
    exact ⟨⟨h0.le, hpi.le⟩, hlo, hhi⟩
  · intro h
    rcases h with ⟨hI, hlo, hhi⟩
    have h0 : 0 < θ - α := lt_of_le_of_ne hI.1 (fun he => by
      rw [← he] at hhi; simp at hhi; linarith)
    have hpi : θ - α < Real.pi := lt_of_le_of_ne hI.2 (fun he => by
      rw [he] at hlo; simp at hlo; linarith)
    refine ⟨(mem_trianglePolarTrace_iff_principalTraceWindow_height_one hr
      hI.1 hI.2).2 ⟨h0, hpi, Real.sin_le_one _, hlo, hhi⟩, ?_⟩
    constructor <;> linarith

/-- Height-one quotient coverage by the merged closed presentation. -/
theorem principalTraceHeightOneShiftedClosedPresentation_cover
    {α c r : ℝ} (hr : 0 < r) :
    ((principalTraceHeightOneClosedPresentation (a := c - 1 / 2)
      (b := c + 1 / 2) hr).toShiftedClosedPolarPresentation α
        (fun lo hi h => principalTraceHeightOnePiece_icc_span_lt hr h)).carrier =
      polarCircleTrace (supportNeedleTriangle α r c) r := by
  let P := (principalTraceHeightOneClosedPresentation (a := c - 1 / 2)
    (b := c + 1 / 2) hr).toShiftedClosedPolarPresentation α
      (fun lo hi h => principalTraceHeightOnePiece_icc_span_lt hr h)
  change P.carrier = _
  rw [P.carrier_eq, polarCircleTrace_supportNeedleTriangle_eq_positiveChart_image hr hr,
    trianglePolarTrace_inter_positiveChart_eq_shift_heightOnePiece hr]

/-- At `δ=r` the touching halves form one connected closed arc (or the trace is
empty), with coverage and maximality supplied by the one-arc constructor. -/
noncomputable def heightOneTraceClosedDecomposition
    {r α c : ℝ} (hr : 0 < r) :
    ClosedTraceDecomposition (supportNeedleTriangle α r c) r := by
  let P := (principalTraceHeightOneClosedPresentation (a := c - 1 / 2)
    (b := c + 1 / 2) hr).toShiftedClosedPolarPresentation α
      (fun lo hi h => principalTraceHeightOnePiece_icc_span_lt hr h)
  have hcover : P.carrier = polarCircleTrace (supportNeedleTriangle α r c) r :=
    principalTraceHeightOneShiftedClosedPresentation_cover hr
  exact closedTraceDecompositionOfPolarPresentation P hcover

/-- The strict-radius decomposition of an actual support-needle triangle.  No
coverage hypothesis is exposed: it is derived from the raw trace iff. -/
noncomputable def principalTraceClosedDecomposition
    {r α δ c : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hδr : δ < r) :
    ClosedTraceDecomposition (supportNeedleTriangle α δ c) r :=
  let hk0 : 0 ≤ δ / r := div_nonneg hδ.le hr.le
  let hk1 : δ / r < 1 := (div_lt_one hr).2 hδr
  let P := principalTraceShiftedClosedPolarPresentations (a := c - 1 / 2)
    (b := c + 1 / 2) α hδ hk0 hk1
  closedTraceDecompositionOfPolarPresentations P.1 P.2
    (principalTraceShiftedClosedPolarPresentations_cover hr hδ hδr)
    (disjoint_principalTraceClosedPresentations hk0 hk1 P.1 P.2)

/-- Genuine first-arc data for an actual strict-radius support triangle. -/
noncomputable def principalTraceFirstArcData?
    {r α δ c : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hδr : δ < r) :
    Option (FirstArcData (supportNeedleTriangle α δ c) r) :=
  (principalTraceClosedDecomposition hr hδ hδr).toFirstArcData?

/-- Uniform decomposition throughout the closed small-radius range. -/
noncomputable def supportTraceClosedDecomposition
    {r α δ c : ℝ} (hr : 0 < r) (hδ0 : 0 ≤ δ) (hδr : δ ≤ r) :
    ClosedTraceDecomposition (supportNeedleTriangle α δ c) r :=
  if hzero : δ = 0 then
    hzero.symm ▸ zeroHeightTraceClosedDecomposition hr
  else if hone : δ = r then
    hone.symm ▸ heightOneTraceClosedDecomposition hr
  else
    principalTraceClosedDecomposition hr (lt_of_le_of_ne hδ0 (Ne.symm hzero))
      (lt_of_le_of_ne hδr hone)

/-- Genuine optional first-arc data for every `0 ≤ δ ≤ r`. -/
noncomputable def supportTraceFirstArcData?
    {r α δ c : ℝ} (hr : 0 < r) (hδ0 : 0 ≤ δ) (hδr : δ ≤ r) :
    Option (FirstArcData (supportNeedleTriangle α δ c) r) :=
  (supportTraceClosedDecomposition hr hδ0 hδr).toFirstArcData?

/-- Exact covariance of the selected concrete trace arc at positive height.
The equality is between actual outputs of the presentation selector, including
the two-component winner and its component-zero tie rule. -/
theorem supportTraceFirstArcData?_firstArc_rotate
    {r α δ c : ℝ} (β : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hδr : δ ≤ r) :
    (supportTraceFirstArcData? (α := α + β) (c := c) hr hδ.le hδr).map
        FirstArcData.firstArc =
      (supportTraceFirstArcData? (α := α) (c := c) hr hδ.le hδr).map
        (fun D => D.firstArc.rotate β) := by
  by_cases hone : δ = r
  · subst δ
    rw [supportTraceFirstArcData?, supportTraceFirstArcData?,
      supportTraceClosedDecomposition, supportTraceClosedDecomposition,
      dif_neg hr.ne', dif_pos rfl, dif_neg hr.ne', dif_pos rfl]
    simp only [heightOneTraceClosedDecomposition]
    let P := principalTraceHeightOneClosedPresentation (a := c - 1 / 2)
      (b := c + 1 / 2) hr
    let hshort : ∀ lo hi,
        principalTraceHeightOnePiece r (c - 1 / 2) (c + 1 / 2) = Icc lo hi →
          hi - lo < Real.pi :=
      fun _ _ h => principalTraceHeightOnePiece_icc_span_lt hr h
    have hP := ClosedIccPresentation.toShiftedClosedPolarPresentation_arc_add
      P α β hshort
    have hold := closedTraceDecompositionOfPolarPresentation_firstArc
      (T := supportNeedleTriangle α r c) (r := r)
      (P.toShiftedClosedPolarPresentation α hshort)
      (principalTraceHeightOneShiftedClosedPresentation_cover hr)
    rw [closedTraceDecompositionOfPolarPresentation_firstArc]
    rw [hP, ← hold]
    rw [Option.map_map]
    rfl
  · have hδr' : δ < r := lt_of_le_of_ne hδr hone
    rw [supportTraceFirstArcData?, supportTraceFirstArcData?,
      supportTraceClosedDecomposition, supportTraceClosedDecomposition,
      dif_neg hδ.ne', dif_neg hone, dif_neg hδ.ne', dif_neg hone]
    simp only [principalTraceClosedDecomposition]
    let hk0 : 0 ≤ δ / r := div_nonneg hδ.le hr.le
    let hk1 : δ / r < 1 := (div_lt_one hr).2 hδr'
    let Pα := principalTraceShiftedClosedPolarPresentations (a := c - 1 / 2)
      (b := c + 1 / 2) α hδ hk0 hk1
    let Pβ := principalTraceShiftedClosedPolarPresentations (a := c - 1 / 2)
      (b := c + 1 / 2) (α + β) hδ hk0 hk1
    have hzero : Pβ.1.arc = Pα.1.arc.map (NormalizedPolarArc.rotate β) :=
      ClosedIccPresentation.toShiftedClosedPolarPresentation_arc_add
        (principalTraceClosedPresentations hδ hk0 hk1).1 α β
          (fun lo hi h => principalTraceLeftPiece_icc_span_lt hk1 h)
    have hone' : Pβ.2.arc = Pα.2.arc.map (NormalizedPolarArc.rotate β) :=
      ClosedIccPresentation.toShiftedClosedPolarPresentation_arc_add
        (principalTraceClosedPresentations hδ hk0 hk1).2 α β
          (fun lo hi h => principalTraceRightPiece_icc_span_lt hk1 h)
    have hold := closedTraceDecomposition_firstArc_eq_selectedArcOfOptions
      (T := supportNeedleTriangle α δ c) (r := r) Pα.1 Pα.2
      (principalTraceShiftedClosedPolarPresentations_cover hr hδ hδr')
      (disjoint_principalTraceClosedPresentations hk0 hk1 Pα.1 Pα.2)
    rw [closedTraceDecomposition_firstArc_eq_selectedArcOfOptions]
    rw [hzero, hone', selectedArcOfOptions?_rotate]
    rw [← hold]
    rw [Option.map_map]
    rfl

/-- Exterior endpoint identities from a genuine attained contact equation.  The
sine contact and fundamental-chart bounds identify the upper endpoint by
injectivity of sine; no endpoint envelope is assumed. -/
theorem exteriorEndpointData_of_traceContact
    {R₁ t S αlo : ℝ}
    (hSlo : -(Real.pi / 2) ≤ S) (hShi : S ≤ Real.pi / 2)
    (hcontact : Real.sin S = R₁ * Real.sin t)
    (hbalance : αlo + S = t) :
    S = Real.arcsin (R₁ * Real.sin t) ∧
      αlo = t - S ∧ S - αlo = 2 * S - t ∧
      (αlo + S) / 2 = t / 2 := by
  have hS : Real.arcsin (Real.sin S) = S := Real.arcsin_sin hSlo hShi
  have hformula : S = Real.arcsin (R₁ * Real.sin t) := by
    rw [← hcontact, hS]
  exact ⟨hformula, by linarith, by linarith, by linarith⟩

/-- Once the independent analytic exterior estimate is proved, the real contact
gap gives the ratio bound directly; this statement still assumes no envelope
containment. -/
theorem exteriorEndpoint_gap_ratio_of_traceContact
    {R₁ g t S αlo : ℝ} (ht : 0 < t)
    (hSlo : -(Real.pi / 2) ≤ S) (hShi : S ≤ Real.pi / 2)
    (hcontact : Real.sin S = R₁ * Real.sin t)
    (hbalance : αlo + S = t)
    (hanalytic : 2 * Real.arcsin (R₁ * Real.sin t) - t ≤ g * t) :
    (S - αlo) / t ≤ g := by
  have H := exteriorEndpointData_of_traceContact hSlo hShi hcontact hbalance
  rw [H.2.2.1, H.1]
  exact (div_le_iff₀ ht).2 hanalytic

/-- Elementary transitivity of set containment through an endpoint envelope.
This lemma contains no geometry and does not construct or identify endpoints. -/
theorem subset_dilate_of_subset_endpointEnvelope
    {X envelope dilate : Set ProjectiveDirection}
    (hX : X ⊆ envelope) (henvelope : envelope ⊆ dilate) : X ⊆ dilate :=
  hX.trans henvelope

/-- Pure endpoint-envelope algebra.  If an arbitrary set `X` is *already known*
to lie in the displayed endpoint interval, the endpoint equalities and length
bound place it in the same-centre dilation.  In particular, this theorem proves
no trace geometry, endpoint existence/contact statement, or selector result. -/
theorem endpointEnvelopeAlgebra_subset_sameCentre_dilate
    {g t s αlo αhi : ℝ} {X : Set ProjectiveDirection}
    (hsubset : X ⊆ directionsBetween αlo αhi)
    (hhi : αhi = s) (hbalance : αlo + αhi = t)
    (ht0 : 0 ≤ t) (htπ : t < Real.pi) (hs : t / 2 ≤ s)
    (hlen : 2 * s - t ≤ g * t) :
    X ⊆
        quotientClosedCenteredDilate g Real.pi (t / 2) (t / 2) ∧
      αhi - αlo = 2 * s - t ∧
      (αlo + αhi) / 2 = t / 2 ∧
      polarToProjective '' polarArc 0 t =
        quotientClosedCenteredArc Real.pi (t / 2) (t / 2) := by
  have hgap : αhi - αlo = 2 * s - t := by linarith
  have hmid : (αlo + αhi) / 2 = t / 2 := by linarith
  have hcfg := endpointConfiguration_envelope_subset_sameCentre_dilate
    (g := g) (t := t) (.interior s) ht0 htπ (Or.inl ⟨hs, hlen⟩)
  have henvelope : directionsBetween αlo αhi ⊆
      quotientClosedCenteredDilate g Real.pi (t / 2) (t / 2) := by
    rw [first_endpoint_configuration hhi hgap]
    exact hcfg.1
  exact ⟨subset_dilate_of_subset_endpointEnvelope hsubset henvelope,
    hgap, hmid, hcfg.2⟩

/-! ## Support-parameter primitives

`SupportParameter` is a pair `(δ, c)`: signed support height and tangential
centre.  `DirectedSupportParameter` prefixes it with a direction lift `α`, so a
support line is `supportPoint α δ ·` and the unit needle on it has base
endpoints at `c ± 1/2`.
-/

abbrev SupportParameter := ℝ × ℝ

abbrev DirectedSupportParameter := ℝ × SupportParameter

/-- Rotation drops out of the squared norm of a support-line point. -/
theorem planeNormSq_supportPoint (α δ x : ℝ) :
    planeNormSq (supportPoint α δ x) = δ ^ 2 + x ^ 2 := by
  simp [planeNormSq, supportPoint, addCoordinatePlane, scaleCoordinatePlane,
    unitDirection, unitNormal]
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq α]

/-- Both base endpoints are points of the raw support triangle. -/
theorem supportNeedle_baseEndpoints_mem_triangle (α δ c : ℝ) :
    supportPoint α δ (c - 1 / 2) ∈ supportNeedleTriangle α δ c ∧
      supportPoint α δ (c + 1 / 2) ∈ supportNeedleTriangle α δ c := by
  constructor
  · exact ⟨1, ⟨by norm_num, by norm_num⟩, c - 1 / 2,
      ⟨le_rfl, by linarith⟩, by simp [scaleCoordinatePlane]⟩
  · exact ⟨1, ⟨by norm_num, by norm_num⟩, c + 1 / 2,
      ⟨by linarith, le_rfl⟩, by simp [scaleCoordinatePlane]⟩

/-- The canonical zero-height decomposition always selects a singleton whose
projective centre is the needle direction; its half-span is zero.  This includes
the two-contact tie (component zero wins) and both one-contact branches. -/
theorem supportTraceFirstArcData?_zeroHeight_projectiveCenter_radius
    {r α c : ℝ} (hr : 0 < r)
    (D : FirstArcData (supportNeedleTriangle α 0 c) r)
    (hD : supportTraceFirstArcData? (α := α) (c := c) hr (le_refl 0) hr.le =
      some D) :
    ((((D.firstArc.lo + D.firstArc.hi) / 2 : ℝ) : ProjectiveDirection)) =
        (α : ProjectiveDirection) ∧
      (D.firstArc.hi - D.firstArc.lo) / 2 = 0 := by
  have hz : supportTraceFirstArcData? (α := α) (c := c) hr (le_refl 0) hr.le =
      (zeroHeightTraceClosedDecomposition (α := α) (c := c) hr).toFirstArcData? := by
    simp [supportTraceFirstArcData?, supportTraceClosedDecomposition]
  rw [hz] at hD
  simp only [zeroHeightTraceClosedDecomposition] at hD
  split at hD <;> rename_i hp
  · split at hD <;> rename_i hm
    · simp only [ClosedTraceDecomposition.toFirstArcData?, Option.some.injEq] at hD
      subst D
      simp [FirstArcData.firstArc, FirstArcData.ofTwoClosedArcs,
        FirstArcData.ofTwoComponents, singletonPolarArc, NormalizedPolarArc.span]
    · simp only [ClosedTraceDecomposition.toFirstArcData?, Option.some.injEq] at hD
      subst D
      simp [FirstArcData.firstArc, FirstArcData.ofOneClosedArc,
        FirstArcData.ofOneComponent, singletonPolarArc]
  · split at hD <;> rename_i hm
    · simp only [ClosedTraceDecomposition.toFirstArcData?, Option.some.injEq] at hD
      subst D
      simp [FirstArcData.firstArc, FirstArcData.ofOneClosedArc,
        FirstArcData.ofOneComponent, singletonPolarArc]
    · simp at hD

/-!
### Exact scope boundary

The coordinate model now gives an exact iff between the raw trace on a fixed
positive half-period chart and the shifted principal window when
`0 < δ < r`.  Its two half-window pieces are proved compact and order-connected
and are converted to explicit `empty` or closed `Icc` presentations (with the
singleton case included).  The boundary regimes are separate: `δ = 0` is
classified as at most two radial singleton contacts, while `δ = r` has the
height-one principal-window iff.  Fundamental-chart presentations carry
attained least/greatest endpoints on a fundamental chart, not on the periodic
trace over all of `ℝ`. The abstract and presentation-driven
`ClosedTraceDecomposition` APIs cover empty, one, and two
arc cases; in the concrete packager quotient gap data are derived from compact
disjointness rather than assumed.

The real `Icc` presentations are now promoted through `ℝ → AddCircle (2π)`
with exact carrier equations, faithful-chart quotient injectivity, and proved
left/right disjointness in the strict-radius regime.  A generic compact
separation argument supplies the no-crossing gap, and the uniform packager
constructs `ClosedTraceDecomposition` (empty/one/two) and genuine optional
`FirstArcData`, retaining singleton tangencies and the documented tie rule.
`principalTraceShiftedClosedPolarPresentations_cover` proves global circle
coverage from the periodic support coordinates, and
`principalTraceClosedDecomposition` supplies that equality to the strict
principal-window constructor. Separate zero-height and height-one constructors
retain the degenerate cases. Stronger Li endpoint-contact and ratio estimates
are not provided by this module and are not premises of the public one-tenth
theorem. No balance equation or endpoint-envelope identification is assumed.
-/

end

end StarKakeyaLower
