import StarKakeyaLower.CaseIEndpointAnalytic

/-!
# Orientation normalization and reflection of support coordinates

This module records the coordinate identities needed by local-contact arguments.
It also makes explicit an important boundary of the existing optional selector:
`selectedSupportFirstArc?` is a selector for the normalized convention `0 ≤ δ`,
not for arbitrary oriented support triples.  Thus reversing a strictly positive
triple makes the raw selector `none`; covariance is recovered by the signed
normalizing wrapper below.  Target reflection has two equivalent support
presentations, one of which keeps the height nonnegative.
-/

open Set

namespace StarKakeyaLower

noncomputable section

/-- Reflection in the line whose polar angle is `t/2`. -/
def reflectCoordinatePlane (t : ℝ) (z : CoordinatePlane) : CoordinatePlane :=
  (Real.cos t * z.1 + Real.sin t * z.2,
    Real.sin t * z.1 - Real.cos t * z.2)

/-- Reflection preserves squared Euclidean norm. -/
@[simp] theorem planeNormSq_reflectCoordinatePlane (t : ℝ) (z : CoordinatePlane) :
    planeNormSq (reflectCoordinatePlane t z) = planeNormSq z := by
  simp [planeNormSq, reflectCoordinatePlane]
  nlinarith [Real.sin_sq_add_cos_sq t]

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

/-- The underlying unit segment carrier is orientation independent. -/
theorem supportNeedle_add_pi_neg (α δ c : ℝ) :
    supportNeedle (α + Real.pi) (-δ) (-c) = supportNeedle α δ c := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨-x, ?_, ?_⟩
    · constructor <;> linarith [hx.1, hx.2]
    · simpa using (supportPoint_add_pi_neg α δ (-x)).symm
  · rintro ⟨x, hx, rfl⟩
    refine ⟨-x, ?_, ?_⟩
    · constructor <;> linarith [hx.1, hx.2]
    · simpa using supportPoint_add_pi_neg α δ x

/-- The lifted base endpoints are exchanged by orientation reversal. -/
theorem supportPoint_add_pi_neg_endpoint_minus (α δ c : ℝ) :
    supportPoint (α + Real.pi) (-δ) (-c - 1 / 2) =
      supportPoint α δ (c + 1 / 2) := by
  convert supportPoint_add_pi_neg α δ (c + 1 / 2) using 1 <;> ring

theorem supportPoint_add_pi_neg_endpoint_plus (α δ c : ℝ) :
    supportPoint (α + Real.pi) (-δ) (-c + 1 / 2) =
      supportPoint α δ (c - 1 / 2) := by
  convert supportPoint_add_pi_neg α δ (c - 1 / 2) using 1 <;> ring

/-- Orientation reversal does not change an unoriented direction. -/
theorem projectiveDirection_add_pi (α : ℝ) :
    ((α + Real.pi : ℝ) : ProjectiveDirection) = (α : ProjectiveDirection) := by
  rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]

/-- Consequently the polar circle trace (and hence every intrinsic first-arc
carrier) is unchanged. -/
theorem polarCircleTrace_supportNeedleTriangle_add_pi_neg
    (r α δ c : ℝ) :
    polarCircleTrace (supportNeedleTriangle (α + Real.pi) (-δ) (-c)) r =
      polarCircleTrace (supportNeedleTriangle α δ c) r := by
  rw [supportNeedleTriangle_add_pi_neg]

/-- Reflection sends support coordinates to the positive-height presentation.
The equivalent presentation `(t-α,-δ,c)` follows by orientation reversal. -/
theorem reflectCoordinatePlane_supportPoint (t α δ x : ℝ) :
    reflectCoordinatePlane t (supportPoint α δ x) =
      supportPoint (t - α + Real.pi) δ (-x) := by
  ext <;>
    simp [reflectCoordinatePlane, supportPoint, addCoordinatePlane,
      scaleCoordinatePlane, unitDirection, unitNormal, Real.sin_add,
      Real.cos_add, Real.sin_sub, Real.cos_sub] <;> ring

/-- Reflection commutes with radial scaling. -/
theorem reflectCoordinatePlane_scaleCoordinatePlane
    (t lam : ℝ) (z : CoordinatePlane) :
    reflectCoordinatePlane t (scaleCoordinatePlane lam z) =
      scaleCoordinatePlane lam (reflectCoordinatePlane t z) := by
  ext <;> simp [reflectCoordinatePlane, scaleCoordinatePlane] <;> ring

/-- Polar angles are reflected by `θ ↦ t-θ`. -/
theorem reflectCoordinatePlane_polarPoint (t r θ : ℝ) :
    reflectCoordinatePlane t (polarPoint r θ) = polarPoint r (t - θ) := by
  ext <;>
    simp [reflectCoordinatePlane, polarPoint, scaleCoordinatePlane, unitDirection,
      Real.sin_sub, Real.cos_sub] <;> ring

/-- Reflection transports the whole support triangle, with its endpoint
coordinates exchanged. -/
theorem supportNeedleTriangle_reflect (t α δ c : ℝ) :
    reflectCoordinatePlane t '' supportNeedleTriangle α δ c =
      supportNeedleTriangle (t - α + Real.pi) δ (-c) := by
  ext z
  constructor
  · rintro ⟨_, ⟨lam, hlam, x, hx, rfl⟩, rfl⟩
    refine ⟨lam, hlam, -x, ?_, ?_⟩
    · constructor <;> linarith [hx.1, hx.2]
    · rw [← reflectCoordinatePlane_supportPoint,
        reflectCoordinatePlane_scaleCoordinatePlane]
  · rintro ⟨lam, hlam, x, hx, rfl⟩
    refine ⟨scaleCoordinatePlane lam (supportPoint α δ (-x)),
      ⟨lam, hlam, -x, ?_, rfl⟩, ?_⟩
    · constructor <;> linarith [hx.1, hx.2]
    · rw [reflectCoordinatePlane_scaleCoordinatePlane,
        reflectCoordinatePlane_supportPoint]
      congr 2
      ring

/-- The same reflected triangle in the alternative signed-height presentation. -/
theorem supportNeedleTriangle_reflect_signed (t α δ c : ℝ) :
    reflectCoordinatePlane t '' supportNeedleTriangle α δ c =
      supportNeedleTriangle (t - α) (-δ) c := by
  rw [supportNeedleTriangle_reflect]
  convert supportNeedleTriangle_add_pi_neg (t - α) (-δ) c using 1 <;> ring

/-- Reflection swaps endpoint norms.  In particular every common endpoint
radius cap is preserved. -/
theorem reflected_support_endpoint_norms (t α δ c : ℝ) :
    planeNormSq (supportPoint (t - α + Real.pi) δ (-c - 1 / 2)) =
        planeNormSq (supportPoint α δ (c + 1 / 2)) ∧
      planeNormSq (supportPoint (t - α + Real.pi) δ (-c + 1 / 2)) =
        planeNormSq (supportPoint α δ (c - 1 / 2)) := by
  simp only [planeNormSq_supportPoint]
  constructor <;> ring

/-- Any common endpoint-radius cap is invariant under reflection. -/
theorem reflected_support_endpoint_cap_iff {t α δ c R : ℝ} :
    (planeNormSq (supportPoint (t - α + Real.pi) δ (-c - 1 / 2)) ≤ R ^ 2 ∧
      planeNormSq (supportPoint (t - α + Real.pi) δ (-c + 1 / 2)) ≤ R ^ 2) ↔
    (planeNormSq (supportPoint α δ (c - 1 / 2)) ≤ R ^ 2 ∧
      planeNormSq (supportPoint α δ (c + 1 / 2)) ≤ R ^ 2) := by
  rw [reflected_support_endpoint_norms t α δ c |>.1,
    reflected_support_endpoint_norms t α δ c |>.2]
  tauto

/-- Absolute height caps survive either orientation choice for reflection. -/
@[simp] theorem reflected_support_height_abs (δ : ℝ) : |(-δ)| = |δ| := abs_neg δ

/-- Reflection of a normalized lifted polar arc about the target bisector. -/
def NormalizedPolarArc.reflectTarget (t : ℝ) (A : NormalizedPolarArc) :
    NormalizedPolarArc := A.reverse.rotate t

@[simp] theorem NormalizedPolarArc.reflectTarget_lo (t : ℝ) (A : NormalizedPolarArc) :
    (A.reflectTarget t).lo = t - A.hi := by simp [NormalizedPolarArc.reflectTarget]; ring

@[simp] theorem NormalizedPolarArc.reflectTarget_hi (t : ℝ) (A : NormalizedPolarArc) :
    (A.reflectTarget t).hi = t - A.lo := by simp [NormalizedPolarArc.reflectTarget]; ring

@[simp] theorem NormalizedPolarArc.reflectTarget_span (t : ℝ) (A : NormalizedPolarArc) :
    (A.reflectTarget t).span = A.span := by simp [NormalizedPolarArc.reflectTarget]

/-- Carrier covariance under `θ ↦ t-θ`. -/
theorem NormalizedPolarArc.reflectTarget_carrier (t : ℝ) (A : NormalizedPolarArc) :
    (A.reflectTarget t).carrier =
      (fun q : PolarAngle => (t : PolarAngle) - q) '' A.carrier := by
  rw [NormalizedPolarArc.reflectTarget, NormalizedPolarArc.rotate_carrier,
    NormalizedPolarArc.reverse_carrier]
  ext q
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp [sub_eq_add_neg]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨-x, ⟨x, hx, rfl⟩, by simp [sub_eq_add_neg]⟩

/-- The target arc `[0,t]` is setwise fixed by its bisector reflection. -/
theorem polarArc_zero_target_reflection {t : ℝ} (ht0 : 0 ≤ t)
    (ht2pi : t < 2 * Real.pi) :
    (fun q : PolarAngle => (t : PolarAngle) - q) '' polarArc 0 t = polarArc 0 t := by
  rw [polarArc, quotientClosedInterval, if_neg (not_le.mpr (by simpa using ht2pi))]
  ext q
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨t - x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, ?_⟩
    change ((t - x : ℝ) : PolarAngle) = (t : PolarAngle) - (x : PolarAngle)
    exact AddCircle.coe_sub (2 * Real.pi) t x
  · rintro ⟨x, hx, rfl⟩
    refine ⟨((t - x : ℝ) : PolarAngle), ?_, ?_⟩
    · exact ⟨t - x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, rfl⟩
    · change (t : PolarAngle) - ((t - x : ℝ) : PolarAngle) = (x : PolarAngle)
      rw [← AddCircle.coe_sub]
      congr 1
      ring

/-- The raw selector deliberately rejects a reversed strictly positive support:
this is why orientation covariance cannot be stated for
`selectedSupportFirstArc?` itself. -/
theorem selectedSupportFirstArc?_orientation_reversal_eq_none
    {r α δ c : ℝ} (hδ : 0 < δ) :
    selectedSupportFirstArc? r (α + Real.pi) (-δ, -c) = none := by
  simp [selectedSupportFirstArc?, not_le.mpr (neg_neg_of_pos hδ)]

/-- Signed adapter for the existing normalized selector.  It changes orientation
before invoking `selectedSupportFirstArc?`, and does not alter its deterministic
component ordering or tie rule. -/
noncomputable def selectedOrientedSupportFirstArc?
    (r α δ c : ℝ) : Option NormalizedPolarArc :=
  if 0 ≤ δ then selectedSupportFirstArc? r α (δ, c)
  else selectedSupportFirstArc? r (α + Real.pi) (-δ, -c)

/-- Carrier-level orientation covariance of the signed adapter away from zero
height.  The only lifted discrepancy is one full polar turn.  The original
selector (and hence its component-zero tie rule) is used on both sides. -/
theorem selectedOrientedSupportFirstArc?_add_pi_neg_carrier
    {r α δ c : ℝ} (hδ : δ ≠ 0) :
    (selectedOrientedSupportFirstArc? r (α + Real.pi) (-δ) (-c)).map
        NormalizedPolarArc.carrier =
      (selectedOrientedSupportFirstArc? r α δ c).map
        NormalizedPolarArc.carrier := by
  rcases lt_or_gt_of_ne hδ with hneg | hpos
  · rw [selectedOrientedSupportFirstArc?, selectedOrientedSupportFirstArc?,
      if_pos (neg_nonneg.mpr hneg.le), if_neg (not_le.mpr hneg)]
  · rw [selectedOrientedSupportFirstArc?, selectedOrientedSupportFirstArc?,
      if_neg (not_le.mpr (neg_neg_of_pos hpos)), if_pos hpos.le]
    simp only [neg_neg]
    by_cases hr : 0 < r
    · by_cases hδr : δ ≤ r
      · rw [show α + Real.pi + Real.pi = α + 2 * Real.pi by ring,
          selectedSupportFirstArc?_add_of_pos (β := 2 * Real.pi) hr hpos hδr,
          Option.map_map]
        cases hA : selectedSupportFirstArc? r α (δ, c) with
        | none => simp
        | some A =>
            simp only [Option.map_some]
            simpa [NormalizedPolarArc.changeLift] using
              (A.changeLift_carrier (1 : ℤ))
      · simp [selectedSupportFirstArc?, hr, hpos.le, hδr]
    · simp [selectedSupportFirstArc?, hr]

end

end StarKakeyaLower
