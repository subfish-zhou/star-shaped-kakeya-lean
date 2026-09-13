import StarKakeyaLower.LiGeometry
import StarKakeyaLower.CaseIISelection

/-!
# Adapter from Li's coordinate needles to the Euclidean Case-II API

`DirectionNeedle` uses the product model `ℝ × ℝ`, while the fixed greedy
machinery uses `EuclideanSpace ℝ (Fin 2)`.  This file gives the canonical
measure-preserving identification and turns the raw support-line data into the
actual `UnitNeedle` consumed by Case II.  No geometric estimate is stored in the
adapter.
-/

open Set MeasureTheory

namespace StarKakeyaLower

noncomputable section

/-- Canonical coordinate identification from Li's product plane to `Plane`. -/
def coordinatePlaneEquiv : CoordinatePlane ≃ᵐ Plane :=
  (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).symm.trans
    (MeasurableEquiv.toLp 2 ((Fin 2) → ℝ))

@[simp] theorem coordinatePlaneEquiv_apply (z : CoordinatePlane) :
    coordinatePlaneEquiv z = WithLp.toLp 2 ![z.1, z.2] := rfl

@[simp] theorem coordinatePlaneEquiv_apply_zero (z : CoordinatePlane) :
    coordinatePlaneEquiv z 0 = z.1 := rfl

@[simp] theorem coordinatePlaneEquiv_apply_one (z : CoordinatePlane) :
    coordinatePlaneEquiv z 1 = z.2 := rfl

/-- The coordinate identification preserves planar Lebesgue measure. -/
theorem coordinatePlaneEquiv_measurePreserving :
    MeasurePreserving coordinatePlaneEquiv (volume.prod volume) volume := by
  have hpi := measurePreserving_piFinTwo (fun _ : Fin 2 => (volume : Measure ℝ))
  rw [← volume_pi] at hpi
  have hLp := PiLp.volume_preserving_toLp (Fin 2)
  exact hpi.symm.trans hLp

/-- Hence measurable images have exactly the same area. -/
theorem coordinatePlaneEquiv_volume_image (S : Set CoordinatePlane)
    (hS : MeasurableSet S) :
    volume (coordinatePlaneEquiv '' S) = (volume.prod volume) S := by
  have hLp := PiLp.volume_preserving_toLp (Fin 2)
  have hLp' := hLp.symm (MeasurableEquiv.toLp 2 ((Fin 2) → ℝ))
  have hpi := measurePreserving_piFinTwo (fun _ : Fin 2 => (volume : Measure ℝ))
  rw [← volume_pi] at hpi
  have hinv : MeasurePreserving coordinatePlaneEquiv.symm volume
      (volume.prod volume) := hLp'.trans hpi
  have hpre : coordinatePlaneEquiv.symm ⁻¹' S = coordinatePlaneEquiv '' S := by
    ext z
    constructor
    · intro hz
      exact ⟨coordinatePlaneEquiv.symm z, hz,
        coordinatePlaneEquiv.apply_symm_apply z⟩
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
  rw [← hpre, hinv.measure_preimage hS.nullMeasurableSet]

/-- The endpoint model of a raw Li needle as a genuine Euclidean unit needle. -/
def DirectionNeedle.toUnitNeedle {d : ProjectiveDirection}
    (N : DirectionNeedle d) : UnitNeedle where
  left := coordinatePlaneEquiv (supportPoint N.angle N.height (N.centre - 1 / 2))
  right := coordinatePlaneEquiv (supportPoint N.angle N.height (N.centre + 1 / 2))
  unit_length := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp only [Fin.sum_univ_two, PiLp.sub_apply, coordinatePlaneEquiv_apply_zero,
      coordinatePlaneEquiv_apply_one, Real.norm_eq_abs, sq_abs]
    have h := supportNeedle_unit_length N.angle N.height N.centre
    dsimp [planeNormSq, subCoordinatePlane] at h
    have hsquare :
        ((supportPoint N.angle N.height (N.centre - 1 / 2)).1 -
            (supportPoint N.angle N.height (N.centre + 1 / 2)).1) ^ 2 +
          ((supportPoint N.angle N.height (N.centre - 1 / 2)).2 -
            (supportPoint N.angle N.height (N.centre + 1 / 2)).2) ^ 2 = 1 := by
      nlinarith [h]
    rw [hsquare, Real.sqrt_one]

/-- The adapter retains the declared projective direction. -/
theorem DirectionNeedle.toUnitNeedle_hasDirection {d : ProjectiveDirection}
    (N : DirectionNeedle d) : N.toUnitNeedle.HasDirection d := by
  refine ⟨N.angle, N.direction_eq, 1, one_ne_zero, ?_⟩
  ext i
  fin_cases i <;>
    simp [DirectionNeedle.toUnitNeedle, supportPoint, addCoordinatePlane,
      scaleCoordinatePlane, unitDirection, unitNormal, angleVector] <;> ring

/-- The Euclidean determinant height is the absolute value of Li's signed
support height. -/
theorem DirectionNeedle.toUnitNeedle_height_zero {d : ProjectiveDirection}
    (N : DirectionNeedle d) :
    N.toUnitNeedle.height 0 = |N.height| := by
  rw [UnitNeedle.height]
  simp only [DirectionNeedle.toUnitNeedle, coordinatePlaneEquiv_apply_zero,
    coordinatePlaneEquiv_apply_one, PiLp.sub_apply, PiLp.zero_apply,
    supportPoint, addCoordinatePlane, scaleCoordinatePlane, unitDirection, unitNormal]
  have htrig := Real.sin_sq_add_cos_sq N.angle
  rw [abs_eq_abs]
  right
  ring_nf
  calc
    -(N.height * Real.sin N.angle ^ 2) - N.height * Real.cos N.angle ^ 2 =
        -N.height * (Real.sin N.angle ^ 2 + Real.cos N.angle ^ 2) := by ring
    _ = -N.height := by rw [htrig]; ring

/-- The filled support triangle is transported literally to the Euclidean
`UnitNeedle.triangleHull`; this is the set-level triangle adapter used by all
Case-II containment and separation lemmas. -/
theorem DirectionNeedle.image_triangle_eq_triangleHull {d : ProjectiveDirection}
    (N : DirectionNeedle d) :
    coordinatePlaneEquiv '' N.triangle = N.toUnitNeedle.triangleHull 0 := by
  ext p
  constructor
  · rintro ⟨z, ⟨lam, hlam, x, hx, rfl⟩, rfl⟩
    simp only [UnitNeedle.triangleHull, mem_iUnion]
    let q := coordinatePlaneEquiv (supportPoint N.angle N.height x)
    refine ⟨q, ?_, ?_⟩
    · rw [UnitNeedle.carrier, segment_eq_image]
      refine ⟨x - (N.centre - 1 / 2), ?_, ?_⟩
      · constructor <;> linarith [hx.1, hx.2]
      · ext i
        fin_cases i <;>
          simp [q, DirectionNeedle.toUnitNeedle, supportPoint, addCoordinatePlane,
            scaleCoordinatePlane, unitDirection, unitNormal,
            AffineMap.lineMap_apply] <;> ring
    · rw [segment_eq_image]
      refine ⟨lam, hlam, ?_⟩
      ext i
      fin_cases i <;>
        simp [q, scaleCoordinatePlane, AffineMap.lineMap_apply]
  · simp only [UnitNeedle.triangleHull, mem_iUnion]
    rintro ⟨q, hq, hp⟩
    rw [UnitNeedle.carrier, segment_eq_image] at hq
    obtain ⟨s, hs, rfl⟩ := hq
    rw [segment_eq_image] at hp
    obtain ⟨lam, hlam, rfl⟩ := hp
    let x := N.centre - 1 / 2 + s
    refine ⟨scaleCoordinatePlane lam (supportPoint N.angle N.height x), ?_, ?_⟩
    · exact ⟨lam, hlam, x, ⟨by dsimp [x]; linarith [hs.1], by dsimp [x]; linarith [hs.2]⟩,
        rfl⟩
    · ext i
      fin_cases i <;>
        simp [x, DirectionNeedle.toUnitNeedle, supportPoint, addCoordinatePlane,
          scaleCoordinatePlane, unitDirection, unitNormal,
          AffineMap.lineMap_apply] <;> ring

/-- Raw Li heights and the paper deletion weight. -/
def li25Height (N : (d : ProjectiveDirection) → DirectionNeedle d)
    (d : ProjectiveDirection) : ℝ := |(N d).height|

/-- Li 2.3 uses the unscaled exterior-area weight `asin(δ/r)`.  This must not be
confused with the larger deletion radius used by the greedy selection. -/
def li25ExteriorWeight
    (N : (d : ProjectiveDirection) → DirectionNeedle d) (r : ℝ)
    (d : ProjectiveDirection) : ℝ :=
  Real.arcsin (li25Height N d / r)

/-- The deletion weight is `asin(δ/((1-ε)r))`; fixed deletion subsequently
uses radius `2H`, exactly matching the intervals in Li's proof. -/
def li25DeletionWeight
    (N : (d : ProjectiveDirection) → DirectionNeedle d) (eps r : ℝ)
    (d : ProjectiveDirection) : ℝ :=
  caseIIPaperWeight eps r (li25Height N d)

/-- The finite/infinite fixed selection is constructed directly from the actual
raw `DirectionNeedle` family.  In particular, no selected sequence and no
certificate is an argument. -/
noncomputable def li25FixedSelectionOutcome
    (N : (d : ProjectiveDirection) → DirectionNeedle d)
    (A : Set ProjectiveDirection) (eps r a : ℝ)
    (hbound : ∀ d ∈ A, li25Height N d ≤ a) :
    FixedSelectionOutcome (li25Height N) (li25DeletionWeight N eps r)
      (1 - eps) A :=
  fixedSelectionOutcome (li25Height N) (li25DeletionWeight N eps r)
    (1 - eps) A (fun d => abs_nonneg _) hbound

end

end StarKakeyaLower
