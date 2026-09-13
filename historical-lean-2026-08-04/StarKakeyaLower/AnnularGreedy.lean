import StarKakeyaLower.AnnularGeometry
import StarKakeyaLower.CaseIISelection

/-!
# Finite restricted exterior assembly (spike 001, milestones M3a and M3b)

This module is the exterior (annular) analogue of the Case-II finite greedy
assembly of `CaseIISelection.lean`.  Every planar quantity is restricted to the
exterior `· \ Metric.closedBall K.center r0` of a fixed closed ball around the
star centre.

* **M3a** (`selected_exterior_sum_le_outerMeasure_finite`) concerns only the
  selected triangles.  It carries **no** residual-fan term and depends on
  nothing from M3b or M4.
* **M3b** proves the annular fan bound
  (`euclideanPolarAnnulus_outerMeasure_ge`) *before* its first use, then the
  finite full exterior geometric bound
  (`geometric_exterior_outerMeasure_lower_finite`) and the finite coefficient
  elimination (`annular_exterior_lower_bound_of_finiteSelection`) with the
  coefficient `min (annularCExt a r0 rho m / 4) ((rho ^ 2 - r0 ^ 2) / 2)`.

Import closure: `AnnularGeometry` (M2) and `CaseIISelection`, both CLEAN in the
sense of `LEAN-PLAN.md` §1; no module carrying the frozen witness constants is
reachable.

All disjoint sums live on the **open** restricted triangles
`triangleInterior · \ closedBall ·`; closed hulls are never claimed pairwise
disjoint anywhere.  The only licensed passage to a hull is M2's
`UnitNeedle.volume_triangleInterior_diff_closedBall`, used inside
`UnitNeedle.annular_payment_triangleInterior`.
-/

open Set MeasureTheory Metric

namespace StarKakeyaLower

noncomputable section

/-! ## M3a — selected restricted interiors

Nothing in this section mentions the residual fan.
-/

namespace FiniteFixedSelection

variable {height H : Direction → ℝ} {m a : ℝ} {A : Set Direction}

/-- The restricted (exterior) part of one selected open triangle.  The sum of
the exterior ledger runs over these **open** sets. -/
def restrictedTriangle (F : FiniteFixedSelection height H m A)
    {E : Set Plane} (K : StarShapedKakeya E) (r0 : ℝ) (i : Fin F.N) : Set Plane :=
  (K.needleFamily (F.selected i)).triangleInterior K.center \
    Metric.closedBall K.center r0

theorem measurableSet_restrictedTriangle (F : FiniteFixedSelection height H m A)
    {E : Set Plane} (K : StarShapedKakeya E) (r0 : ℝ) (i : Fin F.N) :
    MeasurableSet (F.restrictedTriangle K r0 i) :=
  ((K.needleFamily (F.selected i)).triangleInterior_measurable K.center).diff
    measurableSet_closedBall

/-- The finite union of the restricted selected open triangles. -/
def restrictedSelectedUnion (F : FiniteFixedSelection height H m A)
    {E : Set Plane} (K : StarShapedKakeya E) (r0 : ℝ) : Set Plane :=
  ⋃ i : Fin F.N, F.restrictedTriangle K r0 i

theorem restrictedSelectedUnion_eq (F : FiniteFixedSelection height H m A)
    {E : Set Plane} (K : StarShapedKakeya E) (r0 : ℝ) :
    F.restrictedSelectedUnion K r0 =
      F.selectedTriangleUnion K \ Metric.closedBall K.center r0 := by
  simp [restrictedSelectedUnion, restrictedTriangle, selectedTriangleUnion,
    iUnion_diff]

theorem measurableSet_restrictedSelectedUnion
    (F : FiniteFixedSelection height H m A)
    {E : Set Plane} (K : StarShapedKakeya E) (r0 : ℝ) :
    MeasurableSet (F.restrictedSelectedUnion K r0) :=
  MeasurableSet.iUnion fun i => F.measurableSet_restrictedTriangle K r0 i

theorem restrictedSelectedUnion_subset (F : FiniteFixedSelection height H m A)
    {E : Set Plane} (K : StarShapedKakeya E) (r0 : ℝ) :
    F.restrictedSelectedUnion K r0 ⊆ E \ Metric.closedBall K.center r0 := by
  rw [F.restrictedSelectedUnion_eq K r0]
  exact diff_subset_diff_left (F.selectedTriangleUnion_subset K)

/-- **Restricted disjointness by monotonicity.**  Deleting a common set from
two disjoint sets keeps them disjoint, so the existing pairwise disjointness of
the selected *open* triangles transfers verbatim to their exterior parts.  No
statement is made about the closed hulls. -/
theorem pairwise_disjoint_restrictedTriangle
    (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (hbound : ∀ θ ∈ A, height θ ≤ a)
    {E : Set Plane} (K : StarShapedKakeya E) {rho : ℝ} (hrho : 0 < rho)
    (hheight : ∀ θ, height θ = (K.needleFamily θ).height K.center)
    (hpos : ∀ i, 0 < height (F.selected i))
    (hscaled : ∀ i, height (F.selected i) < m * rho)
    (hH : ∀ i, H (F.selected i) =
      Real.arcsin (height (F.selected i) / (m * rho)))
    (hout : ∀ θ ∈ A, (K.needleFamily θ).OutsideBall rho K.center)
    (r0 : ℝ) :
    Pairwise (fun i j : Fin F.N => Disjoint
      (F.restrictedTriangle K r0 i) (F.restrictedTriangle K r0 j)) := by
  intro i j hij
  exact (F.pairwise_disjoint_triangles hm0 hm1 hbound K hrho hheight hpos hscaled
    hH hout hij).mono diff_subset diff_subset

/-- **Finite exterior additivity.**  The volume of the union of the restricted
selected open triangles is the finite sum of their volumes. -/
theorem volume_restrictedSelectedUnion (F : FiniteFixedSelection height H m A)
    {E : Set Plane} (K : StarShapedKakeya E) (r0 : ℝ)
    (hpair : Pairwise (fun i j : Fin F.N => Disjoint
      (F.restrictedTriangle K r0 i) (F.restrictedTriangle K r0 j))) :
    volume (F.restrictedSelectedUnion K r0) =
      ∑ i : Fin F.N, volume (F.restrictedTriangle K r0 i) := by
  rw [restrictedSelectedUnion,
    measure_iUnion hpair (fun i => F.measurableSet_restrictedTriangle K r0 i),
    tsum_fintype]

/-- The finite sum of restricted selected areas is at most the exterior outer
measure of the ambient set. -/
theorem sum_volume_restrictedTriangle_le_outerMeasure
    (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (hbound : ∀ θ ∈ A, height θ ≤ a)
    {E : Set Plane} (K : StarShapedKakeya E) {rho : ℝ} (hrho : 0 < rho)
    (hheight : ∀ θ, height θ = (K.needleFamily θ).height K.center)
    (hpos : ∀ i, 0 < height (F.selected i))
    (hscaled : ∀ i, height (F.selected i) < m * rho)
    (hH : ∀ i, H (F.selected i) =
      Real.arcsin (height (F.selected i) / (m * rho)))
    (hout : ∀ θ ∈ A, (K.needleFamily θ).OutsideBall rho K.center)
    (r0 : ℝ) :
    ∑ i : Fin F.N, volume (F.restrictedTriangle K r0 i) ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0) := by
  rw [← F.volume_restrictedSelectedUnion K r0
    (F.pairwise_disjoint_restrictedTriangle hm0 hm1 hbound K hrho hheight hpos
      hscaled hH hout r0), Measure.toOuterMeasure_apply]
  exact measure_mono (F.restrictedSelectedUnion_subset K r0)

/-- **Exterior payment on the selected restricted interiors** (`PROOF.md`
(8.2)).  `hCext` is what licenses `ENNReal.ofReal_mul`; without it the
coefficient extraction is illegal (and the statement vacuous). -/
theorem cost_le_sum_volume_restrictedTriangle
    (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (hbound : ∀ θ ∈ A, height θ ≤ a)
    {E : Set Plane} (K : StarShapedKakeya E) {rho r0 : ℝ}
    (ha : 0 < a) (harho : a < m * rho) (hr0 : 0 < r0) (hlt : r0 < rho)
    (hCext : 0 < annularCExt a r0 rho m)
    (hheight : ∀ θ, height θ = (K.needleFamily θ).height K.center)
    (hH : ∀ i, H (F.selected i) =
      Real.arcsin (height (F.selected i) / (m * rho)))
    (hout : ∀ θ ∈ A, (K.needleFamily θ).OutsideBall rho K.center) :
    ENNReal.ofReal (annularCExt a r0 rho m) *
        ∑ i : Fin F.N, ENNReal.ofReal (H (F.selected i)) ≤
      ∑ i : Fin F.N, volume (F.restrictedTriangle K r0 i) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hmem : F.selected i ∈ A := F.selected_mem_initial hm0 hm1 hbound i
  have hpay := (K.needleFamily (F.selected i)).annular_payment_triangleInterior
    hm0 hm1 ha harho hr0 hlt
    (by
      have := hbound _ hmem
      rw [hheight] at this
      exact this)
    (hout _ hmem)
  rw [← ENNReal.ofReal_mul hCext.le, hH i, hheight]
  exact hpay

/-- **M3a exit theorem.**  The finite selected exterior payment, with no
residual-fan term and no dependence on M3b or M4. -/
theorem selected_exterior_sum_le_outerMeasure_finite
    (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (hbound : ∀ θ ∈ A, height θ ≤ a)
    {E : Set Plane} (K : StarShapedKakeya E) {rho r0 : ℝ}
    (ha : 0 < a) (harho : a < m * rho) (hr0 : 0 < r0) (hlt : r0 < rho)
    (hCext : 0 < annularCExt a r0 rho m)
    (hheight : ∀ θ, height θ = (K.needleFamily θ).height K.center)
    (hpos : ∀ i, 0 < height (F.selected i))
    (hscaled : ∀ i, height (F.selected i) < m * rho)
    (hH : ∀ i, H (F.selected i) =
      Real.arcsin (height (F.selected i) / (m * rho)))
    (hout : ∀ θ ∈ A, (K.needleFamily θ).OutsideBall rho K.center) :
    ENNReal.ofReal (annularCExt a r0 rho m) *
        ∑ i : Fin F.N, ENNReal.ofReal (H (F.selected i)) ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0) :=
  (F.cost_le_sum_volume_restrictedTriangle hm0 hm1 hbound K ha harho hr0 hlt
      hCext hheight hH hout).trans
    (F.sum_volume_restrictedTriangle_le_outerMeasure hm0 hm1 hbound K
      (lt_trans hr0 hlt) hheight hpos hscaled hH hout r0)

/-- The `C_ext / 4` times `Σ 4 H_i` normalisation of the exterior payment is
literally the same `ENNReal` as `C_ext` times `Σ H_i`.  Pulling the scalar
through `ENNReal.ofReal` needs `hCext`. -/
theorem quarter_cost_eq_cost (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) {rho r0 : ℝ} (hr0 : 0 < r0) (hlt : r0 < rho)
    (hCext : 0 < annularCExt a r0 rho m)
    (hpos : ∀ i, 0 < height (F.selected i))
    (hH : ∀ i, H (F.selected i) =
      Real.arcsin (height (F.selected i) / (m * rho))) :
    ENNReal.ofReal (annularCExt a r0 rho m / 4) *
        ∑ i : Fin F.N, ENNReal.ofReal (4 * H (F.selected i)) =
      ENNReal.ofReal (annularCExt a r0 rho m) *
        ∑ i : Fin F.N, ENNReal.ofReal (H (F.selected i)) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hH0 : 0 ≤ H (F.selected i) := by
    rw [hH i]
    exact Real.arcsin_nonneg.2 (div_nonneg (hpos i).le
      (mul_pos hm0 (lt_trans hr0 hlt)).le)
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hCext.le]
  congr 1
  ring

/-- Deletion-budget form of the exterior payment against the finite sum of
restricted selected areas.  This is the shape the finite coefficient
elimination of M3b consumes. -/
theorem quarter_cost_le_sum_volume_restrictedTriangle
    (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (hbound : ∀ θ ∈ A, height θ ≤ a)
    {E : Set Plane} (K : StarShapedKakeya E) {rho r0 : ℝ}
    (ha : 0 < a) (harho : a < m * rho) (hr0 : 0 < r0) (hlt : r0 < rho)
    (hCext : 0 < annularCExt a r0 rho m)
    (hheight : ∀ θ, height θ = (K.needleFamily θ).height K.center)
    (hpos : ∀ i, 0 < height (F.selected i))
    (hH : ∀ i, H (F.selected i) =
      Real.arcsin (height (F.selected i) / (m * rho)))
    (hout : ∀ θ ∈ A, (K.needleFamily θ).OutsideBall rho K.center) :
    ENNReal.ofReal (annularCExt a r0 rho m / 4) *
        ∑ i : Fin F.N, ENNReal.ofReal (4 * H (F.selected i)) ≤
      ∑ i : Fin F.N, volume (F.restrictedTriangle K r0 i) := by
  rw [F.quarter_cost_eq_cost hm0 hr0 hlt hCext hpos hH]
  exact F.cost_le_sum_volume_restrictedTriangle hm0 hm1 hbound K ha harho hr0 hlt
    hCext hheight hH hout

/-- Deletion-budget form of the M3a exit theorem. -/
theorem quarter_cost_le_outerMeasure_finite
    (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (hbound : ∀ θ ∈ A, height θ ≤ a)
    {E : Set Plane} (K : StarShapedKakeya E) {rho r0 : ℝ}
    (ha : 0 < a) (harho : a < m * rho) (hr0 : 0 < r0) (hlt : r0 < rho)
    (hCext : 0 < annularCExt a r0 rho m)
    (hheight : ∀ θ, height θ = (K.needleFamily θ).height K.center)
    (hpos : ∀ i, 0 < height (F.selected i))
    (hscaled : ∀ i, height (F.selected i) < m * rho)
    (hH : ∀ i, H (F.selected i) =
      Real.arcsin (height (F.selected i) / (m * rho)))
    (hout : ∀ θ ∈ A, (K.needleFamily θ).OutsideBall rho K.center) :
    ENNReal.ofReal (annularCExt a r0 rho m / 4) *
        ∑ i : Fin F.N, ENNReal.ofReal (4 * H (F.selected i)) ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0) :=
  (F.quarter_cost_le_sum_volume_restrictedTriangle hm0 hm1 hbound K ha harho hr0
      hlt hCext hheight hpos hH hout).trans
    (F.sum_volume_restrictedTriangle_le_outerMeasure hm0 hm1 hbound K
      (lt_trans hr0 hlt) hheight hpos hscaled hH hout r0)

end FiniteFixedSelection

/-! ## M3b — the annular residual fan

`PROOF.md` (B5).  The lower bound below is proved **before** any theorem that
consumes it, and it holds for an arbitrary, possibly nonmeasurable angle set:
it is a lower bound, so no measurability of `Θ` may be assumed.  The `2π` cut
is handled exactly as in `PolarOuterMeasure.lean`, by intersecting the angle
set with `Ioo (-π) π` inside `angleSetOuter`; a single cut point is null.
-/

/-- The half-open annular polar sector in the product coordinate model used by
Mathlib's polar-coordinate change of variables. -/
private def coordAnnulusSector (o : CoordinatePlane) (r0 rho : ℝ) (Θ : Set ℝ) :
    Set CoordinatePlane :=
  {z | ∃ r ∈ Ioc r0 rho, ∃ θ ∈ Θ ∩ Ioo (-Real.pi) Real.pi, z = o + polarPoint r θ}

/-- The radial integral of the annulus, with the null radius `r0` cut out of
the integrand so that the section bound holds at *every* point of `Icc r0 ρ`. -/
private theorem lintegral_annulus_radius_mul_const {r0 rho : ℝ} (hr0 : 0 ≤ r0)
    (hle : r0 ≤ rho) (c : ENNReal) :
    (∫⁻ r in Icc r0 rho, ENNReal.ofReal r * (if r0 < r then c else 0)) =
      ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) * c := by
  have hcongr : (∫⁻ r in Icc r0 rho, ENNReal.ofReal r * (if r0 < r then c else 0)) =
      ∫⁻ r in Icc r0 rho, ENNReal.ofReal r * c := by
    apply lintegral_congr_ae
    have hne : ∀ᵐ r : ℝ ∂volume, r ≠ r0 := ae_iff.mpr (by
      simpa only [not_ne_iff, setOf_eq_eq_singleton] using
        (measure_singleton (μ := volume) r0))
    filter_upwards [ae_restrict_of_ae hne, ae_restrict_mem measurableSet_Icc]
      with r hrne hrmem
    have hgt : r0 < r := lt_of_le_of_ne hrmem.1 (Ne.symm hrne)
    simp [hgt]
  rw [hcongr, lintegral_mul_const c (show Measurable (fun r : ℝ => ENNReal.ofReal r) from
    measurable_id.ennreal_ofReal)]
  congr 1
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
      integral_id]
  · exact continuous_id.integrableOn_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hr0.trans hr.1

private theorem coordAnnulusSector_zero_outerMeasure_ge {r0 rho : ℝ}
    (hr0 : 0 ≤ r0) (hle : r0 ≤ rho) (Θ : Set ℝ) :
    ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) * angleSetOuter Θ ≤
      volume.toOuterMeasure (coordAnnulusSector 0 r0 rho Θ) := by
  rw [← lintegral_annulus_radius_mul_const hr0 hle (angleSetOuter Θ)]
  apply outerMeasure_ge_lintegral_of_angleOuter_ge _ (a := r0) (b := rho) hr0
    (fun r => if r0 < r then angleSetOuter Θ else 0)
  intro r hr
  by_cases hgt : r0 < r
  · simp only [hgt, if_true]
    apply OuterMeasure.mono
    intro θ hθ
    exact ⟨hθ.2, r, ⟨hgt, hr.2⟩, θ, hθ, by simp⟩
  · simp [hgt]

private theorem coordAnnulusSector_outerMeasure_ge (o : CoordinatePlane)
    {r0 rho : ℝ} (hr0 : 0 ≤ r0) (hle : r0 ≤ rho) (Θ : Set ℝ) :
    ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) * angleSetOuter Θ ≤
      volume.toOuterMeasure (coordAnnulusSector o r0 rho Θ) := by
  have hzero := coordAnnulusSector_zero_outerMeasure_ge hr0 hle Θ
  rw [Measure.toOuterMeasure_apply] at hzero ⊢
  calc
    _ ≤ volume (coordAnnulusSector 0 r0 rho Θ) := hzero
    _ = volume (coordAnnulusSector o r0 rho Θ) := by
      rw [← measure_preimage_add volume o (coordAnnulusSector o r0 rho Θ)]
      congr 1
      ext z
      simp only [coordAnnulusSector, mem_preimage, mem_setOf_eq]
      constructor
      · rintro ⟨r, hr, θ, hθ, heq⟩
        exact ⟨r, hr, θ, hθ, by simpa using heq⟩
      · rintro ⟨r, hr, θ, hθ, heq⟩
        refine ⟨r, hr, θ, hθ, ?_⟩
        calc
          z = polarPoint r θ := add_left_cancel heq
          _ = 0 + polarPoint r θ := by simp

/-- The half-open annular polar sector in the Euclidean-space model used by the
needle family. -/
def euclideanAnnulusSector (o : Plane) (r0 rho : ℝ) (Θ : Set ℝ) : Set Plane :=
  {z | ∃ r ∈ Ioc r0 rho, ∃ θ ∈ Θ ∩ Ioo (-Real.pi) Real.pi, z = o + r • angleVector θ}

/-- Local copy of the volume-preserving coordinate equivalence.  The one in
`PolarOuterMeasure.lean` is `private`, so it cannot be reused from here; the
definition is identical and carries no assumption. -/
private def planeCoords : Plane ≃ᵐ CoordinatePlane :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

private theorem planeCoords_measurePreserving :
    MeasurePreserving planeCoords volume volume :=
  (MeasureTheory.volume_preserving_finTwoArrow ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

private theorem outerMeasure_preimage_le_of_measurePreserving
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μα : Measure α} {μβ : Measure β} {f : α → β}
    (hf : MeasurePreserving f μα μβ) (A : Set β) :
    μα.toOuterMeasure (f ⁻¹' A) ≤ μβ.toOuterMeasure A := by
  calc
    μα.toOuterMeasure (f ⁻¹' A) ≤
        μα.toOuterMeasure (f ⁻¹' toMeasurable μβ A) :=
      μα.toOuterMeasure.mono (preimage_mono (subset_toMeasurable μβ A))
    _ = μα (f ⁻¹' toMeasurable μβ A) := by
      rw [Measure.toOuterMeasure_apply]
    _ = μβ (toMeasurable μβ A) :=
      hf.measure_preimage (measurableSet_toMeasurable μβ A).nullMeasurableSet
    _ = μβ.toOuterMeasure A := by
      rw [Measure.toOuterMeasure_apply, measure_toMeasurable]

private theorem planeCoords_preimage_coordAnnulusSector
    (o : Plane) (r0 rho : ℝ) (Θ : Set ℝ) :
    planeCoords ⁻¹' coordAnnulusSector (planeCoords o) r0 rho Θ =
      euclideanAnnulusSector o r0 rho Θ := by
  ext z
  simp only [mem_preimage, coordAnnulusSector, euclideanAnnulusSector, mem_setOf_eq]
  constructor
  · rintro ⟨r, hr, θ, hθ, heq⟩
    refine ⟨r, hr, θ, hθ, ?_⟩
    apply planeCoords.injective
    apply Prod.ext
    · simpa [planeCoords, polarPoint, scaleCoordinatePlane, unitDirection,
        angleVector] using congrArg Prod.fst heq
    · simpa [planeCoords, polarPoint, scaleCoordinatePlane, unitDirection,
        angleVector] using congrArg Prod.snd heq
  · rintro ⟨r, hr, θ, hθ, rfl⟩
    refine ⟨r, hr, θ, hθ, ?_⟩
    have h0 : Matrix.vecHead o.ofLp = o.ofLp 0 := rfl
    have h1 : Matrix.vecHead (Matrix.vecTail o.ofLp) = o.ofLp 1 := rfl
    apply Prod.ext <;>
      simp [planeCoords, polarPoint, scaleCoordinatePlane, unitDirection, angleVector,
        h0, h1]

private theorem euclideanAnnulusSector_outerMeasure_ge (o : Plane) {r0 rho : ℝ}
    (hr0 : 0 ≤ r0) (hle : r0 ≤ rho) (Θ : Set ℝ) :
    ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) * angleSetOuter Θ ≤
      volume.toOuterMeasure (euclideanAnnulusSector o r0 rho Θ) := by
  refine (coordAnnulusSector_outerMeasure_ge (planeCoords o) hr0 hle Θ).trans ?_
  have h := outerMeasure_preimage_le_of_measurePreserving
    planeCoords_measurePreserving.symm (euclideanAnnulusSector o r0 rho Θ)
  rw [show planeCoords.symm ⁻¹' euclideanAnnulusSector o r0 rho Θ =
      coordAnnulusSector (planeCoords o) r0 rho Θ by
    rw [← planeCoords_preimage_coordAnnulusSector]
    ext z
    simp] at h
  exact h

/-- **`PROOF.md` (B5): the annular fan bound.**  The exterior part of a closed
polar sector has at least the expected annular polar area.  The angle set `Θ`
is arbitrary and in particular **not** assumed measurable — legitimate because
this is a lower bound, exactly as for `euclideanPolarSector_outerMeasure_ge`. -/
theorem euclideanPolarAnnulus_outerMeasure_ge (o : Plane) {r0 rho : ℝ}
    (hr0 : 0 ≤ r0) (hle : r0 ≤ rho) (Θ : Set ℝ) :
    ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) * angleSetOuter Θ ≤
      volume.toOuterMeasure
        (euclideanPolarSector o rho Θ \ Metric.closedBall o r0) := by
  refine (euclideanAnnulusSector_outerMeasure_ge o hr0 hle Θ).trans ?_
  apply volume.toOuterMeasure.mono
  rintro z ⟨r, hr, θ, hθ, rfl⟩
  have hrnn : 0 ≤ r := hr0.trans hr.1.le
  have hdist : dist (o + r • angleVector θ) o = r := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_angleVector, mul_one,
      Real.norm_eq_abs, abs_of_nonneg hrnn]
  refine ⟨⟨r, ⟨hrnn, hr.2⟩, θ, hθ, rfl⟩, ?_⟩
  rw [Metric.mem_closedBall, hdist]
  exact not_le.2 hr.1

namespace StarShapedKakeya

variable {E : Set Plane} (K : StarShapedKakeya E)

/-- **The residual annular fan.**  Exterior analogue of
`residualFan_outerMeasure_lower`: the oriented-lift bookkeeping
(`residualAngles`, `directionAngleOuter_le_residualAngles`) and the cut-point
handling (`residualAngles_outerMeasure_le_angleSetOuter`) are reused verbatim;
only the planar bound is replaced by the annular one. -/
theorem residualFan_annulus_outerMeasure_lower
    {r0 rho : ℝ} (hr0 : 0 ≤ r0) (hle : r0 ≤ rho) (hrho : 0 < rho)
    (R : Set Direction)
    (hzero : ∀ theta ∈ R, (K.needleFamily theta).height K.center = 0)
    (hout : ∀ theta ∈ R, (K.needleFamily theta).OutsideBall rho K.center) :
    ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) * directionAngleOuter R ≤
      volume.toOuterMeasure
        (residualFan K R \ Metric.closedBall K.center r0) := by
  calc
    ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) * directionAngleOuter R ≤
        ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) *
          volume.toOuterMeasure (residualAngles K R) :=
      mul_le_mul' le_rfl (K.directionAngleOuter_le_residualAngles hrho R hzero hout)
    _ ≤ ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) *
          angleSetOuter (residualAngles K R) :=
      mul_le_mul' le_rfl (K.residualAngles_outerMeasure_le_angleSetOuter R)
    _ ≤ volume.toOuterMeasure
          (euclideanPolarSector K.center rho (residualAngles K R) \
            Metric.closedBall K.center r0) :=
      euclideanPolarAnnulus_outerMeasure_ge K.center hr0 hle _
    _ ≤ volume.toOuterMeasure
          (residualFan K R \ Metric.closedBall K.center r0) :=
      volume.toOuterMeasure.mono (diff_subset_diff_left
        (K.polarSector_residualAngles_subset_residualFan hrho R hout))

end StarShapedKakeya

namespace FiniteFixedSelection

variable {height H : Direction → ℝ} {m a : ℝ} {A : Set Direction}

/-- The restricted fan and the restricted selected union stay disjoint:
`PROOF.md` (B3) survives deletion of a common set. -/
theorem disjoint_restrictedResidualFan_restrictedSelectedUnion
    (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (hbound : ∀ θ ∈ A, height θ ≤ a)
    {E : Set Plane} (K : StarShapedKakeya E) {rho : ℝ} (hrho : 0 < rho)
    (hzero : ∀ theta ∈ F.residual,
      (K.needleFamily theta).height K.center = 0)
    (hheight : ∀ θ, height θ = (K.needleFamily θ).height K.center)
    (hpos : ∀ i, 0 < height (F.selected i))
    (hscaled : ∀ i, height (F.selected i) < m * rho)
    (hH : ∀ i, H (F.selected i) =
      Real.arcsin (height (F.selected i) / (m * rho)))
    (hout : ∀ θ ∈ A, (K.needleFamily θ).OutsideBall rho K.center)
    (r0 : ℝ) :
    Disjoint (residualFan K F.residual \ Metric.closedBall K.center r0)
      (F.restrictedSelectedUnion K r0) := by
  rw [F.restrictedSelectedUnion_eq K r0]
  exact (F.disjoint_residualFan_selectedTriangleUnion hm0 hm1 hbound K hrho hzero
    hheight hpos hscaled hH hout).mono diff_subset diff_subset

/-- **`PROOF.md` (8.3b): the finite full exterior geometric bound.**  The
restricted residual fan and the finite sum over the restricted **open**
selected triangles are added by Carathéodory separation inside
`E \ closedBall K.center r0`. -/
theorem geometric_exterior_outerMeasure_lower_finite
    (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (hbound : ∀ θ ∈ A, height θ ≤ a)
    {E : Set Plane} (K : StarShapedKakeya E) {rho r0 : ℝ}
    (hr0 : 0 ≤ r0) (hle : r0 ≤ rho) (hrho : 0 < rho)
    (hzero : ∀ theta ∈ F.residual,
      (K.needleFamily theta).height K.center = 0)
    (hheight : ∀ θ, height θ = (K.needleFamily θ).height K.center)
    (hpos : ∀ i, 0 < height (F.selected i))
    (hscaled : ∀ i, height (F.selected i) < m * rho)
    (hH : ∀ i, H (F.selected i) =
      Real.arcsin (height (F.selected i) / (m * rho)))
    (hout : ∀ θ ∈ A, (K.needleFamily θ).OutsideBall rho K.center) :
    ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) * directionAngleOuter F.residual +
        ∑ i : Fin F.N, volume (F.restrictedTriangle K r0 i) ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0) := by
  have hfan := K.residualFan_annulus_outerMeasure_lower hr0 hle hrho F.residual
    hzero (fun theta htheta => hout theta (F.residual_subset_initial htheta))
  have hpair := F.pairwise_disjoint_restrictedTriangle hm0 hm1 hbound K hrho
    hheight hpos hscaled hH hout r0
  have hdisj := F.disjoint_restrictedResidualFan_restrictedSelectedUnion hm0 hm1
    hbound K hrho hzero hheight hpos hscaled hH hout r0
  have hadd : volume (residualFan K F.residual \ Metric.closedBall K.center r0) +
      volume (F.restrictedSelectedUnion K r0) ≤
        volume (E \ Metric.closedBall K.center r0) :=
    outerMeasure_add_le_of_disjoint_measurable
      (F.measurableSet_restrictedSelectedUnion K r0) hdisj
      (diff_subset_diff_left (K.residualFan_subset F.residual))
      (F.restrictedSelectedUnion_subset K r0)
  rw [Measure.toOuterMeasure_apply]
  calc
    ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) * directionAngleOuter F.residual +
          ∑ i : Fin F.N, volume (F.restrictedTriangle K r0 i)
        = ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) *
            directionAngleOuter F.residual +
          volume (F.restrictedSelectedUnion K r0) := by
      rw [F.volume_restrictedSelectedUnion K r0 hpair]
    _ ≤ volume (residualFan K F.residual \ Metric.closedBall K.center r0) +
          volume (F.restrictedSelectedUnion K r0) := by
      refine add_le_add ?_ le_rfl
      rw [← Measure.toOuterMeasure_apply]
      exact hfan
    _ ≤ volume (E \ Metric.closedBall K.center r0) := hadd

end FiniteFixedSelection

/-- **Coefficient elimination with a `min`** (`PROOF.md` Prop. 8.1).  Unlike
`caseII_round2_initial_angle_lower_bound` this does **not** compare the payment
coefficient with the fan coefficient: the two are combined by an explicit
minimum, so no `ρ ≤ 1` / `ρ > 1/2` hypothesis is needed, and there is no `κ`. -/
theorem round2_min_initial_angle_lower_bound
    {q p s L R B b M : ENNReal}
    (hqs : q ≤ s) (hqp : q ≤ p) (hcover : L ≤ R + B)
    (hpayment : p * B ≤ b) (hgeom : s * R + b ≤ M) : q * L ≤ M := by
  calc
    q * L ≤ q * (R + B) := mul_le_mul' le_rfl hcover
    _ = q * R + q * B := mul_add q R B
    _ ≤ s * R + p * B :=
      add_le_add (mul_le_mul' hqs le_rfl) (mul_le_mul' hqp le_rfl)
    _ ≤ s * R + b := add_le_add le_rfl hpayment
    _ ≤ M := hgeom

/-- **M3b exit theorem.**  Finite-selection exterior lower bound with the
coefficient `min (C_ext / 4) ((ρ² - r₀²)/2)`, no `κ`, and `hCext` explicit.
Everything used is finite: the deletion coverage budget
`initial_directionAngleOuter_le_residual_add_cost`, the M3a payment, the M3b
annular fan, and the finite Carathéodory ledger.  Nothing from M4 is used. -/
theorem annular_exterior_lower_bound_of_finiteSelection
    {height H : Direction → ℝ} {m a r0 rho : ℝ} {A : Set Direction}
    {E : Set Plane} (K : StarShapedKakeya E)
    (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (ha : 0 < a) (harho : a < m * rho)
    (hr0 : 0 < r0) (hlt : r0 < rho)
    (hCext : 0 < annularCExt a r0 rho m)
    (hheight : ∀ θ, height θ = (K.needleFamily θ).height K.center)
    (hH : ∀ θ, H θ = Real.arcsin (height θ / (m * rho)))
    (hout : ∀ θ ∈ A, (K.needleFamily θ).OutsideBall rho K.center)
    (hlow : ∀ θ ∈ A, (K.needleFamily θ).height K.center < a) :
    ENNReal.ofReal (min (annularCExt a r0 rho m / 4) ((rho ^ 2 - r0 ^ 2) / 2)) *
        directionAngleOuter A ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0) := by
  have hrho : 0 < rho := lt_trans hr0 hlt
  have hheight0 : ∀ θ, 0 ≤ height θ := by
    intro θ
    rw [hheight]
    exact UnitNeedle.height_nonneg _ _
  have hbound : ∀ θ ∈ A, height θ ≤ a := by
    intro θ hθ
    rw [hheight]
    exact (hlow θ hθ).le
  have hmem : ∀ i : Fin F.N, F.selected i ∈ A :=
    fun i => F.selected_mem_initial hm0 hm1 hbound i
  have hpos : ∀ i : Fin F.N, 0 < height (F.selected i) := by
    intro i
    have hd := chooseAbove_dominates hm0 hm1
      (fixedGreedyRemaining_subset height H m A i) hbound (F.positive_before i)
      (F.selected_mem hm0 hm1 hbound i)
    have heq : chooseAbove height m (fixedGreedyRemaining height H m A i) =
        F.selected i := (F.selected_eq i).symm
    rw [heq] at hd
    nlinarith [hheight0 (F.selected i)]
  have hscaled : ∀ i : Fin F.N, height (F.selected i) < m * rho := by
    intro i
    rw [hheight]
    exact lt_trans (hlow _ (hmem i)) harho
  have hHi : ∀ i : Fin F.N, H (F.selected i) =
      Real.arcsin (height (F.selected i) / (m * rho)) := fun i => hH _
  have hzero : ∀ theta ∈ F.residual,
      (K.needleFamily theta).height K.center = 0 := by
    intro θ hθ
    have h := F.residual_height_zero hheight0 hbound θ hθ
    rwa [hheight] at h
  have hH0 : ∀ i : Fin F.N, 0 ≤ H (F.selected i) := by
    intro i
    rw [hHi i]
    exact Real.arcsin_nonneg.2 (div_nonneg (hheight0 _) (mul_pos hm0 hrho).le)
  have hcover := F.initial_directionAngleOuter_le_residual_add_cost hH0
  rw [tsum_fintype] at hcover
  exact round2_min_initial_angle_lower_bound
    (ENNReal.ofReal_le_ofReal (min_le_right _ _))
    (ENNReal.ofReal_le_ofReal (min_le_left _ _)) hcover
    (F.quarter_cost_le_sum_volume_restrictedTriangle hm0 hm1 hbound K ha harho
      hr0 hlt hCext hheight hpos hHi hout)
    (F.geometric_exterior_outerMeasure_lower_finite hm0 hm1 hbound K hr0.le
      hlt.le hrho hzero hheight hpos hscaled hHi hout)

/-- Canonical specialization of the M3b exit theorem: once a finite selection
is supplied, instantiating `height` and `H` by the actual needle height and the
paper weight `H(δ) = arcsin (δ / (m ρ))` satisfies both defining equations
definitionally. This theorem does not assert that the finite branch occurs. -/
theorem annular_exterior_lower_bound_of_finiteSelection_paperWeight
    {E : Set Plane} (K : StarShapedKakeya E) {A : Set Direction} {a r0 rho m : ℝ}
    (F : FiniteFixedSelection (fun θ => (K.needleFamily θ).height K.center)
      (fun θ => Real.arcsin ((K.needleFamily θ).height K.center / (m * rho))) m A)
    (hm0 : 0 < m) (hm1 : m < 1) (ha : 0 < a) (harho : a < m * rho)
    (hr0 : 0 < r0) (hlt : r0 < rho)
    (hCext : 0 < annularCExt a r0 rho m)
    (hout : ∀ θ ∈ A, (K.needleFamily θ).OutsideBall rho K.center)
    (hlow : ∀ θ ∈ A, (K.needleFamily θ).height K.center < a) :
    ENNReal.ofReal (min (annularCExt a r0 rho m / 4) ((rho ^ 2 - r0 ^ 2) / 2)) *
        directionAngleOuter A ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0) :=
  annular_exterior_lower_bound_of_finiteSelection K F hm0 hm1 ha harho hr0 hlt
    hCext (fun _ => rfl) (fun _ => rfl) hout hlow

end

end StarKakeyaLower
