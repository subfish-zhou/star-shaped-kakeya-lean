import StarKakeyaLower.PolarProjectiveOuter
import StarKakeyaLower.LiNeedleAdapter

/-!
# The generic radial core of the Case I estimate

This module holds the parameter-free part of the Case I confined estimate: the
containment/mass interface, the aggregate first-arc comparison, the raw needle
family, the origin-centred coordinate disks, and the two radial integral
theorems `outerMeasure_inner_ge_caseI_lintegral_of_raw` and
`outerMeasure_ge_caseI_lintegral`.

Everything here was previously the front section of
`StarKakeyaLower.CaseIAssemblyConditional`; the declarations were *moved*, not
copied, so there is exactly one semantic track and every old name resolves to
the declaration below.  The point of the move is the import closure: this module
imports only `PolarProjectiveOuter` and `LiNeedleAdapter`, neither of which
carries the frozen witness constants of `StarKakeyaLower.StrongerKernel`.
-/

open Set MeasureTheory Real
open scoped ENNReal

namespace StarKakeyaLower

noncomputable section

/-- The containment input, one of three substantive inputs at one radius.  The set `A` is the
relevant family of unoriented directions; `x i` and `rad i` are the centre and
half-span of its selected first polar arc. -/
def LiFamilyContainment {ι : Type*} (A : Set ProjectiveDirection)
    (g : ℝ) (x rad : ι → ℝ) : Prop :=
  A ⊆ ⋃ i, quotientCenteredDilate g Real.pi (x i) (rad i)

/-- Direction mass is always the outer measure of the literal direction set;
there is no measurable-selector assumption hidden in this abbreviation. -/
def directionOuterMass (A : Set ProjectiveDirection) : ℝ≥0∞ :=
  volume.toOuterMeasure A

/-- The independent critical-endpoint conclusion. -/
def JGammaCriticalContainment {r : ℝ} (F : DirectionNeedleFamily r)
    (Γ : Set PolarAngle) (g : ℝ) : Prop :=
  F.JGamma Γ ⊆ F.selectedDilatedUnion Γ g

/-- Open positive-span containment used by the quotient Haar-growth theorem.
It is kept separate because closed endpoint containment also covers radius zero. -/
def JGammaOpenCriticalContainment {r : ℝ} (F : DirectionNeedleFamily r)
    (Γ : Set PolarAngle) (g : ℝ) : Prop :=
  F.JGamma Γ ⊆ F.selectedOpenDilatedUnion Γ g

/-- Radius-zero endpoint containment.  The centre identity is exactly the
pointwise conclusion of
`supportTraceFirstArcData?_zeroHeight_projectiveCenter_radius`. -/
theorem jGammaCriticalContainment_of_zeroRadius
    {r g : ℝ} {F : DirectionNeedleFamily r} {Γ : Set PolarAngle}
    (hzero : ∀ d ∈ F.JGamma Γ,
      (((F.firstCenter d : ℝ) : ProjectiveDirection) = d ∧
        F.firstRadius d = 0)) :
    JGammaCriticalContainment F Γ g := by
  intro d hd
  rw [DirectionNeedleFamily.selectedDilatedUnion, Set.mem_iUnion]
  refine ⟨⟨d, hd⟩, ?_⟩
  rcases hzero d hd with ⟨hc, hr⟩
  rw [hr]
  simp only [quotientClosedCenteredDilate, quotientClosedInterval]
  have hpi : ¬ Real.pi ≤
      (F.firstCenter d + g * 0) - (F.firstCenter d - g * 0) := by
    simpa using (not_le_of_gt Real.pi_pos)
  rw [if_neg hpi]
  exact ⟨F.firstCenter d, by simp, hc⟩

/-- Total fixed-radius endpoint dispatch.  The printed contact classification is
used only in the explicitly positive branch; zero height is discharged by the
singleton/radius-zero theorem above. -/
theorem jGammaCriticalContainment_zero_or_positive
    {r g : ℝ} {F : DirectionNeedleFamily r} {Γ : Set PolarAngle}
    (hclass :
      (∀ d ∈ F.JGamma Γ,
        (((F.firstCenter d : ℝ) : ProjectiveDirection) = d ∧
          F.firstRadius d = 0)) ∨
      (∀ d ∈ F.JGamma Γ, 0 < (F.needle d).height))
    (hpositive : (∀ d ∈ F.JGamma Γ, 0 < (F.needle d).height) →
      JGammaCriticalContainment F Γ g) :
    JGammaCriticalContainment F Γ g := by
  rcases hclass with hzero | hpos
  · exact jGammaCriticalContainment_of_zeroRadius hzero
  · exact hpositive hpos

/-! ## Aggregate pointwise first-arc family -/

/-- The target `Γ_d` is exactly the carrier of `d`'s selected first arc. -/
def DirectionNeedleFamily.firstArcTarget {r : ℝ} (F : DirectionNeedleFamily r)
    (d : ProjectiveDirection) : Set PolarAngle := (F.firstArc d).carrier

/-- Every direction belongs to the `JΓ` class of its own target. -/
theorem DirectionNeedleFamily.mem_JGamma_firstArcTarget {r : ℝ}
    (F : DirectionNeedleFamily r) (d : ProjectiveDirection) :
    d ∈ F.JGamma (F.firstArcTarget d) := by
  exact Set.Subset.rfl

/-- The literal aggregate cover `A ⊆ ⋃ d ∈ A, J(Γ_d)`. -/
theorem DirectionNeedleFamily.subset_iUnion_JGamma_firstArcTarget {r : ℝ}
    (F : DirectionNeedleFamily r) (A : Set ProjectiveDirection) :
    A ⊆ ⋃ d : A, F.JGamma (F.firstArcTarget d) := by
  intro d hd
  exact Set.mem_iUnion_of_mem (⟨d, hd⟩ : A) (F.mem_JGamma_firstArcTarget d)

/-- Zero-safe critical containment is pointwise in the target `Γ_d`.  Positive
spans use the open dilation needed by Haar growth, while a zero span uses the
closed singleton at its centre.  No positivity of all selected spans is
assumed.

The class `A` is intersected with
`JΓ`: the radius containment of a chosen triangle is known only for directions
of `A` and must not be applied to an arbitrary member of `JΓ`.  The aggregate
cover below uses the contract only at `d ∈ A` itself, so nothing is lost. -/
def FirstArcPointwiseHybridCriticalContainment {r : ℝ}
    (F : DirectionNeedleFamily r) (A : Set ProjectiveDirection) (g : ℝ) : Prop :=
  ∀ d ∈ A, A ∩ F.JGamma (F.firstArcTarget d) ⊆
    quotientHybridCenteredDilate g Real.pi (F.firstCenter d) (F.firstRadius d)

/-- Assemble the hybrid contract from exactly its two legitimate endpoint
branches: open containment at positive span and singleton containment at zero
span. -/
theorem firstArcPointwiseHybridCriticalContainment_of_branches
    {r g : ℝ} {F : DirectionNeedleFamily r} {A : Set ProjectiveDirection}
    (hzero : ∀ d ∈ A, F.firstRadius d = 0 →
      A ∩ F.JGamma (F.firstArcTarget d) ⊆
        {((F.firstCenter d : ℝ) : ProjectiveDirection)})
    (hpositive : ∀ d ∈ A, 0 < F.firstRadius d →
      A ∩ F.JGamma (F.firstArcTarget d) ⊆
        quotientCenteredDilate g Real.pi (F.firstCenter d) (F.firstRadius d)) :
    FirstArcPointwiseHybridCriticalContainment F A g := by
  intro d hd
  rcases (F.firstRadius_nonneg d).eq_or_lt with hrad | hrad
  · simpa [quotientHybridCenteredDilate, hrad] using hzero d hd hrad.symm
  · simpa [quotientHybridCenteredDilate, ne_of_gt hrad] using hpositive d hd hrad

/-- The hybrid first-arc base projects into the actual closed selected carrier,
including the radius-zero singleton. -/
theorem DirectionNeedleFamily.quotientHybrid_firstArc_subset_projected_carrier
    {r : ℝ} (F : DirectionNeedleFamily r) (d : ProjectiveDirection) :
    quotientHybridCenteredArc Real.pi (F.firstCenter d) (F.firstRadius d) ⊆
      polarToProjective '' (F.firstArc d).carrier := by
  by_cases hzero : F.firstRadius d = 0
  · rw [quotientHybridCenteredArc, if_pos hzero]
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst q
    refine ⟨((F.firstArc d).lo : PolarAngle),
      (F.firstArc d).endpoints_mem_carrier.1, ?_⟩
    have heq : (F.firstArc d).hi = (F.firstArc d).lo := by
      dsimp [DirectionNeedleFamily.firstRadius] at hzero
      linarith
    rw [DirectionNeedleFamily.firstCenter, heq]
    ring_nf
    rfl
  · rw [quotientHybridCenteredArc, if_neg hzero]
    exact F.quotient_firstArc_subset_projected_carrier d

/-- Union of the zero-safe undilated first-arc bases indexed by `A`. -/
def DirectionNeedleFamily.aggregateBaseUnion {r : ℝ}
    (F : DirectionNeedleFamily r) (A : Set ProjectiveDirection) :
    Set ProjectiveDirection :=
  ⋃ d : A, quotientHybridCenteredArc Real.pi (F.firstCenter d) (F.firstRadius d)

/-- Own-target membership converts pointwise critical containment into the
aggregate dilated cover. -/
theorem DirectionNeedleFamily.aggregate_dilated_cover {r g : ℝ}
    (F : DirectionNeedleFamily r) (A : Set ProjectiveDirection)
    (hcritical : FirstArcPointwiseHybridCriticalContainment F A g) :
    A ⊆ ⋃ d : A,
      quotientHybridCenteredDilate g Real.pi (F.firstCenter d) (F.firstRadius d) := by
  intro d hd
  exact Set.mem_iUnion_of_mem (⟨d, hd⟩ : A)
    (hcritical d hd ⟨hd, F.mem_JGamma_firstArcTarget d⟩)

/-- The aggregate first-arc bases are contained in the actual radial section. -/
theorem DirectionNeedleFamily.aggregateBaseUnion_volume_le_angleOuter
    {r : ℝ} (F : DirectionNeedleFamily r) (A : Set ProjectiveDirection)
    (E : Set CoordinatePlane)
    (htri : ∀ d : ProjectiveDirection, (F.needle d).triangle ⊆ E) :
    volume (F.aggregateBaseUnion A) ≤ angleOuter E r := by
  let Γ : Set PolarAngle := ⋃ d : A, F.firstArcTarget d
  have hsub : F.aggregateBaseUnion A ⊆
      polarToProjective '' F.selectedPolarUnion Γ := by
    intro z hz
    rw [DirectionNeedleFamily.aggregateBaseUnion, Set.mem_iUnion] at hz
    obtain ⟨d, hd⟩ := hz
    obtain ⟨θ, hθ, rfl⟩ :=
      F.quotientHybrid_firstArc_subset_projected_carrier d hd
    refine ⟨θ, ?_, rfl⟩
    exact Set.mem_iUnion_of_mem
      (⟨d, fun φ hφ => Set.mem_iUnion_of_mem d hφ⟩ : F.JGamma Γ) hθ
  calc
    volume (F.aggregateBaseUnion A) ≤
        volume (polarToProjective '' F.selectedPolarUnion Γ) := measure_mono hsub
    _ ≤ volume.toOuterMeasure (polarCarrierCut (F.selectedPolarUnion Γ)) :=
      volume_projectedPolar_le_cutOuter _
    _ ≤ volume.toOuterMeasure (polarAngleSection E r) :=
      measure_mono (F.polarCarrierCut_selected_subset_angleSection Γ E htri)
    _ = angleOuter E r := rfl

/-- Critical containment in the generic quotient API. -/
theorem DirectionNeedleFamily.liFamilyContainment_of_critical
    {r g : ℝ} {F : DirectionNeedleFamily r} {Γ : Set PolarAngle}
    (hcritical : JGammaOpenCriticalContainment F Γ g) :
    LiFamilyContainment (F.JGamma Γ) g
      (fun d : F.JGamma Γ => F.firstCenter d)
      (fun d : F.JGamma Γ => F.firstRadius d) :=
  hcritical

/-- The conditional quotient-dilation consequence of the three substantive
inputs: containment (`hLi`), direction mass (`hmass`), and the base-arcs section
comparison (`hbase`).  None is an area conclusion. -/
theorem angleOuter_ge_of_liFamilyContainment
    {ι : Type*} {E : Set CoordinatePlane} {rho g : ℝ}
    {A : Set ProjectiveDirection} {x rad : ι → ℝ} {q : ℝ≥0∞}
    (hg : 1 ≤ g) (hrad : ∀ i, 0 ≤ rad i)
    (hLi : LiFamilyContainment A g x rad)
    (hmass : ENNReal.ofReal g * q ≤ volume A)
    (hbase : volume (⋃ i, quotientCenteredArc Real.pi (x i) (rad i)) ≤
      angleOuter E rho) :
    q ≤ angleOuter E rho := by
  have hcover : volume A ≤
      volume (⋃ i, quotientCenteredDilate g Real.pi (x i) (rad i)) :=
    measure_mono hLi
  have hdilate :
      volume (⋃ i, quotientCenteredDilate g Real.pi (x i) (rad i)) ≤
        ENNReal.ofReal g *
          volume (⋃ i, quotientCenteredArc Real.pi (x i) (rad i)) :=
    volume_iUnion_quotientCenteredDilate_le g Real.pi hg x rad hrad
  have hmul : ENNReal.ofReal g * q ≤
      ENNReal.ofReal g * angleOuter E rho :=
    hmass.trans (hcover.trans (hdilate.trans (mul_le_mul_left' hbase _)))
  exact (ENNReal.mul_le_mul_left
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))) ENNReal.ofReal_ne_top).mp hmul

/-- Aggregate fixed-radius estimate.  The arbitrary-family quotient-circle
inequality is the completed finite/infinite/`⊤` form of the epsilon-greedy
interval argument.  It is stronger than the paper's enlargement factor
`2/(1-ε)+1`; consequently the limiting factor `3` can be paid in the chosen
minorant `q` without any finiteness or measurability assumption. -/
theorem angleOuter_ge_of_firstArcPointwiseAggregate
    {E : Set CoordinatePlane} {r g : ℝ} {q : ℝ≥0∞}
    (F : DirectionNeedleFamily r) (A : Set ProjectiveDirection)
    (hg : 1 ≤ g)
    (hmass : ENNReal.ofReal g * q ≤ directionOuterMass A)
    (hcritical : FirstArcPointwiseHybridCriticalContainment F A g)
    (htri : ∀ d : ProjectiveDirection, (F.needle d).triangle ⊆ E) :
    q ≤ angleOuter E r := by
  have hcover : directionOuterMass A ≤
      volume (⋃ d : A, quotientHybridCenteredDilate g Real.pi
        (F.firstCenter d) (F.firstRadius d)) :=
    measure_mono (F.aggregate_dilated_cover A hcritical)
  have hdilate := volume_iUnion_quotientHybridCenteredDilate_le
    g Real.pi hg (fun d : A => F.firstCenter d)
    (fun d : A => F.firstRadius d) (fun d => F.firstRadius_nonneg d)
  have hbase := F.aggregateBaseUnion_volume_le_angleOuter A E htri
  have hmul : ENNReal.ofReal g * q ≤
      ENNReal.ofReal g * angleOuter E r :=
    hmass.trans (hcover.trans (hdilate.trans (mul_le_mul_left' hbase _)))
  exact (ENNReal.mul_le_mul_left
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))) ENNReal.ofReal_ne_top).mp hmul

/-! ## Raw family assembly and the literal inner set -/

/-- Attach first-arc trace data at one fixed radius.  The quantifier is
intentionally only over directions: callers supply this datum separately for
each radius at which it is needed.  Genuine data (rather than mere
nonemptiness) is required so that the selected arc of the resulting family is
literally the caller's arc, and hence literally the trace selector's output. -/
def directionNeedleFamilyOfRaw
    (N : (d : ProjectiveDirection) → DirectionNeedle d) {r : ℝ}
    (htrace : ∀ d, FirstArcData (N d).triangle r) :
    DirectionNeedleFamily r where
  needle := N
  arcData d := htrace d

@[simp] theorem directionNeedleFamilyOfRaw_needle
    (N : (d : ProjectiveDirection) → DirectionNeedle d) {r : ℝ}
    (htrace : ∀ d, FirstArcData (N d).triangle r) (d : ProjectiveDirection) :
    (directionNeedleFamilyOfRaw N htrace).needle d = N d := rfl

@[simp] theorem directionNeedleFamilyOfRaw_arcData
    (N : (d : ProjectiveDirection) → DirectionNeedle d) {r : ℝ}
    (htrace : ∀ d, FirstArcData (N d).triangle r) (d : ProjectiveDirection) :
    (directionNeedleFamilyOfRaw N htrace).arcData d = htrace d := rfl

/-- The literal union `E_A` from Li (2.3). -/
def directionTriangleUnion
    (N : (d : ProjectiveDirection) → DirectionNeedle d)
    (A : Set ProjectiveDirection) : Set CoordinatePlane :=
  ⋃ d : A, (N d).triangle

/-- The open origin-centred Euclidean disk used in Li's Lemma 2.5.  It is
written using the Euclidean radius squared (rather than the product metric on
`ℝ × ℝ`) so the interface agrees literally with the paper's open ball. -/
def originOpenDisk (r₀ : ℝ) : Set CoordinatePlane :=
  {z | z.1 ^ 2 + z.2 ^ 2 < r₀ ^ 2}

/-- The corresponding closed Euclidean disk.  This form is useful for the
radial integral because it retains the endpoint radius. -/
def originClosedDisk (r₀ : ℝ) : Set CoordinatePlane :=
  {z | z.1 ^ 2 + z.2 ^ 2 ≤ r₀ ^ 2}

/-- The Euclidean circle bounding the two origin-centred disks. -/
def originSphere (r₀ : ℝ) : Set CoordinatePlane :=
  {z | z.1 ^ 2 + z.2 ^ 2 = r₀ ^ 2}

/-- The only points gained by closing the open disk lie on its circle. -/
theorem originClosedDisk_diff_originOpenDisk_subset_sphere (r₀ : ℝ) :
    originClosedDisk r₀ \ originOpenDisk r₀ ⊆ originSphere r₀ := by
  intro z hz
  exact le_antisymm hz.1 (le_of_not_gt hz.2)

/-- A Euclidean circle has zero planar Lebesgue volume.  We prove this directly
in `ℝ × ℝ`: every vertical fibre has at most two points, then use the product
measure null-set criterion. -/
theorem volume_originSphere (r₀ : ℝ) : volume (originSphere r₀) = 0 := by
  have hsphere : MeasurableSet (originSphere r₀) := by
    exact (isClosed_eq
      ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const).measurableSet
  have hfiber : ∀ x : ℝ, volume (Prod.mk x ⁻¹' originSphere r₀) = 0 := by
    intro x
    by_cases h : 0 ≤ r₀ ^ 2 - x ^ 2
    · apply measure_mono_null
        (t := {Real.sqrt (r₀ ^ 2 - x ^ 2), -Real.sqrt (r₀ ^ 2 - x ^ 2)})
      · intro y hy
        change x ^ 2 + y ^ 2 = r₀ ^ 2 at hy
        simp only [mem_insert_iff, mem_singleton_iff]
        have hy2 : y ^ 2 = (Real.sqrt (r₀ ^ 2 - x ^ 2)) ^ 2 := by
          rw [sq_sqrt h]
          linarith
        exact sq_eq_sq_iff_eq_or_eq_neg.mp hy2
      · exact measure_union_null Real.volume_singleton Real.volume_singleton
    · have hempty : Prod.mk x ⁻¹' originSphere r₀ = ∅ := by
        ext y
        simp only [originSphere, mem_preimage, mem_setOf_eq, mem_empty_iff_false,
          iff_false]
        intro hy
        apply h
        nlinarith [sq_nonneg y]
      rw [hempty, measure_empty]
  have hp : (volume.prod volume) (originSphere r₀) = 0 :=
    (Measure.measure_prod_null hsphere).2 (Filter.Eventually.of_forall hfiber)
  simpa only [← Measure.volume_eq_prod] using hp

/-- The circle is also null for the outer measure induced by planar volume. -/
theorem outerMeasure_originSphere (r₀ : ℝ) :
    volume.toOuterMeasure (originSphere r₀) = 0 := by
  rw [Measure.toOuterMeasure_apply, volume_originSphere]

/-- Intersecting an arbitrary (not necessarily measurable) planar set with the
open or closed origin disk gives the same outer measure. -/
theorem outerMeasure_inter_originOpenDisk_eq_closedDisk
    (E : Set CoordinatePlane) (r₀ : ℝ) :
    volume.toOuterMeasure (E ∩ originOpenDisk r₀) =
      volume.toOuterMeasure (E ∩ originClosedDisk r₀) := by
  apply le_antisymm
  · apply OuterMeasure.mono
    intro z hz
    refine ⟨hz.1, ?_⟩
    change z.1 ^ 2 + z.2 ^ 2 ≤ r₀ ^ 2
    exact le_of_lt hz.2
  · calc
      volume.toOuterMeasure (E ∩ originClosedDisk r₀) ≤
          volume.toOuterMeasure ((E ∩ originOpenDisk r₀) ∪ originSphere r₀) := by
            apply OuterMeasure.mono
            intro z hz
            by_cases hopen : z ∈ originOpenDisk r₀
            · exact Or.inl ⟨hz.1, hopen⟩
            · exact Or.inr (originClosedDisk_diff_originOpenDisk_subset_sphere r₀
                ⟨hz.2, hopen⟩)
      _ ≤ volume.toOuterMeasure (E ∩ originOpenDisk r₀) +
          volume.toOuterMeasure (originSphere r₀) := measure_union_le _ _
      _ = volume.toOuterMeasure (E ∩ originOpenDisk r₀) := by
        rw [outerMeasure_originSphere, add_zero]

/-- Every triangle in the full direction union is literally contained in it. -/
theorem triangle_subset_directionTriangleUnion_univ
    (N : (d : ProjectiveDirection) → DirectionNeedle d) (d : ProjectiveDirection) :
    (N d).triangle ⊆ directionTriangleUnion N Set.univ := by
  intro z hz
  exact Set.mem_iUnion_of_mem (⟨d, Set.mem_univ d⟩ : (Set.univ : Set ProjectiveDirection)) hz

/-- At a radius in `[0,r₀]`, passing from the full triangle union to its literal
inner disk does not lose any angular section. -/
theorem angleOuter_directionTriangleUnion_le_inner
    (N : (d : ProjectiveDirection) → DirectionNeedle d) {r r₀ : ℝ}
    (hr : r ∈ Icc (0 : ℝ) r₀) :
    angleOuter (directionTriangleUnion N Set.univ) r ≤
      angleOuter (directionTriangleUnion N Set.univ ∩ originClosedDisk r₀) r := by
  apply OuterMeasure.mono
  intro θ hθ
  refine ⟨hθ.1, hθ.2, ?_⟩
  simp only [originClosedDisk, polarPoint, scaleCoordinatePlane, unitDirection, mem_setOf_eq]
  calc
    (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 =
        r ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
    _ = r ^ 2 := by rw [Real.sin_sq_add_cos_sq, mul_one]
    _ ≤ r₀ ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hr.2)
        (add_nonneg hr.1 (hr.1.trans hr.2))]

/-- The radial estimate uses aggregate direction mass and pointwise critical
containment; no single target carries a mass hypothesis. -/
theorem outerMeasure_inner_ge_caseI_lintegral_of_raw
    {a r₀ : ℝ} (ha : 0 ≤ a)
    (N : (d : ProjectiveDirection) → DirectionNeedle d)
    (htrace : ∀ r ∈ Icc a r₀, ∀ d,
      FirstArcData (N d).triangle r)
    (A : ℝ → Set ProjectiveDirection) (g : ℝ → ℝ) (q : ℝ → ℝ≥0∞)
    (hg : ∀ r ∈ Icc a r₀, 1 ≤ g r)
    (hmass : ∀ r (hr : r ∈ Icc a r₀),
      ENNReal.ofReal (g r) * q r ≤ directionOuterMass (A r))
    (hcritical : ∀ r (hr : r ∈ Icc a r₀),
      FirstArcPointwiseHybridCriticalContainment
        (directionNeedleFamilyOfRaw N (htrace r hr)) (A r) (g r)) :
    (∫⁻ r in Icc a r₀, ENNReal.ofReal r * q r) ≤
      volume.toOuterMeasure
        (directionTriangleUnion N Set.univ ∩ originClosedDisk r₀) := by
  apply outerMeasure_ge_lintegral_of_angleOuter_ge _ ha q
  intro r hr
  let F := directionNeedleFamilyOfRaw N (htrace r hr)
  exact (angleOuter_ge_of_firstArcPointwiseAggregate F (A r) (hg r hr)
    (hmass r hr) (hcritical r hr)
    (triangle_subset_directionTriangleUnion_univ N)).trans
      (angleOuter_directionTriangleUnion_le_inner N ⟨ha.trans hr.1, hr.2⟩)

/-- Pointwise Li family containment at every radius gives the polar outer-area
integral.  This generic theorem remains useful independently of the raw family. -/
theorem outerMeasure_ge_caseI_lintegral
    {ι : Type*} (E : Set CoordinatePlane) {a b : ℝ} (ha : 0 ≤ a)
    (g : ℝ → ℝ) (A : ℝ → Set ProjectiveDirection)
    (x rad : ℝ → ι → ℝ) (q : ℝ → ℝ≥0∞)
    (hg : ∀ rho ∈ Icc a b, 1 ≤ g rho)
    (hrad : ∀ rho ∈ Icc a b, ∀ i, 0 ≤ rad rho i)
    (hLi : ∀ rho ∈ Icc a b,
      LiFamilyContainment (A rho) (g rho) (x rho) (rad rho))
    (hmass : ∀ rho ∈ Icc a b,
      ENNReal.ofReal (g rho) * q rho ≤ volume (A rho))
    (hbase : ∀ rho ∈ Icc a b,
      volume (⋃ i, quotientCenteredArc Real.pi (x rho i) (rad rho i)) ≤
        angleOuter E rho) :
    (∫⁻ rho in Icc a b, ENNReal.ofReal rho * q rho) ≤
      volume.toOuterMeasure E := by
  apply outerMeasure_ge_lintegral_of_angleOuter_ge E ha q
  intro rho hrho
  exact angleOuter_ge_of_liFamilyContainment
    (hg rho hrho) (hrad rho hrho) (hLi rho hrho)
    (hmass rho hrho) (hbase rho hrho)

/-! ## Aggregate mass at a variable interior mass

`FirstArcAggregateMass` was moved here from
`StarKakeyaLower.CaseIEndpointMassIntegral`; it is parameter-free and is the
hypothesis shape consumed by `outerMeasure_inner_ge_caseI_lintegral_of_raw`.
The quotient `annularCaseIQ` below is the variable-mass analogue of the frozen
Case-I quotient: its numerator is an arbitrary `L_in : ℝ≥0∞` rather than a
literal multiple of `π`.
-/

/-- Aggregate direction mass interface.  It mentions the whole direction set,
not the mass of any one `JΓ`. -/
def FirstArcAggregateMass (A : Set ProjectiveDirection) (g : ℝ)
    (q : ℝ≥0∞) : Prop :=
  ENNReal.ofReal g * q ≤ directionOuterMass A

/-- The pointwise radial minorant carrying a *variable* interior mass `L_in`.
Everything stays in `ℝ≥0∞`: no finiteness of `L_in` is assumed anywhere. -/
def annularCaseIQ (L_in : ℝ≥0∞) (g : ℝ → ℝ) (r : ℝ) : ℝ≥0∞ :=
  L_in / ENNReal.ofReal (g r)

/-- Aggregate mass at variable `L_in`.  The enlargement factor `g r` cancels
exactly against the denominator of `annularCaseIQ`; `1 ≤ g r` is what makes the
denominator nonzero and finite, so the cancellation is an equality even when
`L_in = ⊤`. -/
theorem annular_aggregateMass_of_directionOuterMass
    {r : ℝ} {A : Set ProjectiveDirection} {g : ℝ → ℝ} {L_in : ℝ≥0∞}
    (hg : 1 ≤ g r) (hmass : L_in ≤ directionOuterMass A) :
    FirstArcAggregateMass A (g r) (annularCaseIQ L_in g r) := by
  have hg0 : (0 : ℝ) < g r := lt_of_lt_of_le zero_lt_one hg
  have hne : ENNReal.ofReal (g r) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le, hg0]
  rw [FirstArcAggregateMass, annularCaseIQ,
    ENNReal.mul_div_cancel' (fun h => absurd h hne)
      (fun h => absurd h ENNReal.ofReal_ne_top)]
  exact hmass

/-- Pointwise identity behind the factorisation. -/
theorem ofReal_mul_annularCaseIQ {r : ℝ} {g : ℝ → ℝ} {L_in : ℝ≥0∞}
    (hg : 1 ≤ g r) :
    ENNReal.ofReal r * annularCaseIQ L_in g r =
      L_in * ENNReal.ofReal (r / g r) := by
  have hg0 : (0 : ℝ) < g r := lt_of_lt_of_le zero_lt_one hg
  rw [annularCaseIQ, ENNReal.ofReal_div_of_pos hg0, div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- The variable interior mass factors out of the radial integral exactly.

Both hypotheses are load bearing: `hg` makes every denominator on the interval
positive, and `hmeas` — which positivity does *not* imply — licenses pulling the
constant out of a lower Lebesgue integral.  Using `lintegral_const_mul''` rather
than `lintegral_const_mul'` keeps the statement sound at `L_in = ⊤`.

No `0 ≤ a` is required *here*, contrary to the M5 sketch in `LEAN-PLAN.md`:
`ENNReal.ofReal` truncates at negative reals, so the pointwise identity
`ofReal r * annularCaseIQ L_in g r = L_in * ofReal (r / g r)` reads `0 = 0` at
negative `r` as well.  Nonnegativity of the left endpoint is still needed by the
raw radial theorem downstream, and is a hypothesis there. -/
theorem lintegral_annularCaseIQ_eq_mul {a r₀ : ℝ} {g : ℝ → ℝ} {L_in : ℝ≥0∞}
    (hg : ∀ r ∈ Icc a r₀, 1 ≤ g r)
    (hmeas : AEMeasurable (fun r => ENNReal.ofReal (r / g r))
      (volume.restrict (Icc a r₀))) :
    (∫⁻ r in Icc a r₀, ENNReal.ofReal r * annularCaseIQ L_in g r) =
      L_in * ∫⁻ r in Icc a r₀, ENNReal.ofReal (r / g r) := by
  have hcongr : (∫⁻ r in Icc a r₀, ENNReal.ofReal r * annularCaseIQ L_in g r) =
      ∫⁻ r in Icc a r₀, L_in * ENNReal.ofReal (r / g r) := by
    refine setLIntegral_congr_fun measurableSet_Icc ?_
    intro r hr
    exact ofReal_mul_annularCaseIQ (hg r hr)
  rw [hcongr]
  exact lintegral_const_mul'' L_in hmeas

/-! ## Direction mass normalization

`directionOuterMass` (this file), `StarShapedKakeya.directionOuterMeasure`
(`Trichotomy`) and `directionAngleOuter` (`CaseIIGeometry`) are three names for
the same number on the direction circle.  The first two are definitionally the
planar-quotient outer volume; the identification with the one-dimensional
Hausdorff measure is the Haar computation
`directionOuterMeasure_eq_directionAngleOuter`, which is *reused* here and not
reproved.  The bridge matters because the exterior branch (M4) is stated in
`directionAngleOuter` while the confined branch is stated in
`directionOuterMass`, and M7 has to add the two masses.
-/

/-- The confined-side and trichotomy-side names for direction mass agree by
definition. -/
theorem directionOuterMass_eq_directionOuterMeasure (A : Set ProjectiveDirection) :
    directionOuterMass A = StarShapedKakeya.directionOuterMeasure A := rfl

/-- The confined-side direction mass is the exterior branch's angular outer
measure.  This is `directionOuterMeasure_eq_directionAngleOuter` transported
along the definitional identity above; no Haar argument is repeated. -/
theorem directionOuterMass_eq_directionAngleOuter (A : Set ProjectiveDirection) :
    directionOuterMass A = directionAngleOuter A :=
  (directionOuterMass_eq_directionOuterMeasure A).trans
    (directionOuterMeasure_eq_directionAngleOuter A)

end

end StarKakeyaLower
