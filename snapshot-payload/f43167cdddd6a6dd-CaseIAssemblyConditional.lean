import StarKakeyaLower.PolarProjectiveOuter
import StarKakeyaLower.StrongerKernel
import StarKakeyaLower.LiNeedleAdapter

/-!
# Conditional Case I assembly

The generic section estimate separates family containment, direction mass, and
the base-section comparison.  For a selected first-arc family, the first comes
from `JGammaCriticalContainment`, the last is proved in
`PolarProjectiveOuter`, and mass remains the independent `JGammaMass` input.
The endpoint below constructs data only on the required radial interval, lands
in the literal inner part of the full triangle union, and invokes one honest
conditional with the exact statement of Li Lemma 2.5.  No area conclusion is
hidden in any geometric premise.
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

/-! ## The honest Li Lemma 2.5 conditional -/

/-- `f(r) = r(2r-1)^2/2`, with Li's exact normalization. -/
def liF (r : ℝ) : ℝ := (1 / 2) * r * (2 * r - 1) ^ 2

/-- The actual statement of Li Lemma 2.5, isolated as the one unformalized
source theorem.  It uses Li's literal open ball and includes the essential
upper domain bound `r ≤ 1/2` (the unrestricted statement is false).  It speaks
about the literal triangle union `E_A`, a direction set and a lower bound for
that set's outer mass.  The conclusion is not among its premises, so unlike the
deleted bridge this conditional is satisfiable and non-circular. -/
def LiLemma25OuterStatement : Prop :=
  ∀ (A : Set ProjectiveDirection)
    (N : (d : ProjectiveDirection) → DirectionNeedle d)
    (r s₀ m : ℝ),
    (3 / 20 : ℝ) ≤ r → r ≤ 1 / 2 → 0 ≤ s₀ → 0 ≤ m →
    ENNReal.ofReal m ≤ directionOuterMass A →
    ENNReal.ofReal s₀ ≤ volume.toOuterMeasure
      (directionTriangleUnion N A ∩ originOpenDisk r) →
    ENNReal.ofReal
      (m / 4 * liF r + (1 - liF r / (2 * r ^ 2)) * s₀) ≤
      volume.toOuterMeasure (directionTriangleUnion N A)

/-- The actual set outside the radius-`r` disk used in Li 2.3. -/
def liExterior {d : ProjectiveDirection} (N : DirectionNeedle d) (r : ℝ) :
    Set CoordinatePlane := N.triangle \ originOpenDisk r

/-- The exact exterior area of the centred (isosceles) unit-base triangle.
This is the formula displayed in Li's proof, with `δ` the (nonnegative)
height.  Keeping the formula named is useful both for the calculus proof and
for checking the range in which the claimed lower bound is true. -/
def liCenteredExteriorArea (r δ : ℝ) : ℝ :=
  δ / 2 -
    (δ * Real.sqrt (r ^ 2 - δ ^ 2) +
      (Real.arcsin (δ / r) - Real.arctan (2 * δ)) * r ^ 2)

@[simp] theorem liCenteredExteriorArea_zero (r : ℝ) :
    liCenteredExteriorArea r 0 = 0 := by
  simp [liCenteredExteriorArea]

/-- The WLOG height cap actually in force immediately before Li 2.3 when the
direction set is the full projective circle.  In the paper the sharper cap is
`δ ≤ L₁*(A) f(r) / 2`; `π f(r)/2` is its uniform consequence. -/
def liLemma23ContextCap (r δ : ℝ) : Prop :=
  0 ≤ δ ∧ δ ≤ Real.pi / 2 * liF r

/-- Correct context-scoped statement of Li Lemma 2.3.  The formerly recorded
unrestricted assertion is false (already at `r=.15, δ=.12`); the paper invokes
the lemma only after the preceding WLOG cap.  The exterior payment uses the
unscaled weight `asin(δ/r)`, not the greedy deletion weight. -/
def LiLemma23ExteriorAreaStatement : Prop :=
  ∀ (d : ProjectiveDirection) (N : DirectionNeedle d) (r : ℝ),
    (3 / 20 : ℝ) ≤ r → r ≤ 1 / 2 →
    liLemma23ContextCap r |N.height| → |N.height| < r →
    ENNReal.ofReal (liF r * Real.arcsin (|N.height| / r)) ≤
      (volume.prod volume).toOuterMeasure (liExterior N r)

/-- Negative control for the deleted unrestricted statement: its known
counterexample is genuinely outside the paper's contextual cap.  This is an
exact theorem (the only transcendental input is the standard `π < 4`). -/
theorem liLemma23_counterexample_not_in_context_cap :
    ¬ liLemma23ContextCap (3 / 20 : ℝ) (12 / 100 : ℝ) := by
  intro h
  have hpi : Real.pi < 16 / 5 := by
    exact Real.pi_lt_d20.trans (by norm_num)
  have hpi2 : Real.pi / 2 < 8 / 5 := (div_lt_iff₀ (by norm_num)).2 (by linarith)
  have hf : liF (3 / 20 : ℝ) = 147 / 4000 := by norm_num [liF]
  have hbound : Real.pi / 2 * liF (3 / 20 : ℝ) < 7 / 100 := by
    rw [hf]
    have := mul_lt_mul_of_pos_right hpi2 (by norm_num : (0 : ℝ) < 147 / 4000)
    norm_num at this ⊢
    linarith
  norm_num at h
  linarith [h.2]

/-- Exact source statement of Li Lemma 2.4 in the projective metric.  The paper
asserts disjointness of the open exterior parts at the non-strict threshold;
using `interior (liExterior ...)` retains precisely that endpoint convention. -/
def LiLemma24ExteriorSeparationStatement : Prop :=
  ∀ (d₁ d₂ : ProjectiveDirection) (N₁ : DirectionNeedle d₁)
      (N₂ : DirectionNeedle d₂) (r : ℝ),
    0 < r → |N₁.height| ≤ r → |N₂.height| ≤ r →
    Real.arcsin (|N₁.height| / r) + Real.arcsin (|N₂.height| / r) ≤ dist d₁ d₂ →
    Disjoint (interior (liExterior N₁ r)) (interior (liExterior N₂ r))

/-! ### Proof of Li 2.4 -/

/-- The coordinate adapter is also a homeomorphism.  This topological spelling
is kept private: the public adapter remains the measure equivalence used by the
area layer. -/
private def coordinatePlaneHomeomorph : CoordinatePlane ≃ₜ Plane :=
  (Homeomorph.piFinTwo (fun _ : Fin 2 => ℝ)).symm.trans
    { toEquiv := (WithLp.equiv 2 ((Fin 2) → ℝ)).symm
      continuous_toFun := PiLp.continuous_toLp 2 _
      continuous_invFun := PiLp.continuous_ofLp 2 _ }

@[simp] private theorem coordinatePlaneHomeomorph_apply (z : CoordinatePlane) :
    coordinatePlaneHomeomorph z = coordinatePlaneEquiv z := rfl

/-- The boundary of a raw coordinate triangle is planar-null. -/
theorem outerMeasure_frontier_directionNeedle_triangle
    {d : ProjectiveDirection} (N : DirectionNeedle d) :
    (volume.prod volume).toOuterMeasure (frontier N.triangle) = 0 := by
  have himage : coordinatePlaneEquiv '' frontier N.triangle =
      frontier (N.toUnitNeedle.triangleHull 0) := by
    change coordinatePlaneHomeomorph '' frontier N.triangle = _
    rw [coordinatePlaneHomeomorph.image_frontier]
    simpa only [coordinatePlaneHomeomorph_apply] using
      congrArg frontier N.image_triangle_eq_triangleHull
  rw [Measure.toOuterMeasure_apply]
  have hvol := coordinatePlaneEquiv_volume_image (frontier N.triangle)
    isClosed_frontier.measurableSet
  rw [himage, N.toUnitNeedle.volume_frontier_triangleHull] at hvol
  exact hvol.symm

/-- The boundary lost when replacing the closed exterior by its interior consists
only of triangle-boundary points and points on the cutting circle. -/
theorem liExterior_diff_interior_subset_frontier_union_sphere
    {d : ProjectiveDirection} (N : DirectionNeedle d) (r : ℝ) :
    liExterior N r \ interior (liExterior N r) ⊆
      frontier N.triangle ∪ originSphere r := by
  have htri : IsClosed N.triangle := by
    have himage : coordinatePlaneHomeomorph '' N.triangle =
        N.toUnitNeedle.triangleHull 0 := by
      simpa only [coordinatePlaneHomeomorph_apply] using N.image_triangle_eq_triangleHull
    rw [← coordinatePlaneHomeomorph.preimage_image N.triangle, himage]
    exact N.toUnitNeedle.triangleHull_isCompact 0 |>.isClosed.preimage
      coordinatePlaneHomeomorph.continuous
  have hdisk : IsClosed (originOpenDisk r)ᶜ := by
    apply IsOpen.isClosed_compl
    exact isOpen_lt
      ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const
  have hext : IsClosed (liExterior N r) := by
    rw [liExterior, diff_eq]
    exact htri.inter hdisk
  intro z hz
  have hzfront : z ∈ frontier (liExterior N r) := by
    rw [← closure_diff_interior, hext.closure_eq]
    exact hz
  have hbound := frontier_inter_subset N.triangle (originOpenDisk r)ᶜ hzfront
  rcases hbound with hbound | hbound
  · exact Or.inl hbound.1
  · right
    have hsphere : frontier (originOpenDisk r) ⊆ originSphere r :=
      frontier_lt_subset_eq
        ((continuous_fst.pow 2).add (continuous_snd.pow 2))
        (continuous_const : Continuous (fun _ : CoordinatePlane => r ^ 2))
    exact hsphere (by simpa only [frontier_compl] using hbound.2)

/-- The raw exterior and its open interior have the same planar outer measure. -/
theorem outerMeasure_interior_liExterior_eq
    {d : ProjectiveDirection} (N : DirectionNeedle d) (r : ℝ) :
    (volume.prod volume).toOuterMeasure (interior (liExterior N r)) =
      (volume.prod volume).toOuterMeasure (liExterior N r) := by
  apply le_antisymm
  · exact OuterMeasure.mono _ interior_subset
  · calc
      (volume.prod volume).toOuterMeasure (liExterior N r) ≤
          (volume.prod volume).toOuterMeasure
            (interior (liExterior N r) ∪ (frontier N.triangle ∪ originSphere r)) := by
        apply OuterMeasure.mono
        intro z hz
        by_cases hi : z ∈ interior (liExterior N r)
        · exact Or.inl hi
        · exact Or.inr (liExterior_diff_interior_subset_frontier_union_sphere N r ⟨hz, hi⟩)
      _ ≤ (volume.prod volume).toOuterMeasure (interior (liExterior N r)) +
          ((volume.prod volume).toOuterMeasure (frontier N.triangle) +
            (volume.prod volume).toOuterMeasure (originSphere r)) := by
        exact (measure_union_le _ _).trans
          (add_le_add_right (measure_union_le _ _) _)
      _ = (volume.prod volume).toOuterMeasure (interior (liExterior N r)) := by
        rw [outerMeasure_frontier_directionNeedle_triangle,
          show (volume.prod volume).toOuterMeasure (originSphere r) = 0 by
            simpa only [← Measure.volume_eq_prod] using outerMeasure_originSphere r]
        simp

/-- The original full-exterior form of Li 2.3 therefore supplies the open-piece
bound required for pairwise Carathéodory summation. -/
theorem liLemma23_interior_bound (hLi23 : LiLemma23ExteriorAreaStatement)
    {d : ProjectiveDirection} (N : DirectionNeedle d) (r : ℝ)
    (hr0 : (3 / 20 : ℝ) ≤ r) (hr1 : r ≤ 1 / 2)
    (hcontext : liLemma23ContextCap r |N.height|) (hheight : |N.height| < r) :
    ENNReal.ofReal (liF r * Real.arcsin (|N.height| / r)) ≤
      (volume.prod volume).toOuterMeasure (interior (liExterior N r)) := by
  rw [outerMeasure_interior_liExterior_eq]
  exact hLi23 d N r hr0 hr1 hcontext hheight

/-- Pointwise ray shadow for an open triangle.  Unlike the Case-II version, no
outside-ball hypothesis on the base is needed: if the point itself has radius at
least `rho`, its continuation to the relatively open base has radius strictly
larger than `rho`.  This is the strictness needed at Li 2.4's non-strict angular
threshold. -/
private theorem UnitNeedle.ray_shadow_lt_of_mem_triangleInterior_of_radius_le
    {theta : Direction} {rho : ℝ} {o p : Plane} {n : UnitNeedle}
    (hrho : 0 < rho) (hp : p ∈ n.triangleInterior o)
    (hradius : rho ≤ ‖p - o‖) (hdir : n.HasDirection theta)
    (hheight : n.height o ≤ rho) :
    dist (rayDirection o p) theta < Real.arcsin (n.height o / rho) := by
  have hh : 0 < n.height o := by
    have hvolpos : 0 < volume (n.triangleInterior o) :=
      (n.triangleInterior_isOpen o).measure_pos volume ⟨p, hp⟩
    change 0 < volume (interior (n.triangleHull o)) at hvolpos
    rw [n.volume_triangleInterior o] at hvolpos
    have := ENNReal.ofReal_pos.mp hvolpos
    linarith
  obtain ⟨t, ht, c, hc, hd⟩ := n.hasDirection_oriented_lift hdir
  obtain ⟨K, hK, l, hl0, hl1, hpK⟩ :=
    n.exists_base_openSegment_on_ray_of_mem_triangleInterior hp hh
  have hKcarrier : K ∈ n.carrier := openSegment_subset_segment ℝ _ _ hK
  have hKnorm : rho < ‖K - o‖ := by
    have hnorm : ‖p - o‖ = l * ‖K - o‖ := by
      rw [hpK, norm_smul, Real.norm_eq_abs, abs_of_pos hl0]
    have hKn0 : 0 ≤ ‖K - o‖ := norm_nonneg _
    nlinarith
  have hKo : K ≠ o :=
    sub_ne_zero.mp (norm_pos_iff.mp (hrho.trans hKnorm))
  have hpangle : vectorAngle (p - o) = vectorAngle (K - o) := by
    rw [hpK, vectorAngle_pos_smul hl0]
  have hsine : Real.sin (dist (rayDirection o p) theta) =
      n.height o / ‖K - o‖ := by
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
    exact div_lt_div_of_pos_left hh hrho hKnorm
  exact angle_lt_arcsin_of_sin_lt dist_nonneg hdpi hrho hh.le hheight hslt

/-- Every point of the open exterior has a projective ray in the strict
`asin(|delta|/r)` shadow of its needle direction.  Membership in the exterior
supplies the non-strict point-radius bound; openness of the triangle supplies
the strict angular bound. -/
private theorem liExteriorInterior_image_shadow
    {d : ProjectiveDirection} (N : DirectionNeedle d) {r : ℝ}
    (hr : 0 < r) (hheight : |N.height| ≤ r) {z : CoordinatePlane}
    (hz : z ∈ interior (liExterior N r)) :
    dist (rayDirection 0 (coordinatePlaneEquiv z)) d <
      Real.arcsin (|N.height| / r) := by
  have hzext : z ∈ liExterior N r := interior_subset hz
  have hztri : z ∈ interior N.triangle := interior_mono diff_subset hz
  have hp : coordinatePlaneEquiv z ∈ N.toUnitNeedle.triangleInterior 0 := by
    change coordinatePlaneEquiv z ∈ interior (N.toUnitNeedle.triangleHull 0)
    rw [← N.image_triangle_eq_triangleHull]
    change coordinatePlaneHomeomorph z ∈
      interior (coordinatePlaneHomeomorph '' N.triangle)
    rw [← coordinatePlaneHomeomorph.image_interior]
    exact ⟨z, hztri, rfl⟩
  have hsq : r ^ 2 ≤ planeNormSq z := by
    have hout := hzext.2
    change ¬z.1 ^ 2 + z.2 ^ 2 < r ^ 2 at hout
    exact le_of_not_gt hout
  have hnormsq : ‖coordinatePlaneEquiv z‖ ^ 2 = planeNormSq z := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (by simp [Fin.sum_univ_two]; positivity)]
    simp [planeNormSq, Fin.sum_univ_two]
  have hradius : r ≤ ‖coordinatePlaneEquiv z - 0‖ := by
    simp only [sub_zero]
    nlinarith [sq_nonneg ‖coordinatePlaneEquiv z‖,
      norm_nonneg (coordinatePlaneEquiv z)]
  have hhunit : N.toUnitNeedle.height 0 ≤ r := by
    rw [N.toUnitNeedle_height_zero]
    exact hheight
  simpa only [N.toUnitNeedle_height_zero] using
    (N.toUnitNeedle.ray_shadow_lt_of_mem_triangleInterior_of_radius_le hr hp
      hradius N.toUnitNeedle_hasDirection hhunit)

/-- Li Lemma 2.4.  A hypothetical common point gives a common projective ray.
The projective triangle inequality and the two strict ray-shadow estimates then
contradict the assumed non-strict centre separation.  Thus equality at the
printed threshold is handled correctly. -/
theorem liLemma24ExteriorSeparation : LiLemma24ExteriorSeparationStatement := by
  intro d₁ d₂ N₁ N₂ r hr hh₁ hh₂ hsep
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  have h₁ := liExteriorInterior_image_shadow N₁ hr hh₁ hz₁
  have h₂ := liExteriorInterior_image_shadow N₂ hr hh₂ hz₂
  have htri := dist_triangle d₁ (rayDirection 0 (coordinatePlaneEquiv z)) d₂
  rw [dist_comm _ d₁] at h₁
  linarith

/-- Any finite or countable selected family satisfying Li's printed centre
separation has pairwise-disjoint open exterior pieces.  The index type is
arbitrary, so this single theorem covers both `Fin n` and `ℕ` outputs of the
fixed greedy selection. -/
theorem pairwise_disjoint_liExteriorInterior
    {ι : Type*} (d : ι → ProjectiveDirection)
    (N : (i : ι) → DirectionNeedle (d i)) {r : ℝ} (hr : 0 < r)
    (hheight : ∀ i, |(N i).height| ≤ r)
    (hsep : Pairwise (fun i j =>
      Real.arcsin (|(N i).height| / r) + Real.arcsin (|(N j).height| / r) ≤
        dist (d i) (d j))) :
    Pairwise (fun i j => Disjoint (interior (liExterior (N i) r))
      (interior (liExterior (N j) r))) := by
  intro i j hij
  exact liLemma24ExteriorSeparation (d i) (d j) (N i) (N j) r hr
    (hheight i) (hheight j) (hsep hij)

/-- Each selected open exterior is measurable. -/
theorem measurableSet_liExteriorInterior
    {d : ProjectiveDirection} (N : DirectionNeedle d) (r : ℝ) :
    MeasurableSet (interior (liExterior N r)) := measurableSet_interior

/-- Consequently the selected exterior union is measurable for either the
finite (`Fin n`) or infinite (`ℕ`) fixed-selection branch. -/
theorem measurableSet_iUnion_liExteriorInterior
    {ι : Type*} [Countable ι] (d : ι → ProjectiveDirection)
    (N : (i : ι) → DirectionNeedle (d i)) (r : ℝ) :
    MeasurableSet (⋃ i, interior (liExterior (N i) r)) :=
  MeasurableSet.iUnion (fun i => measurableSet_liExteriorInterior (N i) r)

/-! ### Fixed-selection exterior unions -/

/-- The literal exterior union attached to an arbitrary finite or countable
selection. -/
def liSelectedExteriorUnion {ι : Type*}
    (d : ι → ProjectiveDirection)
    (N : (i : ι) → DirectionNeedle (d i)) (r : ℝ) : Set CoordinatePlane :=
  ⋃ i, interior (liExterior (N i) r)

theorem measurableSet_liSelectedExteriorUnion
    {ι : Type*} [Countable ι] (d : ι → ProjectiveDirection)
    (N : (i : ι) → DirectionNeedle (d i)) (r : ℝ) :
    MeasurableSet (liSelectedExteriorUnion d N r) :=
  measurableSet_iUnion_liExteriorInterior d N r

/-- Carathéodory summation of Li 2.3 over a fixed selection.  The only area
input is the per-needle theorem; disjointness comes from Li 2.4. -/
theorem liSelectedExteriorUnion_area
    {ι : Type*} [Countable ι] (d : ι → ProjectiveDirection)
    (N : (i : ι) → DirectionNeedle (d i)) {r : ℝ}
    (hr0 : (3 / 20 : ℝ) ≤ r) (hr1 : r ≤ 1 / 2)
    (hcontext : ∀ i, liLemma23ContextCap r |(N i).height|)
    (hheight : ∀ i, |(N i).height| < r)
    (hsep : Pairwise (fun i j =>
      Real.arcsin (|(N i).height| / r) + Real.arcsin (|(N j).height| / r) ≤
        dist (d i) (d j)))
    (hLi23 : LiLemma23ExteriorAreaStatement) :
    (∑' i, ENNReal.ofReal
        (liF r * Real.arcsin (|(N i).height| / r))) ≤
      volume (liSelectedExteriorUnion d N r) := by
  have hr : 0 < r := lt_of_lt_of_le (by norm_num) hr0
  have hpair := pairwise_disjoint_liExteriorInterior d N hr
    (fun i => (hheight i).le) hsep
  rw [liSelectedExteriorUnion, MeasureTheory.measure_iUnion hpair
    (fun i => measurableSet_liExteriorInterior (N i) r)]
  apply ENNReal.tsum_le_tsum
  intro i
  simpa [Measure.toOuterMeasure_apply] using
    liLemma23_interior_bound hLi23 (N i) r hr0 hr1 (hcontext i) (hheight i)

/-- Exterior union in the genuine finite-stop branch. -/
def FiniteFixedSelection.liSelectedExterior
    {height H : Direction → ℝ} {q : ℝ} {A : Set Direction}
    (F : FiniteFixedSelection height H q A)
    (N : (d : ProjectiveDirection) → DirectionNeedle d) (r : ℝ) :
    Set CoordinatePlane :=
  liSelectedExteriorUnion F.selected (fun i => N (F.selected i)) r

/-- Exterior union in the infinite branch. -/
def FixedDeletionGreedyData.liSelectedExterior
    {height H : Direction → ℝ} (G : FixedDeletionGreedyData height H)
    (N : (d : ProjectiveDirection) → DirectionNeedle d) (r : ℝ) :
    Set CoordinatePlane :=
  liSelectedExteriorUnion G.selected (fun i => N (G.selected i)) r

/-- Finite-stop selected-area builder.  No aggregate area or separation estimate
is supplied by the caller: fixed deletion produces separation, Li 2.4 turns it
into disjointness, and Carathéodory sums the per-selected Li 2.3 payments. -/
theorem FiniteFixedSelection.liSelectedExterior_area
    {height H : Direction → ℝ} {q a : ℝ} {A : Set Direction}
    (F : FiniteFixedSelection height H q A)
    (N : (d : ProjectiveDirection) → DirectionNeedle d) {r : ℝ}
    (hr0 : (3 / 20 : ℝ) ≤ r) (hr1 : r ≤ 1 / 2)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hbound : ∀ d ∈ A, height d ≤ a)
    (hheight : ∀ d, height d = |(N d).height|)
    (hpos : ∀ i, 0 < height (F.selected i))
    (hscaled : ∀ i, height (F.selected i) < q * r)
    (hH : ∀ i, H (F.selected i) =
      Real.arcsin (height (F.selected i) / (q * r)))
    (hcontext : ∀ i, liLemma23ContextCap r |(N (F.selected i)).height|)
    (hLi23 : LiLemma23ExteriorAreaStatement) :
    (∑' i : Fin F.N, ENNReal.ofReal
        (liF r * Real.arcsin (|(N (F.selected i)).height| / r))) ≤
      volume (F.liSelectedExterior N r) := by
  apply liSelectedExteriorUnion_area F.selected (fun i => N (F.selected i))
    hr0 hr1 hcontext
  · intro i
    rw [← hheight]
    exact (hscaled i).trans_le
      (mul_le_of_le_one_left (by linarith : 0 ≤ r) hq1.le)
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hs := F.triangle_shadow_sum_lt_distance hq0 hq1 hbound
        (by linarith) hpos hscaled hH hij
      simpa only [hheight] using hs.le
    · have hs := F.triangle_shadow_sum_lt_distance hq0 hq1 hbound
        (by linarith) hpos hscaled hH hji
      simpa only [hheight, dist_comm, add_comm] using hs.le
  · exact hLi23

/-- Infinite selected-area builder.  The conclusion deliberately remains an
`ENNReal` sum, so infinite deletion cost is represented by `⊤` rather than being
silently collapsed by `ENNReal.toReal`. -/
theorem FixedDeletionGreedyData.liSelectedExterior_area
    {height H : Direction → ℝ} (G : FixedDeletionGreedyData height H)
    (N : (d : ProjectiveDirection) → DirectionNeedle d) {r : ℝ}
    (hr0 : (3 / 20 : ℝ) ≤ r) (hr1 : r ≤ 1 / 2)
    (hheight : ∀ d, height d = |(N d).height|)
    (hpos : ∀ i, 0 < height (G.selected i))
    (hscaled : ∀ i, height (G.selected i) < G.multiplier * r)
    (hH : ∀ i, H (G.selected i) =
      Real.arcsin (height (G.selected i) / (G.multiplier * r)))
    (hcontext : ∀ i, liLemma23ContextCap r |(N (G.selected i)).height|)
    (hLi23 : LiLemma23ExteriorAreaStatement) :
    (∑' i, ENNReal.ofReal
        (liF r * Real.arcsin (|(N (G.selected i)).height| / r))) ≤
      volume (G.liSelectedExterior N r) := by
  apply liSelectedExteriorUnion_area G.selected (fun i => N (G.selected i))
    hr0 hr1 hcontext
  · intro i
    rw [← hheight]
    exact (hscaled i).trans_le
      (mul_le_of_le_one_left (by linarith : 0 ≤ r) G.multiplier_lt_one.le)
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hs := G.future_triangle_shadow_sum_lt_distance (by linarith)
        hpos hscaled hH hij
      simpa only [hheight] using hs.le
    · have hs := G.future_triangle_shadow_sum_lt_distance (by linarith)
        hpos hscaled hH hji
      simpa only [hheight, dist_comm, add_comm] using hs.le
  · exact hLi23

/-- In the infinite branch, infinite unscaled deletion cost forces the selected
exterior union itself to have infinite area.  This is kept separate from the
real-valued certificate, avoiding the invalid conversion `ENNReal.toReal ⊤`. -/
theorem FixedDeletionGreedyData.liSelectedExterior_eq_top_of_cost_eq_top
    {height H : Direction → ℝ} (G : FixedDeletionGreedyData height H)
    (N : (d : ProjectiveDirection) → DirectionNeedle d) {r : ℝ}
    (hr0 : (3 / 20 : ℝ) ≤ r) (hr1 : r < 1 / 2)
    (hheight : ∀ d, height d = |(N d).height|)
    (hpos : ∀ i, 0 < height (G.selected i))
    (hscaled : ∀ i, height (G.selected i) < G.multiplier * r)
    (hH : ∀ i, H (G.selected i) =
      Real.arcsin (height (G.selected i) / (G.multiplier * r)))
    (hcontext : ∀ i, liLemma23ContextCap r |(N (G.selected i)).height|)
    (hcost : (∑' i, ENNReal.ofReal
      (4 * Real.arcsin (|(N (G.selected i)).height| / r))) = ⊤)
    (hLi23 : LiLemma23ExteriorAreaStatement) :
    volume (G.liSelectedExterior N r) = ⊤ := by
  have hr : 0 < r := lt_of_lt_of_le (by norm_num) hr0
  have hf : 0 < liF r := by
    unfold liF
    have h2r : 2 * r - 1 ≠ 0 := by nlinarith
    positivity
  have harea := G.liSelectedExterior_area N hr0 hr1.le hheight hpos hscaled hH
    hcontext hLi23
  have hsum : (∑' i, ENNReal.ofReal
      (liF r * Real.arcsin (|(N (G.selected i)).height| / r))) = ⊤ := by
    have heq : (fun i => ENNReal.ofReal
        (liF r * Real.arcsin (|(N (G.selected i)).height| / r))) =
        (fun i => ENNReal.ofReal (liF r / 4) * ENNReal.ofReal
          (4 * Real.arcsin (|(N (G.selected i)).height| / r))) := by
      funext i
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ liF r / 4)]
      congr 1
      ring
    rw [heq, ENNReal.tsum_mul_left, hcost, ENNReal.mul_top]
    exact (ENNReal.ofReal_pos.2 (div_pos hf (by norm_num))).ne'
  apply top_unique
  rw [← hsum]
  exact harea

/-- The union of radial rays in a residual direction set.  The origin is
included explicitly: every closed polar sector contains it, while it belongs to
no positive-radius exterior piece. -/
def liResidualRayFan (R : Set ProjectiveDirection) : Set CoordinatePlane :=
  {z | z = 0 ∨ (coordinatePlaneEquiv z ≠ 0 ∧
    rayDirection 0 (coordinatePlaneEquiv z) ∈ R)}

/-- One oriented representative of each residual projective direction, chosen
on the side on which the zero-height unit needle reaches distance at least
`1/2`.  Taking all real lifts of that oriented polar angle makes the definition
independent of a cut; `angleSetOuter` applies the standard cut afterwards. -/
def liResidualAngles
    (N : (d : ProjectiveDirection) → DirectionNeedle d)
    (R : Set ProjectiveDirection) : Set ℝ :=
  {θ | ∃ d ∈ R, (θ : PolarAngle) =
    ((if 0 ≤ (N d).centre then (N d).angle else (N d).angle + Real.pi) : PolarAngle)}

/-- The chosen oriented residual lift still projects onto the whole residual
projective set. -/
theorem image_directionQuotient_liResidualAngles
    (N : (d : ProjectiveDirection) → DirectionNeedle d)
    (R : Set ProjectiveDirection) :
    directionQuotient '' liResidualAngles N R = R := by
  apply Set.Subset.antisymm
  · rintro _ ⟨θ, ⟨d, hd, hθ⟩, rfl⟩
    have hp := congrArg polarToProjective hθ
    have heq : directionQuotient θ = d := by
      split at hp
      · simpa only [polarToProjective_coe, (N d).direction_eq] using hp
      · simpa only [map_add, polarToProjective_coe, AddCircle.coe_period, add_zero,
          (N d).direction_eq] using hp
    exact heq ▸ hd
  · intro d hd
    let θ := if 0 ≤ (N d).centre then (N d).angle else (N d).angle + Real.pi
    refine ⟨θ, ⟨d, hd, ?_⟩, ?_⟩
    · dsimp [θ]
      split <;> rfl
    dsimp [directionQuotient, θ]
    split <;> simp only [AddCircle.coe_add, AddCircle.coe_period, add_zero,
      (N d).direction_eq]

/-- The standard-cut angular mass of the concrete oriented lift is at least the
Hausdorff angular outer mass of the residual projective set. -/
theorem directionAngleOuter_le_angleSetOuter_liResidualAngles
    (N : (d : ProjectiveDirection) → DirectionNeedle d)
    (R : Set ProjectiveDirection) :
    directionAngleOuter R ≤ angleSetOuter (liResidualAngles N R) := by
  let C := liResidualAngles N R ∩ Ioo (-Real.pi) Real.pi
  have hcover : R ⊆ directionQuotient '' C ∪ {0} := by
    intro d hd
    obtain ⟨θ, hθ, hθd⟩ := Set.ext_iff.mp
      (image_directionQuotient_liResidualAngles N R) d |>.mpr hd
    let u : Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) :=
      AddCircle.equivIoc (2 * Real.pi) (-Real.pi) (θ : PolarAngle)
    have hucoe : ((u : ℝ) : PolarAngle) = (θ : PolarAngle) := AddCircle.coe_equivIoc
    have huupper : (u : ℝ) ≤ Real.pi := by linarith [u.property.2]
    by_cases hupi : (u : ℝ) = Real.pi
    · right
      rw [Set.mem_singleton_iff, ← hθd]
      change (θ : ProjectiveDirection) = 0
      have hp := congrArg polarToProjective hucoe
      simpa only [polarToProjective_coe, hupi, AddCircle.coe_period] using hp.symm
    · left
      refine ⟨u, ?_, ?_⟩
      · refine ⟨?_, ⟨u.property.1, lt_of_le_of_ne huupper hupi⟩⟩
        rcases hθ with ⟨d', hd', hθ'⟩
        exact ⟨d', hd', hucoe.trans hθ'⟩
      · calc
          directionQuotient (u : ℝ) = directionQuotient θ :=
            congrArg polarToProjective hucoe
          _ = d := hθd
  calc
    directionAngleOuter R ≤ directionAngleOuter (directionQuotient '' C ∪ {0}) :=
      measure_mono hcover
    _ ≤ directionAngleOuter (directionQuotient '' C) +
        directionAngleOuter ({0} : Set ProjectiveDirection) := measure_union_le _ _
    _ = directionAngleOuter (directionQuotient '' C) := by
      have hz : directionAngleOuter ({0} : Set ProjectiveDirection) = 0 := by
        have hzle := directionAngleOuter_image_directionQuotient_le ({0} : Set ℝ)
        have himage : directionQuotient '' ({0} : Set ℝ) =
            ({0} : Set ProjectiveDirection) := by
          simp [directionQuotient]
        rw [himage] at hzle
        exact nonpos_iff_eq_zero.mp (hzle.trans (by simp))
      rw [hz, add_zero]
    _ ≤ volume.toOuterMeasure C := directionAngleOuter_image_directionQuotient_le C
    _ = angleSetOuter (liResidualAngles N R) := rfl

/-- At radius at most `1/2`, the oriented sector selected above is literally in
the raw triangle union.  This is where the unit length of the base is used; no
extra sector-containment certificate is needed. -/
theorem polarSector_liResidualAngles_subset_directionTriangleUnion
    (N : (d : ProjectiveDirection) → DirectionNeedle d)
    (A R : Set ProjectiveDirection) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2)
    (hRA : R ⊆ A) (hzero : ∀ d ∈ R, (N d).height = 0) :
    polarSector 0 r (liResidualAngles N R) ⊆ directionTriangleUnion N A := by
  rintro z ⟨s, hs, θ, ⟨⟨d, hd, hθ⟩, _hcut⟩, rfl⟩
  apply Set.mem_iUnion_of_mem (⟨d, hRA hd⟩ : A)
  rw [DirectionNeedle.triangle]
  by_cases hc : 0 ≤ (N d).centre
  · let x := (N d).centre + 1 / 2
    have hx : 0 < x := by dsimp [x]; linarith
    refine ⟨s / x, ⟨div_nonneg hs.1 hx.le, (div_le_one hx).2 ?_⟩,
      x, ⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩, ?_⟩
    · exact hs.2.trans (hr1.trans (by dsimp [x]; linarith))
    · have hp : polarPoint s θ = polarPoint s (N d).angle :=
        polarPoint_eq_of_polar_coe_eq (by simpa [hc] using hθ)
      rw [hp, hzero d hd]
      ext <;> simp [polarPoint, supportPoint, scaleCoordinatePlane,
        addCoordinatePlane, unitDirection, unitNormal, x, div_mul_eq_mul_div] <;>
        field_simp <;> ring
  · let x := (N d).centre - 1 / 2
    have hx : x < 0 := by dsimp [x]; linarith
    refine ⟨-s / x, ⟨div_nonneg_of_nonpos (neg_nonpos.mpr hs.1) hx.le, ?_⟩,
      x, ⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩, ?_⟩
    · rw [div_le_one_of_neg hx]
      exact (by dsimp [x]; linarith [hs.2, hr1])
    · have hp : polarPoint s θ = polarPoint s ((N d).angle + Real.pi) :=
        polarPoint_eq_of_polar_coe_eq (by simpa [hc] using hθ)
      rw [hp, hzero d hd]
      ext
      · simp only [polarPoint, supportPoint, scaleCoordinatePlane,
          addCoordinatePlane, unitDirection, unitNormal, Real.cos_add_pi,
          Real.sin_add_pi, zero_mul, zero_add]
        field_simp [hx.ne]
      · simp only [polarPoint, supportPoint, scaleCoordinatePlane,
          addCoordinatePlane, unitDirection, unitNormal, Real.cos_add_pi,
          Real.sin_add_pi, zero_mul, zero_add]
        field_simp [hx.ne]

/-- A residual ray cannot meet a selected exterior: survival of the deleted
angular ball gives distance at least `2H`, whereas the strict Li-2.4 shadow is
smaller than `H`.  This is the set-level separation needed by the certificate
builder; no aggregate separation premise occurs. -/
theorem disjoint_liResidualRayFan_selectedExterior
    {ι : Type*} {d : ι → ProjectiveDirection}
    (N : (i : ι) → DirectionNeedle (d i)) {r : ℝ} (hr : 0 < r)
    (H : ι → ℝ) (R : Set ProjectiveDirection)
    (hheight : ∀ i, |(N i).height| ≤ r)
    (hshadow : ∀ i, Real.arcsin (|(N i).height| / r) < H i)
    (hHpos : ∀ i, 0 < H i)
    (hsurvive : ∀ theta ∈ R, ∀ i,
      theta ∉ fixedDeletionBall (d i) (H i)) :
    Disjoint (liResidualRayFan R) (liSelectedExteriorUnion d N r) := by
  rw [Set.disjoint_left]
  intro z hzR hzU
  simp only [liSelectedExteriorUnion, mem_iUnion] at hzU
  obtain ⟨i, hzi⟩ := hzU
  rcases hzR with rfl | hzR
  · exact (interior_subset hzi).2 (by simp [originOpenDisk, hr])
  · have hang := liExteriorInterior_image_shadow (N i) hr (hheight i) hzi
    have hnot := hsurvive _ hzR.2 i
    rw [fixedDeletionBall, Metric.mem_ball, not_lt] at hnot
    have hdist : dist (d i) (rayDirection 0 (coordinatePlaneEquiv z)) < H i := by
      rw [dist_comm]
      exact hang.trans (hshadow i)
    rw [dist_comm] at hnot
    linarith [hHpos i]

/-- Finite-stop residual/selected separation, directly from the deleted balls. -/
theorem FiniteFixedSelection.disjoint_liResidualRayFan_liSelectedExterior
    {height H : Direction → ℝ} {q a : ℝ} {A : Set Direction}
    (F : FiniteFixedSelection height H q A)
    (N : (d : ProjectiveDirection) → DirectionNeedle d) {r : ℝ} (hr : 0 < r)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hbound : ∀ d ∈ A, height d ≤ a)
    (hheight : ∀ d, height d = |(N d).height|)
    (hpos : ∀ i, 0 < height (F.selected i))
    (hscaled : ∀ i, height (F.selected i) < q * r)
    (hH : ∀ i, H (F.selected i) =
      Real.arcsin (height (F.selected i) / (q * r))) :
    Disjoint (liResidualRayFan F.residual) (F.liSelectedExterior N r) := by
  apply disjoint_liResidualRayFan_selectedExterior
    (fun i => N (F.selected i)) hr (fun i => H (F.selected i)) F.residual
  · intro i
    rw [← hheight]
    exact ((hscaled i).trans_le
      (mul_le_of_le_one_left hr.le hq1.le)).le
  · intro i
    rw [← hheight]
    rw [hH i]
    apply Real.arcsin_lt_arcsin
    · have := div_nonneg (hpos i).le hr.le
      linarith
    · apply (div_lt_div_iff_of_pos_left (hpos i) hr (mul_pos hq0 hr)).2
      nlinarith
    · rw [div_le_one (mul_pos hq0 hr)]
      exact (hscaled i).le
  · intro i
    rw [hH i]
    exact Real.arcsin_pos.2 (div_pos (hpos i) (mul_pos hq0 hr))
  · intro theta htheta i
    exact F.residual_not_mem_selected_ball htheta i

/-- Infinite residual/selected separation, again using only survival of each
literal deleted angular ball. -/
theorem FixedDeletionGreedyData.disjoint_liResidualRayFan_liSelectedExterior
    {height H : Direction → ℝ} (G : FixedDeletionGreedyData height H)
    (N : (d : ProjectiveDirection) → DirectionNeedle d) {r : ℝ} (hr : 0 < r)
    (hheight : ∀ d, height d = |(N d).height|)
    (hpos : ∀ i, 0 < height (G.selected i))
    (hscaled : ∀ i, height (G.selected i) < G.multiplier * r)
    (hH : ∀ i, H (G.selected i) =
      Real.arcsin (height (G.selected i) / (G.multiplier * r))) :
    Disjoint (liResidualRayFan (greedyResidual G.remaining))
      (G.liSelectedExterior N r) := by
  apply disjoint_liResidualRayFan_selectedExterior
    (fun i => N (G.selected i)) hr (fun i => H (G.selected i))
      (greedyResidual G.remaining)
  · intro i
    rw [← hheight]
    exact ((hscaled i).trans_le
      (mul_le_of_le_one_left hr.le G.multiplier_lt_one.le)).le
  · intro i
    rw [← hheight]
    exact G.selected_arcsin_lt_H hr hpos hscaled hH i
  · intro i
    exact (Real.arcsin_nonneg.2 (div_nonneg (hpos i).le hr.le)).trans_lt
      (G.selected_arcsin_lt_H hr hpos hscaled hH i)
  · intro theta htheta i
    have hn := G.residual_not_mem_deleted htheta i
    rw [G.deleted_eq_fixedBall i] at hn
    exact hn

/-- Li's printed constant `Cε = 2 asin (1-ε) / (π(1-ε))`. -/
def li25C (eps : ℝ) : ℝ :=
  2 * Real.arcsin (1 - eps) / (Real.pi * (1 - eps))

/-- The coefficient multiplying the actual deleted interval length
`Σ 4H_scaled`; it equals `Cε(1-ε)`.  This spelling prevents scaled weights
from being confused with raw exterior costs. -/
def li25ExteriorFactor (eps : ℝ) : ℝ :=
  2 * Real.arcsin (1 - eps) / Real.pi

theorem li25ExteriorFactor_eq_C_mul {eps : ℝ} (heps : eps ≠ 1) :
    li25ExteriorFactor eps = li25C eps * (1 - eps) := by
  unfold li25ExteriorFactor li25C
  have h : 1 - eps ≠ 0 := sub_ne_zero.mpr (Ne.symm heps)
  field_simp [h]

/-- Checked output of Li's fixed-deletion selection.  In contrast to the old
record, the two final lower bounds are not fields: the certificate records the
literal selected exterior set and residual fan, their containment/disjointness,
and the two local geometric payments.  The aggregate inequalities are derived
below by Carathéodory additivity.

`selectedExteriorArea` is the sum of Li 2.3 over the pairwise-disjoint pieces;
`residualFanArea` is the polar-sector estimate after the finite-stop or summable
infinite branch has proved residual height zero. -/
structure LiLemma25GreedyCertificate
    (A : Set ProjectiveDirection)
    (N : (d : ProjectiveDirection) → DirectionNeedle d)
    (r m : ℝ) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_lt_one : epsilon < 1
  deletionCost : ℝ
  deletionCost_nonneg : 0 ≤ deletionCost
  deletionCost_le_mass : deletionCost ≤ m
  selectedExterior : Set CoordinatePlane
  residualFan : Set CoordinatePlane
  selectedExterior_measurable : MeasurableSet selectedExterior
  selectedExterior_subset : selectedExterior ⊆ directionTriangleUnion N A
  selectedExterior_outside : selectedExterior ⊆ (originOpenDisk r)ᶜ
  residualFan_subset : residualFan ⊆ directionTriangleUnion N A
  residualFan_disjoint_selected : Disjoint residualFan selectedExterior
  selectedExteriorArea :
    ENNReal.ofReal
      (liF r * li25ExteriorFactor epsilon / 4 * deletionCost) ≤
      volume selectedExterior
  residualFanArea :
    ENNReal.ofReal (r ^ 2 / 2 * (m - deletionCost)) ≤
      volume.toOuterMeasure residualFan

/-- Constructor for the finite fixed-selection certificate.  Its geometric
inputs are pointwise/cover data: membership of selected directions, the angular
mass left in a concrete polar sector, and containment of that sector.  Selected
area and all separation are proved internally from the fixed selection and the
single per-selected Li 2.3 theorem. -/
noncomputable def FiniteFixedSelection.liLemma25GreedyCertificate
    {height H : Direction → ℝ} {q a : ℝ} {A : Set Direction}
    (F : FiniteFixedSelection height H q A)
    (N : (d : ProjectiveDirection) → DirectionNeedle d) (r m eps : ℝ)
    (heps0 : 0 < eps) (heps1 : eps < 1)
    (hr0 : (3 / 20 : ℝ) ≤ r) (hr1 : r ≤ 1 / 2)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hbound : ∀ d ∈ A, height d ≤ a)
    (hheight : ∀ d, height d = |(N d).height|)
    (hpos : ∀ i, 0 < height (F.selected i))
    (hscaled : ∀ i, height (F.selected i) < q * r)
    (hH : ∀ i, H (F.selected i) =
      Real.arcsin (height (F.selected i) / (q * r)))
    (hraw_scaled : ∀ i, li25ExteriorFactor eps * H (F.selected i) ≤
      Real.arcsin (|(N (F.selected i)).height| / r))
    (hcontext : ∀ i, liLemma23ContextCap r |(N (F.selected i)).height|)
    (hselected_mem : ∀ i, F.selected i ∈ A)
    (Θ : Set ℝ)
    (hsectorRay : polarSector 0 r Θ ⊆ liResidualRayFan F.residual)
    (hsectorE : polarSector 0 r Θ ⊆ directionTriangleUnion N A)
    (hcost_le : (∑ i : Fin F.N, 4 * H (F.selected i)) ≤ m)
    (hresidualMass : ENNReal.ofReal
      (m - (∑ i : Fin F.N, 4 * H (F.selected i))) ≤ angleSetOuter Θ)
    (hLi23 : LiLemma23ExteriorAreaStatement) :
    LiLemma25GreedyCertificate A N r m := by
  let b := ∑ i : Fin F.N, 4 * H (F.selected i)
  have hr : 0 < r := lt_of_lt_of_le (by norm_num) hr0
  have ha (i : Fin F.N) :
      0 ≤ Real.arcsin (|(N (F.selected i)).height| / r) :=
    Real.arcsin_nonneg.2 (div_nonneg (abs_nonneg _) hr.le)
  have hH0 (i : Fin F.N) : 0 ≤ H (F.selected i) := by
    rw [hH i]
    exact Real.arcsin_nonneg.2
      (div_nonneg (hpos i).le (mul_pos hq0 hr).le)
  have hb0 : 0 ≤ b := Finset.sum_nonneg fun i _ =>
    mul_nonneg (by norm_num) (hH0 i)
  have hf : 0 ≤ liF r := by unfold liF; positivity
  have hfac : 0 ≤ li25ExteriorFactor eps := by
    unfold li25ExteriorFactor
    exact div_nonneg (mul_nonneg (by norm_num)
      (Real.arcsin_nonneg.2 (by linarith))) Real.pi_pos.le
  have hselectedArea := F.liSelectedExterior_area N hr0 hr1 hq0 hq1
    hbound hheight hpos hscaled hH hcontext hLi23
  have harea : ENNReal.ofReal
      (liF r * li25ExteriorFactor eps / 4 * b) ≤
      volume (F.liSelectedExterior N r) := by
    have heq : liF r * li25ExteriorFactor eps / 4 * b = ∑ i : Fin F.N,
        liF r * (li25ExteriorFactor eps * H (F.selected i)) := by
      dsimp [b]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq, ENNReal.ofReal_sum_of_nonneg]
    · calc
        (∑ i, ENNReal.ofReal
            (liF r * (li25ExteriorFactor eps * H (F.selected i)))) ≤
            ∑' i, ENNReal.ofReal
              (liF r * Real.arcsin (|(N (F.selected i)).height| / r)) := by
          simpa only [tsum_fintype] using
            (ENNReal.tsum_le_tsum (fun i => ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_left (hraw_scaled i) hf)))
        _ ≤ volume (F.liSelectedExterior N r) := hselectedArea
    · intro i _
      exact mul_nonneg hf (mul_nonneg hfac (hH0 i))
  have hdisj := F.disjoint_liResidualRayFan_liSelectedExterior N hr hq0 hq1
    hbound hheight hpos hscaled hH
  refine
    { epsilon := eps
      epsilon_pos := heps0
      epsilon_lt_one := heps1
      deletionCost := b
      deletionCost_nonneg := hb0
      deletionCost_le_mass := by simpa [b] using hcost_le
      selectedExterior := F.liSelectedExterior N r
      residualFan := polarSector 0 r Θ
      selectedExterior_measurable := measurableSet_liSelectedExteriorUnion _ _ _
      selectedExterior_subset := ?_
      selectedExterior_outside := ?_
      residualFan_subset := hsectorE
      residualFan_disjoint_selected := hdisj.mono hsectorRay Subset.rfl
      selectedExteriorArea := harea
      residualFanArea := ?_ }
  · intro z hz
    simp only [FiniteFixedSelection.liSelectedExterior, liSelectedExteriorUnion,
      mem_iUnion] at hz
    obtain ⟨i, hzi⟩ := hz
    exact Set.mem_iUnion_of_mem
      (⟨F.selected i, hselected_mem i⟩ : A)
      (diff_subset (interior_subset hzi))
  · intro z hz
    simp only [FiniteFixedSelection.liSelectedExterior, liSelectedExteriorUnion,
      mem_iUnion] at hz
    obtain ⟨i, hzi⟩ := hz
    exact (interior_subset hzi).2
  · have hc : 0 ≤ r ^ 2 / 2 := div_nonneg (sq_nonneg r) (by norm_num)
    rw [ENNReal.ofReal_mul hc]
    exact (mul_le_mul_left' (by simpa [b] using hresidualMass) _).trans
      (polarSector_outerMeasure_ge 0 hr.le Θ)

/-- Constructor for the finite-cost infinite branch.  Finiteness of the deletion
weights is used, rather than postulated convergence of the selected heights:
it gives summability, hence selected heights tend to zero and every survivor has
zero height.  The resulting zero-height fact is the sole input to the concrete
polar-sector selector. -/
noncomputable def liLemma25Certificate_of_fixedSelection
    {height H : Direction → ℝ} (G : FixedDeletionGreedyData height H)
    (A : Set ProjectiveDirection)
    (N : (d : ProjectiveDirection) → DirectionNeedle d) (r m eps : ℝ)
    (heps0 : 0 < eps) (heps1 : eps < 1)
    (hr0 : (3 / 20 : ℝ) ≤ r) (hr1 : r ≤ 1 / 2)
    (hheight : ∀ d, height d = |(N d).height|)
    (hheight0 : ∀ d, 0 ≤ height d)
    (hpos : ∀ i, 0 < height (G.selected i))
    (hscaled : ∀ i, height (G.selected i) < G.multiplier * r)
    (hH : ∀ i, H (G.selected i) =
      Real.arcsin (height (G.selected i) / (G.multiplier * r)))
    (hraw_scaled : ∀ i, li25ExteriorFactor eps * H (G.selected i) ≤
      Real.arcsin (|(N (G.selected i)).height| / r))
    (hcontext : ∀ i, liLemma23ContextCap r |(N (G.selected i)).height|)
    (hselected_mem : ∀ i, G.selected i ∈ A)
    (hfiniteCost : (∑' i, ENNReal.ofReal (4 * H (G.selected i))) ≠ ⊤)
    (Θ : Set ℝ)
    (hsector :
      (∀ d ∈ greedyResidual G.remaining, height d = 0) →
      polarSector 0 r Θ ⊆ liResidualRayFan (greedyResidual G.remaining) ∧
      polarSector 0 r Θ ⊆ directionTriangleUnion N A)
    (hcost_le : (∑' i, 4 * H (G.selected i)) ≤ m)
    (hresidualMass : ENNReal.ofReal
      (m - (∑' i, 4 * H (G.selected i))) ≤ angleSetOuter Θ)
    (hLi23 : LiLemma23ExteriorAreaStatement) :
    LiLemma25GreedyCertificate A N r m := by
  let b := ∑' i, 4 * H (G.selected i)
  have hr : 0 < r := lt_of_lt_of_le (by norm_num) hr0
  have ha (i : ℕ) : 0 ≤ Real.arcsin (|(N (G.selected i)).height| / r) :=
    Real.arcsin_nonneg.2 (div_nonneg (abs_nonneg _) hr.le)
  have hterm0 (i : ℕ) :
      0 ≤ 4 * Real.arcsin (|(N (G.selected i)).height| / r) :=
    mul_nonneg (by norm_num) (ha i)
  have hf : 0 ≤ liF r := by unfold liF; positivity
  have hH0 (i : ℕ) : 0 ≤ H (G.selected i) := by
    rw [hH i]
    exact Real.arcsin_nonneg.2
      (div_nonneg (hheight0 _) (mul_pos G.multiplier_pos hr).le)
  have hb0 : 0 ≤ b := tsum_nonneg fun i => mul_nonneg (by norm_num) (hH0 i)
  have hfac : 0 ≤ li25ExteriorFactor eps := by
    unfold li25ExteriorFactor
    exact div_nonneg (mul_nonneg (by norm_num)
      (Real.arcsin_nonneg.2 (by linarith))) Real.pi_pos.le
  have hsummableH : Summable (fun i => H (G.selected i)) :=
    summable_of_cost_tsum_ne_top hH0 hfiniteCost
  have hraw_le_H (i : ℕ) :
      Real.arcsin (|(N (G.selected i)).height| / r) ≤ H (G.selected i) := by
    rw [← hheight, hH i]
    apply Real.arcsin_le_arcsin
    exact div_le_div_of_nonneg_left (hheight0 _)
      (mul_pos G.multiplier_pos hr) (by nlinarith [G.multiplier_lt_one])
  have hsummableCost : Summable (fun i =>
      4 * Real.arcsin (|(N (G.selected i)).height| / r)) := by
    apply Summable.of_nonneg_of_le hterm0
      (fun i => mul_le_mul_of_nonneg_left (hraw_le_H i) (by norm_num))
    exact hsummableH.mul_left 4
  have hheight_le_H : ∀ i, height (G.selected i) ≤ H (G.selected i) := by
    intro i
    have hdelta := height_eq_multiplier_rho_sin_paperWeight G.multiplier_pos hr
      (hheight0 (G.selected i)) (hscaled i).le
    rw [← hH i] at hdelta
    have hmr : G.multiplier * r ≤ 1 := by
      nlinarith [G.multiplier_lt_one, hr1]
    have hsin0 : 0 ≤ Real.sin (H (G.selected i)) := by
      rw [hH i, Real.sin_arcsin]
      · exact div_nonneg (hheight0 (G.selected i)) (mul_pos G.multiplier_pos hr).le
      · have := div_nonneg (hheight0 (G.selected i)) (mul_pos G.multiplier_pos hr).le
        linarith
      · rw [div_le_one (mul_pos G.multiplier_pos hr)]
        exact (hscaled i).le
    rw [hdelta]
    nlinarith [Real.sin_le (hH0 i)]
  have hselectedArea := G.liSelectedExterior_area N hr0 hr1 hheight hpos hscaled hH
    hcontext hLi23
  have hsummableWeighted : Summable (fun i => 4 * H (G.selected i)) :=
    hsummableH.mul_left 4
  have harea : ENNReal.ofReal
      (liF r * li25ExteriorFactor eps / 4 * b) ≤
      volume (G.liSelectedExterior N r) := by
    have heq : liF r * li25ExteriorFactor eps / 4 * b = ∑' i,
        liF r * (li25ExteriorFactor eps * H (G.selected i)) := by
      dsimp [b]
      rw [← hsummableWeighted.tsum_mul_left
        (liF r * li25ExteriorFactor eps / 4)]
      apply tsum_congr
      intro i
      ring
    rw [heq, ENNReal.ofReal_tsum_of_nonneg]
    · exact (ENNReal.tsum_le_tsum (fun i => ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (hraw_scaled i) hf))).trans hselectedArea
    · intro i
      exact mul_nonneg hf (mul_nonneg hfac (hH0 i))
    · exact (hsummableH.mul_left (liF r * li25ExteriorFactor eps)).congr
        (fun i => by ring)
  have hzero := G.residual_height_zero_of_summable_cost hheight0 hheight_le_H hsummableH
  obtain ⟨hsectorRay, hsectorE⟩ := hsector hzero
  have hdisj := G.disjoint_liResidualRayFan_liSelectedExterior N hr hheight hpos hscaled hH
  refine
    { epsilon := eps
      epsilon_pos := heps0
      epsilon_lt_one := heps1
      deletionCost := b
      deletionCost_nonneg := hb0
      deletionCost_le_mass := by simpa [b] using hcost_le
      selectedExterior := G.liSelectedExterior N r
      residualFan := polarSector 0 r Θ
      selectedExterior_measurable := measurableSet_liSelectedExteriorUnion _ _ _
      selectedExterior_subset := ?_
      selectedExterior_outside := ?_
      residualFan_subset := hsectorE
      residualFan_disjoint_selected := hdisj.mono hsectorRay Subset.rfl
      selectedExteriorArea := harea
      residualFanArea := ?_ }
  · intro z hz
    simp only [FixedDeletionGreedyData.liSelectedExterior, liSelectedExteriorUnion,
      mem_iUnion] at hz
    obtain ⟨i, hzi⟩ := hz
    exact Set.mem_iUnion_of_mem
      (⟨G.selected i, hselected_mem i⟩ : A) (diff_subset (interior_subset hzi))
  · intro z hz
    simp only [FixedDeletionGreedyData.liSelectedExterior, liSelectedExteriorUnion,
      mem_iUnion] at hz
    obtain ⟨i, hzi⟩ := hz
    exact (interior_subset hzi).2
  · have hc : 0 ≤ r ^ 2 / 2 := div_nonneg (sq_nonneg r) (by norm_num)
    rw [ENNReal.ofReal_mul hc]
    exact (mul_le_mul_left' (by simpa [b] using hresidualMass) _).trans
      (polarSector_outerMeasure_ge 0 hr.le Θ)

private theorem liF_nonneg (r : ℝ) (hr : 0 ≤ r) : 0 ≤ liF r := by
  unfold liF
  positivity

private theorem liF_le_two_mul_sq {r : ℝ}
    (hr0 : (3 / 20 : ℝ) ≤ r) (hr1 : r ≤ 1 / 2) :
    liF r ≤ 2 * r ^ 2 := by
  unfold liF
  nlinarith [sq_nonneg (2 * r - 1),
    mul_nonneg (sub_nonneg.mpr hr0) (sub_nonneg.mpr hr1)]

/-- The certificate fields imply both aggregate estimates.  This is the
Carathéodory bookkeeping portion of Li 2.5; no aggregate area estimate is an
input field. -/
theorem liLemma25_greedy_geometry
    (A : Set ProjectiveDirection)
    (N : (d : ProjectiveDirection) → DirectionNeedle d)
    (r s₀ m : ℝ) (hr : 0 ≤ r) (hs₀ : 0 ≤ s₀) (hm : 0 ≤ m)
    (hinner : ENNReal.ofReal s₀ ≤ volume.toOuterMeasure
      (directionTriangleUnion N A ∩ originOpenDisk r))
    (G : LiLemma25GreedyCertificate A N r m) :
    ∃ b : ℝ, 0 ≤ b ∧ b ≤ m ∧
      ENNReal.ofReal
          (s₀ + liF r * li25ExteriorFactor G.epsilon / 4 * b) ≤
        volume.toOuterMeasure (directionTriangleUnion N A) ∧
      ENNReal.ofReal
          (liF r * li25ExteriorFactor G.epsilon / 4 * b +
            r ^ 2 / 2 * (m - b)) ≤
        volume.toOuterMeasure (directionTriangleUnion N A) := by
  have hfac : 0 ≤ li25ExteriorFactor G.epsilon := by
    unfold li25ExteriorFactor
    exact div_nonneg (mul_nonneg (by norm_num)
      (Real.arcsin_nonneg.2 (by linarith [G.epsilon_lt_one]))) Real.pi_pos.le
  have hf : 0 ≤ liF r * li25ExteriorFactor G.epsilon / 4 * G.deletionCost :=
    mul_nonneg (div_nonneg (mul_nonneg (liF_nonneg r hr) hfac) (by norm_num))
      G.deletionCost_nonneg
  have hres : 0 ≤ r ^ 2 / 2 * (m - G.deletionCost) :=
    mul_nonneg (div_nonneg (sq_nonneg r) (by norm_num))
      (sub_nonneg.mpr G.deletionCost_le_mass)
  let I := directionTriangleUnion N A ∩ originOpenDisk r
  have hdisjI : Disjoint I G.selectedExterior := by
    rw [Set.disjoint_left]
    intro z hzI hzS
    exact (G.selectedExterior_outside hzS) hzI.2
  have haddI : volume.toOuterMeasure I + volume G.selectedExterior ≤
      volume.toOuterMeasure (directionTriangleUnion N A) := by
    rw [Measure.toOuterMeasure_apply, Measure.toOuterMeasure_apply]
    rw [← measure_union hdisjI G.selectedExterior_measurable]
    exact measure_mono (union_subset inter_subset_left G.selectedExterior_subset)
  have hout : ENNReal.ofReal
      (s₀ + liF r * li25ExteriorFactor G.epsilon / 4 * G.deletionCost) ≤
      volume.toOuterMeasure (directionTriangleUnion N A) := by
    rw [ENNReal.ofReal_add hs₀ hf]
    exact (add_le_add hinner G.selectedExteriorArea).trans haddI
  have haddR : volume.toOuterMeasure G.residualFan + volume G.selectedExterior ≤
      volume.toOuterMeasure (directionTriangleUnion N A) := by
    rw [Measure.toOuterMeasure_apply, Measure.toOuterMeasure_apply]
    rw [← measure_union G.residualFan_disjoint_selected G.selectedExterior_measurable]
    exact measure_mono (union_subset G.residualFan_subset G.selectedExterior_subset)
  have hfan : ENNReal.ofReal
        (liF r * li25ExteriorFactor G.epsilon / 4 * G.deletionCost +
          r ^ 2 / 2 * (m - G.deletionCost)) ≤
      volume.toOuterMeasure (directionTriangleUnion N A) := by
    rw [ENNReal.ofReal_add hf hres]
    exact (add_le_add G.selectedExteriorArea G.residualFanArea).trans (by
      rw [add_comm]
      exact haddR)
  exact ⟨G.deletionCost, G.deletionCost_nonneg, G.deletionCost_le_mass, hout, hfan⟩

/-- The elementary interpolation at the end of Li 2.5.  It is kept separate
from the geometric core so the latter cannot hide the final statement. -/
private theorem li25_interpolation {r s₀ m b eps : ℝ}
    (hr0 : (3 / 20 : ℝ) ≤ r) (hr1 : r ≤ 1 / 2)
    (heps0 : 0 < eps) (heps1 : eps < 1)
    (hs₀ : 0 ≤ s₀) (hm : 0 ≤ m) (hb0 : 0 ≤ b) (hbm : b ≤ m) :
    m / 4 * (liF r * li25ExteriorFactor eps) +
        (1 - liF r * li25ExteriorFactor eps / (2 * r ^ 2)) * s₀ ≤
      max (s₀ + liF r * li25ExteriorFactor eps / 4 * b)
        (liF r * li25ExteriorFactor eps / 4 * b +
          r ^ 2 / 2 * (m - b)) := by
  have hr : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 20) hr0
  have hfac0 : 0 ≤ li25ExteriorFactor eps := by
    unfold li25ExteriorFactor
    exact div_nonneg (mul_nonneg (by norm_num)
      (Real.arcsin_nonneg.2 (by linarith))) Real.pi_pos.le
  have hfac1 : li25ExteriorFactor eps ≤ 1 := by
    unfold li25ExteriorFactor
    apply (div_le_one Real.pi_pos).2
    nlinarith [Real.arcsin_le_pi_div_two (1 - eps)]
  have hf0 : 0 ≤ liF r * li25ExteriorFactor eps :=
    mul_nonneg (liF_nonneg r hr.le) hfac0
  have hf2 : liF r * li25ExteriorFactor eps ≤ 2 * r ^ 2 :=
    (mul_le_of_le_one_right (liF_nonneg r hr.le) hfac1).trans
      (liF_le_two_mul_sq hr0 hr1)
  by_cases hfan : s₀ ≤ r ^ 2 / 2 * (m - b)
  · apply le_max_of_le_right
    field_simp [ne_of_gt hr]
    nlinarith [mul_nonneg (sub_nonneg.mpr hf2) (sub_nonneg.mpr hfan)]
  · apply le_max_of_le_left
    have hfan' : r ^ 2 / 2 * (m - b) < s₀ := lt_of_not_ge hfan
    field_simp [ne_of_gt hr]
    nlinarith [mul_nonneg hf0 (sub_nonneg.mpr (le_of_lt hfan'))]

/-- For a fixed normalization parameter, a checked greedy certificate gives the
factor-weighted Li 2.5 lower bound. -/
theorem liLemma25OuterStatement_epsilon
    (A : Set ProjectiveDirection)
    (N : (d : ProjectiveDirection) → DirectionNeedle d)
    (r s₀ m : ℝ) (hr0 : (3 / 20 : ℝ) ≤ r) (hr1 : r ≤ 1 / 2)
    (hs₀ : 0 ≤ s₀) (hm : 0 ≤ m)
    (hinner : ENNReal.ofReal s₀ ≤ volume.toOuterMeasure
      (directionTriangleUnion N A ∩ originOpenDisk r))
    (G : LiLemma25GreedyCertificate A N r m) :
    ENNReal.ofReal
      (m / 4 * (liF r * li25ExteriorFactor G.epsilon) +
        (1 - liF r * li25ExteriorFactor G.epsilon / (2 * r ^ 2)) * s₀) ≤
      volume.toOuterMeasure (directionTriangleUnion N A) := by
  obtain ⟨b, hb0, hbm, hout, hfan⟩ :=
    liLemma25_greedy_geometry A N r s₀ m (by linarith) hs₀ hm hinner G
  have hinterp := li25_interpolation hr0 hr1 G.epsilon_pos G.epsilon_lt_one
    hs₀ hm hb0 hbm
  refine (ENNReal.ofReal_le_ofReal hinterp).trans ?_
  rw [ENNReal.ofReal_max]
  exact max_le hout hfan

/-- Letting the fixed-selection normalization tend to one recovers Li's
unscaled statement.  A fresh selection may be used for every epsilon; no
uniform certificate or selected sequence is assumed. -/
theorem liLemma25OuterStatement_of_greedy
    (hgreedy : ∀ (A : Set ProjectiveDirection)
      (N : (d : ProjectiveDirection) → DirectionNeedle d)
      (r s₀ m eps : ℝ),
      (3 / 20 : ℝ) ≤ r → r ≤ 1 / 2 → 0 ≤ s₀ → 0 ≤ m →
      ENNReal.ofReal m ≤ directionOuterMass A →
      ENNReal.ofReal s₀ ≤ volume.toOuterMeasure
        (directionTriangleUnion N A ∩ originOpenDisk r) →
      0 < eps → eps < 1 →
      {G : LiLemma25GreedyCertificate A N r m // G.epsilon = eps}) :
    LiLemma25OuterStatement := by
  intro A N r s₀ m hr0 hr1 hs₀ hm hmass hinner
  let eps : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have heps0 (n : ℕ) : 0 < eps n := by
    dsimp [eps]
    positivity
  have heps1 (n : ℕ) : eps n < 1 := by
    dsimp [eps]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    exact (div_lt_one (by linarith)).2 (by linarith)
  have hlower (n : ℕ) :
      ENNReal.ofReal
        (m / 4 * (liF r * li25ExteriorFactor (eps n)) +
          (1 - liF r * li25ExteriorFactor (eps n) / (2 * r ^ 2)) * s₀) ≤
        volume.toOuterMeasure (directionTriangleUnion N A) := by
    let G := hgreedy A N r s₀ m (eps n) hr0 hr1 hs₀ hm hmass hinner
      (heps0 n) (heps1 n)
    simpa [G.property] using liLemma25OuterStatement_epsilon A N r s₀ m
      hr0 hr1 hs₀ hm hinner G.1
  have heps_tendsto : Filter.Tendsto eps Filter.atTop (nhds 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (Filter.tendsto_add_atTop_nat 1)
    convert h using 1
    funext n
    dsimp [eps, Function.comp_def]
    push_cast
    ring
  have hfactor : Filter.Tendsto (fun n => li25ExteriorFactor (eps n)) Filter.atTop
      (nhds 1) := by
    have harg : Filter.Tendsto (fun n => 1 - eps n) Filter.atTop (nhds (1 - 0)) :=
      heps_tendsto.const_sub 1
    have hasin := Real.continuous_arcsin.continuousAt.tendsto.comp harg
    have hquot := (hasin.const_mul 2).div_const Real.pi
    have hpi : 2 * (Real.pi / 2) / Real.pi = (1 : ℝ) := by
      field_simp [ne_of_gt Real.pi_pos]
    simpa only [li25ExteriorFactor, Function.comp_apply, sub_zero,
      Real.arcsin_one, hpi] using hquot
  let phi : ℝ → ℝ := fun x =>
    m / 4 * (liF r * x) + (1 - liF r * x / (2 * r ^ 2)) * s₀
  have hphi : Continuous phi := by
    dsimp [phi]
    fun_prop
  have hreal : Filter.Tendsto (fun n => phi (li25ExteriorFactor (eps n))) Filter.atTop
      (nhds (phi 1)) := hphi.continuousAt.tendsto.comp hfactor
  have henn : Filter.Tendsto
      (fun n => ENNReal.ofReal (phi (li25ExteriorFactor (eps n)))) Filter.atTop
      (nhds (ENNReal.ofReal (phi 1))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hlim := le_of_tendsto henn (Filter.Eventually.of_forall (fun n => by
    simpa [phi] using hlower n))
  simpa [phi] using hlim

/-- The full projective direction circle has outer mass `π`. -/
theorem directionOuterMass_univ :
    ENNReal.ofReal Real.pi ≤
      directionOuterMass (Set.univ : Set ProjectiveDirection) := by
  simp [directionOuterMass, Measure.toOuterMeasure_apply]

/-- Exact normalization of the Li 2.5 output at the stronger parameters. -/
theorem strong_li25_output_eq :
    Real.pi / 4 * liF strongR₀ +
        (1 - liF strongR₀ / (2 * strongR₀ ^ 2)) *
          (Real.pi * strongP * strongILower) =
      Real.pi * strongCaseI strongILower := by
  rw [show liF strongR₀ = strongF₀ by rfl, strong_k_exact]
  simp only [strongCaseI]
  ring

/-- Non-vacuous conditional Case-I area theorem.  The radial hypotheses first
produce the specific inner-area lower bound `s₀ = π p I`; the single honest
Li-2.5 conditional then supplies the baseline and outer part.  No finiteness or
`ENNReal.toReal` assumption is needed, so the `∞` case is handled correctly. -/
theorem strongCaseI_conditional_area_lower_bound
    {a : ℝ} (ha : 0 ≤ a)
    (N : (d : ProjectiveDirection) → DirectionNeedle d)
    (htrace : ∀ r ∈ Icc a strongR₀, ∀ d,
      FirstArcData (N d).triangle r)
    (A : ℝ → Set ProjectiveDirection) (g : ℝ → ℝ) (q : ℝ → ℝ≥0∞)
    (hg : ∀ r ∈ Icc a strongR₀, 1 ≤ g r)
    (hmass : ∀ r (hr : r ∈ Icc a strongR₀),
      ENNReal.ofReal (g r) * q r ≤ directionOuterMass (A r))
    (hcritical : ∀ r (hr : r ∈ Icc a strongR₀),
      FirstArcPointwiseHybridCriticalContainment
        (directionNeedleFamilyOfRaw N (htrace r hr)) (A r) (g r))
    (hI : ENNReal.ofReal (Real.pi * strongP * strongILower) ≤
      ∫⁻ r in Icc a strongR₀, ENNReal.ofReal r * q r)
    (hLi25 : LiLemma25OuterStatement) :
    ENNReal.ofReal (Real.pi * strongTarget) <
      volume.toOuterMeasure (directionTriangleUnion N Set.univ) := by
  let Eall := directionTriangleUnion N Set.univ
  let s₀ := Real.pi * strongP * strongILower
  have hs₀ : 0 ≤ s₀ := by
    dsimp [s₀]
    exact mul_nonneg (mul_nonneg Real.pi_pos.le (by norm_num [strongP]))
      (by norm_num [strongILower])
  have hinner : ENNReal.ofReal s₀ ≤
      volume.toOuterMeasure (Eall ∩ originClosedDisk strongR₀) :=
    hI.trans (outerMeasure_inner_ge_caseI_lintegral_of_raw ha N htrace A g q
      hg hmass hcritical)
  have hinnerOpen : ENNReal.ofReal s₀ ≤
      volume.toOuterMeasure (Eall ∩ originOpenDisk strongR₀) := by
    rw [outerMeasure_inter_originOpenDisk_eq_closedDisk]
    exact hinner
  have hLi := hLi25 (Set.univ : Set ProjectiveDirection) N strongR₀ s₀ Real.pi
    strongParameterDomain.r₀_ge_three_twentieths strongParameterDomain.r₀_lt_half.le
    hs₀ Real.pi_pos.le directionOuterMass_univ hinnerOpen
  rw [strong_li25_output_eq] at hLi
  have hstrict : ENNReal.ofReal (Real.pi * strongTarget) <
      ENNReal.ofReal (Real.pi * strongCaseI strongILower) := by
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ?_).2
    · exact mul_lt_mul_of_pos_left strong_caseI_strict Real.pi_pos
    · exact mul_nonneg Real.pi_pos.le (by norm_num [strongTarget])
  exact hstrict.trans_le hLi

end

end StarKakeyaLower
