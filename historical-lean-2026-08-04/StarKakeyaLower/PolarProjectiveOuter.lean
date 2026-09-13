import StarKakeyaLower.PolarOuterMeasure

/-!
# Outer measure under the polar-to-projective quotient

The quotient `T(2π) → Tπ` is two-to-one.  We therefore do not use a false
blanket comparison between an arbitrary projected set and one chosen section.
Instead we cut the polar carrier in the standard real turn, split that turn
into two projective fundamental intervals, apply measure preservation on each,
and discard only the null cut point.
-/

open Set MeasureTheory Real
open scoped ENNReal

namespace StarKakeyaLower

noncomputable section

/-- A quotient image from one right-closed fundamental interval has no more
outer measure than its (possibly nonmeasurable) real source. -/
theorem volume_quotient_image_le_outerMeasure_of_subset_Ioc
    {p t : ℝ} [Fact (0 < p)] (A : Set ℝ) (hA : A ⊆ Ioc t (t + p)) :
    volume ((fun x : ℝ => (x : AddCircle p)) '' A) ≤ volume.toOuterMeasure A := by
  let C : Set ℝ := toMeasurable volume A
  let Cs : Set (Ioc t (t + p)) := {x | (x : ℝ) ∈ C}
  let e := AddCircle.measurableEquivIoc p t
  let D : Set (AddCircle p) := e.symm '' Cs
  have hCs : MeasurableSet Cs := by
    exact (measurableSet_toMeasurable volume A).preimage measurable_subtype_coe
  have hD : MeasurableSet D := by
    exact e.symm.measurableEmbedding.measurableSet_image' hCs
  have himage : (fun x : ℝ => (x : AddCircle p)) '' A ⊆ D := by
    rintro _ ⟨x, hx, rfl⟩
    let xs : Ioc t (t + p) := ⟨x, hA hx⟩
    refine ⟨xs, subset_toMeasurable volume A hx, ?_⟩
    change (e.symm xs) = (x : AddCircle p)
    rfl
  calc
    volume ((fun x : ℝ => (x : AddCircle p)) '' A) ≤ volume D := measure_mono himage
    _ = (volume.restrict (Ioc t (t + p)))
        ((fun x : ℝ => (x : AddCircle p)) ⁻¹' D) :=
      ((AddCircle.measurePreserving_mk p t).measure_preimage hD.nullMeasurableSet).symm
    _ ≤ volume C := by
      rw [Measure.restrict_apply (hD.preimage AddCircle.measurable_mk')]
      apply measure_mono
      intro x hx
      rcases hx with ⟨⟨y, hyC, hyx⟩, hxI⟩
      have he : y = (⟨x, hxI⟩ : Ioc t (t + p)) := by
        apply e.symm.injective
        exact hyx
      simpa [he] using hyC
    _ = volume A := measure_toMeasurable A
    _ = volume.toOuterMeasure A := (Measure.toOuterMeasure_apply volume A).symm

/-- The standard one-turn real cut of a polar-circle carrier. -/
def polarCarrierCut (S : Set PolarAngle) : Set ℝ :=
  {θ | θ ∈ Ioo (-Real.pi) Real.pi ∧ (θ : PolarAngle) ∈ S}

/-- Correct outer-measure direction for `polarToProjective`.  The proof splits
the standard polar turn into two `π`-fundamental intervals; this is where the
map's two-to-one nature is accounted for, rather than silently dropping a
factor. -/
theorem volume_projectedPolar_le_cutOuter (S : Set PolarAngle) :
    volume (polarToProjective '' S) ≤ volume.toOuterMeasure (polarCarrierCut S) := by
  let A := polarCarrierCut S
  let B := A ∩ Ioc (-Real.pi) 0
  let C := A \ Ioc (-Real.pi) 0
  have hA : A ⊆ Ioo (-Real.pi) Real.pi := fun _ h => h.1
  have hB : B ⊆ Ioc (-Real.pi) (-Real.pi + Real.pi) := by
    simpa only [neg_add_cancel] using (inter_subset_right : B ⊆ Ioc (-Real.pi) 0)
  have hC : C ⊆ Ioc 0 (0 + Real.pi) := by
    intro x hx
    have hxA := hA hx.1
    constructor
    · exact lt_of_not_ge (fun hx0 => hx.2 ⟨hxA.1, hx0⟩)
    · simpa using hxA.2.le
  have hmk : volume ((fun x : ℝ => (x : ProjectiveDirection)) '' A) ≤
      volume.toOuterMeasure A := by
    have hsplit : A = B ∪ C := (inter_union_diff A (Ioc (-Real.pi) 0)).symm
    calc
      volume ((fun x : ℝ => (x : ProjectiveDirection)) '' A) =
          volume (((fun x : ℝ => (x : ProjectiveDirection)) '' B) ∪
            ((fun x : ℝ => (x : ProjectiveDirection)) '' C)) := by
        rw [hsplit, image_union]
      _ ≤ volume ((fun x : ℝ => (x : ProjectiveDirection)) '' B) +
          volume ((fun x : ℝ => (x : ProjectiveDirection)) '' C) := measure_union_le _ _
      _ ≤ volume.toOuterMeasure B + volume.toOuterMeasure C :=
        add_le_add (volume_quotient_image_le_outerMeasure_of_subset_Ioc B hB)
          (volume_quotient_image_le_outerMeasure_of_subset_Ioc C hC)
      _ = volume.toOuterMeasure A := by
        simp only [Measure.toOuterMeasure_apply]
        exact measure_inter_add_diff A measurableSet_Ioc
  have hproject : polarToProjective '' S ⊆
      (fun x : ℝ => (x : ProjectiveDirection)) '' A ∪
        {(Real.pi : ProjectiveDirection)} := by
    rintro _ ⟨z, hzS, rfl⟩
    let x : Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) :=
      AddCircle.equivIoc (2 * Real.pi) (-Real.pi) z
    have hxI : (x : ℝ) ∈ Ioc (-Real.pi) Real.pi := by
      constructor <;> linarith [x.property.1, x.property.2]
    have hcoe : ((x : ℝ) : PolarAngle) = z := AddCircle.coe_equivIoc
    by_cases hxpi : (x : ℝ) = Real.pi
    · right
      rw [Set.mem_singleton_iff]
      calc
        polarToProjective z = polarToProjective (((x : ℝ) : PolarAngle)) :=
          congrArg polarToProjective hcoe.symm
        _ = ((x : ℝ) : ProjectiveDirection) := rfl
        _ = (Real.pi : ProjectiveDirection) := congrArg (fun y : ℝ =>
          (y : ProjectiveDirection)) hxpi
    · left
      refine ⟨(x : ℝ), ?_, ?_⟩
      · exact ⟨⟨hxI.1, lt_of_le_of_ne hxI.2 hxpi⟩, hcoe.symm ▸ hzS⟩
      · change ((x : ℝ) : ProjectiveDirection) = polarToProjective z
        exact congrArg polarToProjective hcoe
  calc
    volume (polarToProjective '' S) ≤
        volume (((fun x : ℝ => (x : ProjectiveDirection)) '' A) ∪
          {(Real.pi : ProjectiveDirection)}) := measure_mono hproject
    _ ≤ volume ((fun x : ℝ => (x : ProjectiveDirection)) '' A) +
        volume ({(Real.pi : ProjectiveDirection)} : Set ProjectiveDirection) := measure_union_le _ _
    _ = volume ((fun x : ℝ => (x : ProjectiveDirection)) '' A) := by
      have hs : volume ({(Real.pi : ProjectiveDirection)} : Set ProjectiveDirection) = 0 := by
        rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
        simp
      rw [hs, add_zero]
    _ ≤ volume.toOuterMeasure A := hmk

/-! ## Selected first arcs and planar sections -/

/-- The selected projective base union, indexed only by directions in `JΓ`. -/
def DirectionNeedleFamily.selectedBaseUnion {r : ℝ} (F : DirectionNeedleFamily r)
    (Γ : Set PolarAngle) : Set ProjectiveDirection :=
  ⋃ d : F.JGamma Γ,
    quotientCenteredArc Real.pi (F.firstCenter d) (F.firstRadius d)

/-- Its closed same-centre quotient dilation.  Closed arcs are essential at the
zero-span endpoint: dilation of a singleton is the same singleton, rather than
the empty open interval. -/
def DirectionNeedleFamily.selectedDilatedUnion {r : ℝ} (F : DirectionNeedleFamily r)
    (Γ : Set PolarAngle) (g : ℝ) : Set ProjectiveDirection :=
  ⋃ d : F.JGamma Γ,
    quotientClosedCenteredDilate g Real.pi (F.firstCenter d) (F.firstRadius d)

/-- The open dilation used by the Haar-measure growth lemma.  It is deliberately
separate from endpoint containment, since an open radius-zero arc is empty. -/
def DirectionNeedleFamily.selectedOpenDilatedUnion {r : ℝ} (F : DirectionNeedleFamily r)
    (Γ : Set PolarAngle) (g : ℝ) : Set ProjectiveDirection :=
  ⋃ d : F.JGamma Γ,
    quotientCenteredDilate g Real.pi (F.firstCenter d) (F.firstRadius d)

/-- The actual selected polar carriers before quotienting. -/
def DirectionNeedleFamily.selectedPolarUnion {r : ℝ} (F : DirectionNeedleFamily r)
    (Γ : Set PolarAngle) : Set PolarAngle :=
  ⋃ d : F.JGamma Γ, (F.firstArc d).carrier

theorem DirectionNeedleFamily.selectedBaseUnion_subset_projectedPolarUnion
    {r : ℝ} (F : DirectionNeedleFamily r) (Γ : Set PolarAngle) :
    F.selectedBaseUnion Γ ⊆ polarToProjective '' F.selectedPolarUnion Γ := by
  intro z hz
  rw [DirectionNeedleFamily.selectedBaseUnion, mem_iUnion] at hz
  obtain ⟨d, hd⟩ := hz
  obtain ⟨θ, hθ, rfl⟩ := F.quotient_firstArc_subset_projected_carrier d hd
  exact ⟨θ, Set.mem_iUnion_of_mem d hθ, rfl⟩

theorem DirectionNeedleFamily.selectedPolarUnion_subset_triangleTraces
    {r : ℝ} (F : DirectionNeedleFamily r) (Γ : Set PolarAngle) :
    F.selectedPolarUnion Γ ⊆
      ⋃ d : F.JGamma Γ, polarCircleTrace (F.needle d).triangle r := by
  intro θ hθ
  rw [DirectionNeedleFamily.selectedPolarUnion, mem_iUnion] at hθ
  rw [mem_iUnion]
  obtain ⟨d, hd⟩ := hθ
  exact ⟨d, F.firstArc_carrier_subset_polarCircleTrace d hd⟩

/-- Standard-cut representatives of selected carriers lie in the literal polar
section of any set containing every triangle in the family. -/
theorem DirectionNeedleFamily.polarCarrierCut_selected_subset_angleSection
    {r : ℝ} (F : DirectionNeedleFamily r) (Γ : Set PolarAngle)
    (E : Set CoordinatePlane)
    (htri : ∀ d : ProjectiveDirection, (F.needle d).triangle ⊆ E) :
    polarCarrierCut (F.selectedPolarUnion Γ) ⊆ polarAngleSection E r := by
  intro θ hθ
  rcases hθ with ⟨hcut, hsel⟩
  have htrace := F.selectedPolarUnion_subset_triangleTraces Γ hsel
  rw [mem_iUnion] at htrace
  obtain ⟨d, φ, hφtrace, hφθ⟩ := htrace
  refine ⟨hcut, htri d ?_⟩
  have hpoint : polarPoint r θ = polarPoint r φ :=
    polarPoint_eq_of_polar_coe_eq hφθ.symm
  rw [hpoint]
  exact hφtrace

/-- The selected projective base union is controlled by the actual planar polar
section, with no additional selected-base hypothesis. -/
theorem DirectionNeedleFamily.selectedBaseUnion_volume_le_angleOuter
    {r : ℝ} (F : DirectionNeedleFamily r) (Γ : Set PolarAngle)
    (E : Set CoordinatePlane)
    (htri : ∀ d : ProjectiveDirection, (F.needle d).triangle ⊆ E) :
    volume (F.selectedBaseUnion Γ) ≤ angleOuter E r := by
  calc
    volume (F.selectedBaseUnion Γ) ≤
        volume (polarToProjective '' F.selectedPolarUnion Γ) :=
      measure_mono (F.selectedBaseUnion_subset_projectedPolarUnion Γ)
    _ ≤ volume.toOuterMeasure (polarCarrierCut (F.selectedPolarUnion Γ)) :=
      volume_projectedPolar_le_cutOuter _
    _ ≤ volume.toOuterMeasure (polarAngleSection E r) :=
      measure_mono (F.polarCarrierCut_selected_subset_angleSection Γ E htri)
    _ = angleOuter E r := rfl

end

end StarKakeyaLower
