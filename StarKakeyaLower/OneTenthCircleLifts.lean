import StarKakeyaLower.OneTenthCircle

/-!
# Both physical lifts, measured in the ordinary circle

A Borel choice of one physical lift preserves projective direction length.
The opposite lift of the eligible subcut is disjoint from that first lift.
The proofs use actual quotient images of a right-closed fundamental chart,
not an assumed normalization or a multiplicity count of target arcs.
-/

open Set MeasureTheory

namespace StarKakeyaLower.OneTenth
noncomputable section

/-- Quotient injectivity within one right-closed real fundamental chart. -/
theorem coe_injective_on_Ioc (p a : ℝ) [Fact (0 < p)] :
    Set.InjOn (fun t : ℝ => (t : AddCircle p)) (Ioc a (a+p)) := by
  intro x hx y hy hxy
  have h : (⟨x,hx⟩ : Ioc a (a+p)) = ⟨y,hy⟩ := by
    apply (AddCircle.equivIoc p a).symm.injective
    exact hxy
  exact congrArg Subtype.val h

/-- A Borel subset of one real fundamental chart has Borel quotient image and
exactly the same Lebesgue/Haar length. -/
theorem chart_image_measure (p a : ℝ) [Fact (0 < p)] (E : Set ℝ)
    (hE : MeasurableSet E) (hchart : E ⊆ Ioc a (a+p)) :
    MeasurableSet ((fun t : ℝ => (t : AddCircle p)) '' E) ∧
      volume ((fun t : ℝ => (t : AddCircle p)) '' E) = volume E := by
  let e := AddCircle.measurableEquivIoc p a
  let C : Set (Ioc a (a+p)) := {t | (t : ℝ) ∈ E}
  have hC : MeasurableSet C := hE.preimage measurable_subtype_coe
  have heq : e.symm '' C = (fun t : ℝ => (t : AddCircle p)) '' E := by
    ext q
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, hchart ht⟩, ht, rfl⟩
  have hD : MeasurableSet ((fun t : ℝ => (t : AddCircle p)) '' E) :=
    heq ▸ e.symm.measurableEmbedding.measurableSet_image' hC
  refine ⟨hD, ?_⟩
  rw [← (AddCircle.measurePreserving_mk p a).measure_preimage hD.nullMeasurableSet,
    Measure.restrict_apply (hD.preimage AddCircle.measurable_mk')]
  congr 1
  ext t
  constructor
  · rintro ⟨⟨s, hs, hst⟩, ht⟩
    have he : s = t := coe_injective_on_Ioc p a (hchart hs) ht hst
    exact he ▸ hs
  · intro ht
    exact ⟨⟨t,ht,rfl⟩, hchart ht⟩

/-- First-half physical image of a real direction chart. -/
def firstLift (E : Set ℝ) : Set PolarAngle := (fun t : ℝ => (t : PolarAngle)) '' E

/-- Second, antipodal physical image, not identified with the first. -/
def secondLift (E : Set ℝ) : Set PolarAngle :=
  (fun t : ℝ => ((Real.pi+t : ℝ) : PolarAngle)) '' E

/-- The chosen far lift uses the first chart on `A`, the second on its complement. -/
def chosenLift (V A : Set ℝ) : Set PolarAngle := firstLift (V ∩ A) ∪ secondLift (V \ A)

/-- The selected near endpoint occupies the opposite physical lift. -/
def oppositeLift (B A : Set ℝ) : Set PolarAngle := firstLift (B \ A) ∪ secondLift (B ∩ A)

theorem firstLift_measurable_volume {E : Set ℝ} (hE : MeasurableSet E)
    (hchart : E ⊆ Ioc 0 Real.pi) :
    MeasurableSet (firstLift E) ∧ volume (firstLift E) = volume E := by
  apply chart_image_measure (2*Real.pi) 0 E hE
  intro t ht
  have hh := hchart ht
  exact ⟨hh.1, by linarith [hh.2, Real.pi_pos]⟩

theorem secondLift_eq_translate (E : Set ℝ) :
    secondLift E = (fun q : PolarAngle => (Real.pi : PolarAngle) + q) '' firstLift E := by
  rw [firstLift, image_image]
  simp only [secondLift, AddCircle.coe_add]

theorem secondLift_measurable_volume {E : Set ℝ} (hE : MeasurableSet E)
    (hchart : E ⊆ Ioc 0 Real.pi) :
    MeasurableSet (secondLift E) ∧ volume (secondLift E) = volume E := by
  have h := firstLift_measurable_volume hE hchart
  rw [secondLift_eq_translate]
  constructor
  · exact (Homeomorph.addLeft (Real.pi : PolarAngle)).measurableEmbedding.measurableSet_image' h.1
  · exact (measure_vadd volume (Real.pi : PolarAngle) (firstLift E)).trans h.2

/-- The half-circle charts are disjoint even at their endpoints. -/
theorem first_second_disjoint {E F : Set ℝ}
    (hE : E ⊆ Ioc 0 Real.pi) (hF : F ⊆ Ioc 0 Real.pi) :
    Disjoint (firstLift E) (secondLift F) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,heq⟩
  have hx' := hE hx
  have hy' := hF hy
  have he : Real.pi+y = x := coe_injective_on_Ioc (2*Real.pi) 0
    ⟨by linarith [hy'.1, Real.pi_pos], by linarith [hy'.2]⟩
    ⟨hx'.1, by linarith [hx'.2, Real.pi_pos]⟩ heq
  linarith [hx'.2, hy'.1]

theorem firstLift_disjoint {E F : Set ℝ} (hE : E ⊆ Ioc 0 Real.pi)
    (hF : F ⊆ Ioc 0 Real.pi) (h : Disjoint E F) :
    Disjoint (firstLift E) (firstLift F) := by
  rw [Set.disjoint_left] at h ⊢
  rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,heq⟩
  have hx' := hE hx
  have hy' := hF hy
  have he : y = x := coe_injective_on_Ioc (2*Real.pi) 0
    ⟨hy'.1, by linarith [hy'.2, Real.pi_pos]⟩
    ⟨hx'.1, by linarith [hx'.2, Real.pi_pos]⟩ heq
  exact h hx (he ▸ hy)

theorem secondLift_disjoint {E F : Set ℝ} (hE : E ⊆ Ioc 0 Real.pi)
    (hF : F ⊆ Ioc 0 Real.pi) (h : Disjoint E F) :
    Disjoint (secondLift E) (secondLift F) := by
  rw [secondLift_eq_translate, secondLift_eq_translate]
  have hd := Set.disjoint_left.mp (firstLift_disjoint hE hF h)
  rw [Set.disjoint_left]
  rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,heq⟩
  exact hd hx ((add_left_cancel heq) ▸ hy)

/-- Borel lift selection preserves length, without any continuity assumption. -/
theorem chosenLift_measurable_volume {V A : Set ℝ}
    (hV : MeasurableSet V) (hA : MeasurableSet A) (hchart : V ⊆ Ioc 0 Real.pi) :
    MeasurableSet (chosenLift V A) ∧ volume (chosenLift V A) = volume V := by
  have hfirst := firstLift_measurable_volume (hV.inter hA) (inter_subset_left.trans hchart)
  have hsecond := secondLift_measurable_volume (hV.diff hA) (diff_subset.trans hchart)
  refine ⟨hfirst.1.union hsecond.1, ?_⟩
  rw [chosenLift, measure_union (first_second_disjoint
    (inter_subset_left.trans hchart) (diff_subset.trans hchart)) hsecond.1,
    hfirst.2, hsecond.2]
  exact measure_inter_add_diff V hA

theorem oppositeLift_eq_chosen (B A : Set ℝ) :
    oppositeLift B A = chosenLift B Aᶜ := by
  simp [oppositeLift, chosenLift, diff_eq]

/-- Two anchors for a direction are genuinely distinct physical points. No
projective quotient is used when taking this union. -/
theorem chosen_opposite_disjoint {V B A : Set ℝ}
    (hV : V ⊆ Ioc 0 Real.pi) (hB : B ⊆ Ioc 0 Real.pi) :
    Disjoint (chosenLift V A) (oppositeLift B A) := by
  unfold chosenLift oppositeLift
  rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
  refine ⟨⟨?_, first_second_disjoint (inter_subset_left.trans hV) (inter_subset_left.trans hB)⟩,
    ⟨(first_second_disjoint (diff_subset.trans hB) (diff_subset.trans hV)).symm, ?_⟩⟩
  · apply firstLift_disjoint (inter_subset_left.trans hV) (diff_subset.trans hB)
    exact Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx.2)
  · apply secondLift_disjoint (diff_subset.trans hV) (inter_subset_left.trans hB)
    exact Set.disjoint_left.mpr (fun _ hx hy => hx.2 hy.2)

/-- The eligible-anchor census: the ordinary physical union has length
`|V|+|B|`, where each summand is actual Haar measure on the projective circle. -/
theorem eligible_lift_length {V B A : Set ℝ}
    (hV : MeasurableSet V) (hB : MeasurableSet B) (hA : MeasurableSet A)
    (hchart : V ⊆ Ioc 0 Real.pi) (hBV : B ⊆ V) :
    volume.toOuterMeasure (chosenLift V A ∪ oppositeLift B A) =
      volume ((fun t : ℝ => (t : ProjectiveDirection)) '' V) +
      volume ((fun t : ℝ => (t : ProjectiveDirection)) '' B) := by
  have hBchart := hBV.trans hchart
  have hv := chosenLift_measurable_volume hV hA hchart
  have hb := chosenLift_measurable_volume hB hA.compl hBchart
  rw [← oppositeLift_eq_chosen] at hb
  simp only [Measure.toOuterMeasure_apply]
  rw [measure_union (chosen_opposite_disjoint hchart hBchart) hb.1, hv.2, hb.2,
    (chart_image_measure Real.pi 0 V hV (by simpa using hchart)).2,
    (chart_image_measure Real.pi 0 B hB (by simpa using hBchart)).2]

#print axioms eligible_lift_length

end
end StarKakeyaLower.OneTenth
